/*
 * Copyright (C) 2007-2021 Intel Corporation.
 * SPDX-License-Identifier: MIT
 */

/*! @file
 *  This is an example of the PIN tool that demonstrates some basic PIN APIs 
 *  and could serve as the starting point for developing your first PIN tool
 */

#include "pin.H"
#include <cstdio>
#include <iostream>
#include <fstream>
#include <unordered_map>
#include <vector>
using std::cerr;
using std::endl;
using std::string;

/* ================================================================== */
// Global variables
/* ================================================================== */

int insCount    = 0; //number of dynamically executed instructions
int loads       = 0;
int lduh        = 0;
int stalls_q1   = 0;
int stalls_q2   = 0;
int reg_ready[REG_LAST];

// Q1: single-threaded, in-order F/D/EX/M/WB timing model.
// A ready cycle is the producer's WB cycle. Decode can read in that
// same cycle because WB writes RF before Decode reads it.
UINT64 q1_ready[REG_LAST] = {};
UINT64 q1_previous_decode = 1; //track the decode cycle of the previous instruction for Q1 (isCount)

// Q2 uses an independent clock: F/D/EX1/EX2/M/WB, full forwarding.
// ready[r] is the first cycle a forwarded value can be consumed.
UINT64 q2_ready[REG_LAST] = {};
UINT64 q2_previous_ex1 = 2;

/* ===================================================================== */
// Command line switches
/* ===================================================================== */

/* ===================================================================== */
// Utilities
/* ===================================================================== */
//Returns -1 if the instruction is not a simple store
//Otherwise, returns the index of the operand that provides the store value
int storeOps(INS insn)
{
  if (!INS_IsMemoryWrite(insn)) return -1;
  if (INS_IsMov(insn)) return 1;
  if (!INS_IsXchg(insn)) return -1;
  if (INS_OperandIsMemory(insn, 0)) return 1;
  return 0;
}
/* ===================================================================== */
// Analysis routines
/* ===================================================================== */
// Return a register needed ONLY as simple-store data (at M), not an
// address input (at EX1). Compare register identities, not vector indices.
REG StoreDataOnlyReg(INS insn)
{
    const int op = storeOps(insn);
    if (op < 0 || !INS_OperandIsReg(insn, op)) return REG_INVALID();
    const REG value = REG_FullRegName(INS_OperandReg(insn, op));
    for (UINT32 i = 0; i < INS_OperandCount(insn); ++i) {
        if (!INS_OperandIsMemory(insn, i)) continue;
        const REG base = INS_OperandMemoryBaseReg(insn, i);
        const REG index = INS_OperandMemoryIndexReg(insn, i);
        if ((base != REG_INVALID() && REG_FullRegName(base) == value) ||
            (index != REG_INVALID() && REG_FullRegName(index) == value)) {
            return REG_INVALID();
        }
    }
    return value;
}

VOID CountQ2(const std::vector<REG>* srcs,
             const std::vector<REG>* dsts,
             BOOL isLoad,
             UINT32 storeDataReg)
{
    const UINT64 nominal_ex1 = q2_previous_ex1 + 1;
    UINT64 actual_ex1 = nominal_ex1;

    for (REG src : *srcs) {
        // Execute inputs are needed at EX1. Simple-store data can be
        // forwarded to M, which is two cycles after EX1 in this pipeline.
        const UINT64 offset = static_cast<UINT32>(src) == storeDataReg ? 2 : 0;
        const UINT64 required_ex1 = q2_ready[src] > offset
            ? q2_ready[src] - offset : 0;
        if (required_ex1 > actual_ex1) actual_ex1 = required_ex1;
    }
    stalls_q2 += static_cast<int>(actual_ex1 - nominal_ex1);

    // EX2 finishes at the end of EX1+1: usable at EX1+2.
    // M finishes at the end of EX1+2: load usable at EX1+3.
    // Use the starter's RISC-like approximation: memory readers are loads.
    for (REG dst : *dsts) {
        q2_ready[dst] = actual_ex1 + (isLoad ? 3 : 2);
    }
    q2_previous_ex1 = actual_ex1;
}

VOID CountQ1(const std::vector<REG>* srcs,
             const std::vector<REG>* dsts)
{
    const UINT64 nominal_decode = q1_previous_decode + 1;
    UINT64 actual_decode = nominal_decode;

    // Wait for every input, including store data. Overlapping waits
    // count only once, so use the maximum rather than adding waits.
    for (REG src : *srcs) {
        if (q1_ready[src] > actual_decode) {
            actual_decode = q1_ready[src];
        }
    }
    stalls_q1 += static_cast<int>(actual_decode - nominal_decode);

    // Read sources before updating destinations for read/write operands.
    // Every producer writes at WB, three cycles after its Decode.
    for (REG dst : *dsts) {
        q1_ready[dst] = actual_decode + 3;
    }
    q1_previous_decode = actual_decode; //update q1 is count
}

void CountLDUH(
    std::vector<REG>* srcs,
    std::vector<REG>* dsts,
    bool isLoad,
    int storeValueOp)
{
    insCount++;
    if (isLoad) loads++;

    // Check whether this instruction needs a previous load's result.
    for (int i = 0; (size_t)i < srcs->size(); i++) {
        if (i != storeValueOp &&
            reg_ready[(*srcs)[i]] > insCount) {
            lduh++;
            break;  // Count at most one hazard per instruction.
        }
    }

    // A load's destination is unavailable to the next instruction.
    for (REG dst : *dsts) {
        if (isLoad) {
            reg_ready[dst] = insCount + 2;
        }
    }
}
/* ===================================================================== */
// Instrumentation callbacks
/* ===================================================================== */


VOID Instruction(INS insn, VOID* v)
{
    // Keep Q1's dependency lists separate from the original Lab 0 counter.
    // Pin's register lists include address registers and implicit operands.
    // Model overlapping names (e.g. EAX/RAX) as one RISC-like register;
    // this is a whole-register approximation, not byte-level x86 tracking.
    std::vector<REG>* q1_srcs = new std::vector<REG>();
    std::vector<REG>* q1_dsts = new std::vector<REG>();
    for (UINT32 i = 0; i < INS_MaxNumRRegs(insn); ++i) {
        REG reg = INS_RegR(insn, i);
        if (reg == REG_INVALID()) continue;
        reg = REG_FullRegName(reg);
        // Do not treat instruction-pointer updates as RF data hazards.
        if (reg != REG_INVALID() && reg != REG_INST_PTR) q1_srcs->push_back(reg);
    }
    for (UINT32 i = 0; i < INS_MaxNumWRegs(insn); ++i) {
        REG reg = INS_RegW(insn, i);
        if (reg == REG_INVALID()) continue;
        reg = REG_FullRegName(reg);
        // Do not treat instruction-pointer updates as RF data hazards.
        if (reg != REG_INVALID() && reg != REG_INST_PTR) q1_dsts->push_back(reg);
    }
    INS_InsertCall(insn, IPOINT_BEFORE, (AFUNPTR)CountQ1,
        IARG_PTR, q1_srcs,
        IARG_PTR, q1_dsts,
        IARG_END);

  std::vector<REG> *srcs = new std::vector<REG>();
  std::vector<REG> *dsts = new std::vector<REG>();
  for (UINT32 i = 0; i < INS_OperandCount(insn); i++)
  {
    REG reg = INS_OperandReg(insn, i);
    if (reg == REG_INVALID()) continue;
    if (INS_OperandRead(insn, i)) srcs->push_back(reg);
    if (INS_OperandWritten(insn, i)) dsts->push_back(reg);
  }
  bool isLoad = INS_IsMemoryRead(insn);
  INS_InsertCall(insn, IPOINT_BEFORE, (AFUNPTR)CountLDUH,
        IARG_ADDRINT, srcs,
        IARG_ADDRINT, dsts,
        IARG_BOOL, isLoad,
        IARG_ADDRINT, storeOps(insn),
        IARG_END);
    
    // Both models read the same immutable register lists, but maintain
    // separate clocks and readiness arrays. Count instructions only once
    // in the original CountLDUH callback below.
    INS_InsertCall(insn, IPOINT_BEFORE, (AFUNPTR)CountQ2,
        IARG_PTR, q1_srcs,
        IARG_PTR, q1_dsts,
        IARG_BOOL, INS_IsMemoryRead(insn),
        IARG_UINT32, static_cast<UINT32>(StoreDataOnlyReg(insn)),
        IARG_END);
    
}

/*!
 * Print out analysis results.
 * This function is called when the application exits.
 * @param[in]   code            exit code of the application
 * @param[in]   v               value specified by the tool in the 
 *                              PIN_AddFiniFunction function call
 */
VOID Fini(INT32 code, VOID* v)
{
    cerr << "===============================================" << endl;
    cerr << "Load-to-use Hazard analysis results: " << endl;
    cerr << "Number of instructions: " << insCount << endl;
    cerr << "Number of load instructions: " << loads << endl;
    cerr << "Number of load-to-use hazards: " << lduh << endl;
    const double cpi_q1 = insCount > 0
        ? 1.0 + static_cast<double>(stalls_q1) / insCount : 1.0;
    const double slowdown_q1 = 100.0 * (1.0 - 1.0 / cpi_q1);
    const double cpi_q2 = insCount > 0
        ? 1.0 + static_cast<double>(stalls_q2) / insCount : 1.0;
    const double slowdown_q2 = 100.0 * (1.0 - 1.0 / cpi_q2);
    fprintf(stderr, "Question 1 stall cycles: %d CPI %lf slowdown: %lf%%\n", stalls_q1, cpi_q1, slowdown_q1);
    fprintf(stderr, "Question 2 stall cycles: %d CPI %lf slowdown: %lf%%\n", stalls_q2, cpi_q2, slowdown_q2);
    cerr << "===============================================" << endl;
}

/*!
 * The main procedure of the tool.
 * This function is called when the application image is loaded but not yet started.
 * @param[in]   argc            total number of elements in the argv array
 * @param[in]   argv            array of command line arguments, 
 *                              including pin -t <toolname> -- ...
 */
int main(int argc, char* argv[])
{
    // Initialize PIN library. Print help message if -h(elp) is specified
    // in the command line or the command line is invalid
    if (PIN_Init(argc, argv))
    {
        return -1;
    }

    INS_AddInstrumentFunction(Instruction, 0);
    // Register function to be called when the application exits
    PIN_AddFiniFunction(Fini, 0);


    // Start the program, never returns
    PIN_StartProgram();

    return 0;
}

/* ===================================================================== */
/* eof */
/* ===================================================================== */
