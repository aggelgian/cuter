#!/usr/bin/env python3
# -*- coding: utf-8 -*-

##
## Solves the constraints in a trace file offline.
##

import sys, getopt, os
import subprocess as subp
import cuter_io as cIO
import cuter_smt as cSMT
import cuter_common as cc
import cuter_print as cpt
import cuter_global as cglb

VERBOSE = True

def solve(fname, n, printConstraints):
  # Do the initializations.
  cglb.init()
  erlSolver = cSMT.ErlangSMT(1)
  # Load the trace.
  r = cIO.JsonReader(fname, n)
  if printConstraints:
    print("### TRACE")
  all_entries = list(r)
  for i, (entry, rev) in enumerate(all_entries):
      if printConstraints:
        if i == len(all_entries) - 1:
          print("[TO BE REVERSED]", end=" ")
        cpt.print_cmd(entry, rev)
      if cc.is_interpretable(entry):
        erlSolver.command_toSolver(entry, rev)
  if printConstraints:
    print()
  # Load the axioms to the solver.
  erlSolver.add_axioms()
  # Solve the model.
  slv = erlSolver.solve()
  if VERBOSE:
    print(str(slv).strip())
  if cc.is_sat(slv):
      m = erlSolver.encode_model()
      if VERBOSE:
        print(str(m).strip())
      values = [e.value.value for e in m.model.entries]
      return (slv, values)
  return slv

def usage():
  print("Usage: cuter_solve_offline.py TraceFile NoOfConstraint [ OPTIONS ]")
  print("PARAMETERS")
  print("	TraceFile		The trace file of an execution.")
  print("	NoOfConstraint		The cardinality of the constraint to reverse.")
  print("OPTIONS")
  print("	--print-constraints	Print all the commands as they are being loaded (for debugging).")
  print("	-e Dir			Dir is the ebin.")
  print("	-u Dir			Dir is the utest ebin.")
  print("	--help			Display this information.")

def run_tests(ebin, utestEbin):
  VERBOSE = False
  fname = "logfile"
  cmd = " ".join(["erl", "-noshell", "-pa", ebin, "-pa", utestEbin, "-eval",
    "\"cuter_tests_lib:sample_trace_file(\\\"{}\\\")\"".format(fname), "-s", "init", "stop"])
  subp.call(cmd, shell=True)
  result = solve(fname, 3, False)
  assert len(result), "Solver error"
  assert cc.is_sat(result[0]), "Not SAT status"
  assert ["1", "44"] == result[1], "Wrong model: {}".format(result[1])
  try:
    os.remove(fname)
  except OSError:
    pass

if __name__ == "__main__":
  shortOpts = "u:e:"
  longOpts = ["print-constraints", "help"]
  optlist, remainder = getopt.gnu_getopt(sys.argv[1:], shortOpts, longOpts)
  printConstraints = False
  ebin, utestEbin = None, None
  for opt, arg in optlist:
    if opt == "--help":
      usage()
      sys.exit(0)
    elif opt == "--print-constraints":
      printConstraints = True
    elif opt == "-u":
      utestEbin = arg
    elif opt == "-e":
      ebin = arg
  if ebin != None or utestEbin != None:
    sys.exit(run_tests(ebin, utestEbin))
  solve(remainder[0], int(remainder[1]), printConstraints)
