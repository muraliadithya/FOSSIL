#!/usr/bin/env bash
# test_all.sh — run the FOSSIL benchmark-suite.
#
# Iterates benchmark-suite/*.py, runs each with a 360s timeout, reports
# SUCCESS/FAILURE, exits 0/1.
#
# The grammar suite (grammars/*.sy via CVC4) is in a SEPARATE script,
# test_grammars.sh, run by its own CI job (workflow_dispatch). It is intentionally
# decoupled from test_all.sh so that grammar-suite issues (e.g. CVC4 flag
# compatibility) do not fail the benchmark-suite job. The lvl1 *.sy files
# (grammar_*-lvl1.sy) are covered by test_grammars.sh.
#
# NOTE: the project uses shared temporary files (see README). Do NOT run this
# script in parallel with another instance of the same benchmark.
#
# NOTE: the benchmark-suite requires the `minisy` binary from the mini-sygus
# repo (github.com/muraliadithya/mini-sygus) to be on PATH. Without it every
# benchmark fails with "minisy: not found".

set -u

COUNT=1
NUM_ERRORS=0

function report_case () {
  if [ "$1" == 0 ]
  then printf "%s | %s | SUCCESS: %ss\n" "$COUNT" "$2" "$3"
  else
    printf "%s | %s | FAILURE: %ss\n" "$COUNT" "$2" "$3"
    NUM_ERRORS=$(( NUM_ERRORS + 1 ))
  fi
}

function final_report () {
  if [ "$NUM_ERRORS" == 0 ]
  then printf "    %s programs have been successfully run.\n" "$(( COUNT - 1 ))"
       exit 0
  else printf "    %s out of %s programs did not successfully run.\n" "$NUM_ERRORS" "$(( COUNT - 1 ))"
       exit 1
  fi
}

# --- Part 1: benchmark-suite (original behaviour) ---------------------------
for file in benchmark-suite/*.py; do
  [ -e "$file" ] || continue
  printf "Running %s:\n--------------------------------------------------\n" "$file"
  START=$(date +%s)
  timeout 360 python3 -u "$file"
  exit_code=$?
  END=$(date +%s)
  DIFF=$(( END - START ))
  report_case "$exit_code" "$file" "$DIFF"
  printf "\n"
  COUNT=$(( COUNT + 1 ))
done
printf -- "---------------------------------------------------\n"

final_report
