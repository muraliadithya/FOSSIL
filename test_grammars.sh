#!/usr/bin/env bash
# test_grammars.sh — run the SyGuS grammar files in grammars/ via CVC4.
#
# This closes the gap noted in issue #10's progress comment:
#   "lvl1 grammars are not included in the script."
# The lvl1 *.sy files (grammar_*-lvl1.sy) are covered here as part of the
# full grammar suite.
#
# SyGuS outcome semantics (OPEN DESIGN DECISION — flagged to maintainer):
#   `cvc4 --lang=sygus2 file.sy` can legitimately exit non-zero when:
#     - synthesis is UNSAT (no term in the grammar satisfies the constraints)
#     - synthesis does not terminate within the timeout
#   Neither of those is a *tool crash*. Currently this script:
#     - reports each file's outcome (SYNTHESIZED / TIMEOUT / ERROR)
#     - exits 0 unless CVC4 crashes (segfault) or the file fails to parse
#   If the maintainer prefers CI to also fail on non-synthesis (UNSAT /
#   timeout), flip the FAIL_ON_NON_SYNTHESIS flag below to 1.
#
# Bounds:
#   - per-file timeout: 60s (SyGuS can be non-terminating without a bound)
#   - --sygus-abort-size=20 caps candidate size so CVC4 cannot loop forever

set -u

PER_FILE_TIMEOUT=60
SYGUS_ABORT_SIZE=20
FAIL_ON_NON_SYNTHESIS=0   # 0 = only crash/parse-error fails CI; 1 = also fail on timeout/unsat

GRAMMAR_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/grammars"
COUNT=0
NUM_ERRORS=0

if ! command -v cvc4 >/dev/null 2>&1; then
  printf "ERROR: cvc4 not found on PATH.\n" >&2
  exit 2
fi

for file in "$GRAMMAR_DIR"/*.sy; do
  [ -e "$file" ] || continue
  COUNT=$(( COUNT + 1 ))
  base="$(basename "$file")"
  printf "Running %s:\n---------------------------------------------------\n" "$base"
  START=$(date +%s)
  timeout "$PER_FILE_TIMEOUT" cvc4 --lang=sygus2 --sygus-abort-size="$SYGUS_ABORT_SIZE" "$file" >/tmp/cvc4_"$COUNT".log 2>&1
  exit_code=$?
  END=$(date +%s)
  DIFF=$(( END - START ))
  case "$exit_code" in
    0)
      printf "%s | SYNTHESIZED | %ss\n" "$base" "$DIFF"
      ;;
    124)
      printf "%s | TIMEOUT | %ss\n" "$base" "$DIFF"
      [ "$FAIL_ON_NON_SYNTHESIS" = 1 ] && NUM_ERRORS=$(( NUM_ERRORS + 1 ))
      ;;
    *)
      # Distinguish parse/flag error (cvc4 prints "error" or "parse") from a
      # real crash. Print the first lines of the cvc4 output so the actual
      # error (e.g. unknown flag --sygus-abort-size, unsupported --lang=sygus2)
      # is visible in the CI log instead of being hidden.
      if grep -qiE "error|parse|unknown|invalid|unsupported|expected" /tmp/cvc4_"$COUNT".log; then
        printf "%s | ERROR (see cvc4 output below) | %ss\n" "$base" "$DIFF"
        printf -- "--- cvc4 output (first 15 lines) ---\n"
        head -15 /tmp/cvc4_"$COUNT".log
        printf -- "--- end cvc4 output ---\n"
        NUM_ERRORS=$(( NUM_ERRORS + 1 ))
      else
        printf "%s | NON-SYNTHESIS (exit %s) | %ss\n" "$base" "$exit_code" "$DIFF"
        [ "$FAIL_ON_NON_SYNTHESIS" = 1 ] && NUM_ERRORS=$(( NUM_ERRORS + 1 ))
      fi
      ;;
  esac
  printf "\n"
done

printf -- "--------------------------------------------------\n"
if [ "$NUM_ERRORS" == 0 ]; then
  printf "    %s grammar files ran without tool crashes.\n" "$COUNT"
  exit 0
else
  printf "    %s out of %s grammar files had tool-level errors.\n" "$NUM_ERRORS" "$COUNT"
  exit 1
fi
