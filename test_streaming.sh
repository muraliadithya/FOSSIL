#!/usr/bin/env bash
COUNT=1
NUM_ERRORS=0

function report_case () {
  if [ $1 == 0 ]
  then printf "%s %s %s %s\n" "$COUNT" "|" $2 "SUCCESS: $3s"
  else
    printf "%s %s %s %s\n" "$COUNT" "|" $2 "FAILURE: $3s";
    (( NUM_ERRORS += 1 ));
  fi
}

function final_report () {
  if [ $NUM_ERRORS == 0 ]
  then (printf "    $(( COUNT-1 )) programs have been successfully run.\n"; exit 0)
  else (printf "    $NUM_ERRORS out of $(( COUNT-1 )) programs did not successfully run.\n"; exit 1)
  fi
}

for file in `ls benchmark-suite/*.py`
  do
    printf "Running $file:\n---------------------------------------------------\n";
    START=$(date +%s)
    timeout 3600 python3 -u $file
    exit_code=$?
    END=$(date +%s)
    DIFF=$(( $END - $START ))
    if [ $exit_code != 0 ]
      then report_case 1 $file $DIFF
      else report_case 0 $file $DIFF
    fi;
    printf "\n";
    (( COUNT+=1 ));
done;
printf -- "---------------------------------------------------\n"

final_report
