#!/usr/bin/env bash
COUNT=1
NUM_ERRORS=0

function report_case () {
  if [ $1 == 0 ]
  then printf "\e[94m%s\e[0m %s \e[1m%s\e[0m \e[32m %s\e[0m\n" "$COUNT" "|" $2 "SUCCESS: $3s"
  else
    printf "\e[94m%s\e[0m %s \e[1m%s\e[0m \e[31m %s\e[0m\n" "$COUNT" "|" $2 "FAILURE: $3s";
    (( NUM_ERRORS += 1 ));
  fi
}

function final_report () {
  if [ $NUM_ERRORS == 0 ]
  then (printf "    \e[1m\e[32m$(( COUNT-1 )) programs have been successfully run.\e[0m\n"; exit 0)
  else (printf "    \e[1m\e[31m$NUM_ERRORS out of $(( COUNT-1 )) programs did not successfully run.\e[0m\n"; exit 1)
  fi
}

for file in `ls benchmark-suite/*.py`
# for file in $(cat lvl1.txt)
# for file in `ls benchmark-suite/reachability*.py`
  do
    printf "Running $file:\n---------------------------------------------------\n";
    START=$(date +%s)
    timeout 300 python3 $file
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
