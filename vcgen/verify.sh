#!/usr/bin/env bash

python3 bbgen.py $1

progfile="${1##*/}"
progname="${progfile%.fsl}"

for file in .tmp/"$progname"/*.fsl
do
  [[ -e "$file" ]] || break;  # handle the case of no *.fsl files
  filename=${file##*/};
  printf "\nRunning %s\n" "${filename%.fsl}";
  time python3 -u bbverify.py "$file"
done;
