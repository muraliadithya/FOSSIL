#!/usr/bin/env bash


for i in {1..100}; do python3 -u genregression.py $i; echo "Running repetition ${i}"; time python3 -u runbench.py reg.fsl 1; done
