#!/usr/bin/bash -i

pip install -r requirements.txt

echo '' >> ~/.bashrc
echo '# Setting PATH and PYTHONPATH variables for FOSSIL artifact' >> ~/.bashrc
echo 'export PATH="'$PWD'":$PATH' >> ~/.bashrc
echo 'export PATH="'$PWD'/entrypoints":$PATH' >> ~/.bashrc
echo 'export PYTHONPATH="'$PWD'":$PYTHONPATH' >> ~/.bashrc
echo '' >> ~/.bashrc

source ~/.bashrc

# testing minisy
minisy -h >/dev/null 2>&1 || { echo >&2 "SyGuS solver minisy was not found in PATH Aborting."; exit 1; }

solverout=$(minisy tests/minisy_test.sy 2>&1)

if [[ $? -ne 0 ]]; then
    echo "Problem executing minisy SyGuS solver. Aborting."; exit 1
fi

if [[ $solverout != "(define-fun sub ((x Int) (y Int)) Int (op x y))" ]]; then
    echo "Problem executing minisy SyGuS solver. The output was:"; echo $solverout; exit 1
fi


# testing z3
z3 --version >/dev/null 2>&1 || { echo >&2 "z3 not found in PATH. Aborting."; exit 1; }

if [[ $(z3 --version) != "Z3 version 4.10.2 - 64 bit" ]]; then
    echo "The command 'z3' appears to resolve to a different program than the one we have provided. Be warned that our results may not be reproducible. To resolve this add the following line to your .bashrc:
alias z3='/path/to/entrypoints/z3'
and then execute source ~/.bashrc to add this update to your current terminal session."
fi


# testing cvc4
cvc4 --version >/dev/null 2>&1 || { echo >&2 "cvc4 not found in PATH. Aborting."; exit 1; }

if [[ $(cvc4 --version | head -n 1) != "This is CVC4 version 1.9-prerelease [git master e6c9674d]" ]]; then
    echo "The command 'cvc4' appears to resolve to a different program than the one we have provided. Be warned that our results may not be reproducible. To resolve this add the following line to your .bashrc:
alias cvc4='/path/to/entrypoints/cvc4'
and then execute source ~/.bashrc to add this update to your current terminal session."
fi

# cleanup
./clean.sh

echo ""
echo "Installation successful!"

# Restart bash
exec bash
