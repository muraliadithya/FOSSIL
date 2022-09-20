# Artifact for OOPSLA 2022 Paper Model-Guided Synthesis of Inductive Lemmas for FOL with Least Fixpoints

See the full version of our paper [here](https://arxiv.org/abs/2009.10207).  

Our tool is called FOSSIL: First-Order Solver for Synthesizing Inductive Lemmas. The tool is evolving, and we are continuing to make it more user friendly! See our [github repo](https://github.com/muraliadithya/FOSSIL) for the latest version of the tool.  

The following installation instructions are meant for linux users, with easy installation for Ubuntu users (64 bit). The tool has been tested and can be installed on Ubuntu, MacOS, as well as Windows by following the instructions appropriately for the corresponding OS.

## Installation

1. Make sure that you have [Python 3.6 or above](https://www.python.org/downloads/)
2. (Easy install for Ubuntu users) Execute the script `./install.sh`. You should get `Installation successful!` if it is successful. If you are on a different OS or are unable to do the easy install, do the following:
    * Install the requirements in `requirements.txt`. If you have pip, this can be done by running `pip install -r requirements.txt`.
    * Add the top level of this directory as well as the `entrypoints/` subdirectory to your `PATH` environment variable, and the top level of the directory to your `PYTHONPATH` environment variable.
    * The above steps make sure that the commands `z3` and `cvc4` resolve to the binaries that we have provided within the `entrypoints/` subdirectory. 
    * At this point, the following commands should execute successfully: `minisy tests/minisy_test.sy`, `z3 --version`, and `cvc4 --version`. The tool has been tested with z3 version 4.10.2, and cvc4 version 1.9 (pre-release). The tool should be runnable with other versions of these solvers, but results may vary.
3. Command `timeout` is needed to reproduce our experiments. On MacOS, run the following in order to obtain the `timeout` command:
    - `brew install coreutils`
    - `sudo ln -s /usr/local/bin/gtimeout /usr/local/bin/timeout`

## Experiments

* We have two benchmark suites, as well as options that you can set to run ablated versions of the tool.
* The following are the scripts corresponding to the two benchmark suites:
    - To run the tool on the first suite consisting of problems obtained from the heap verification domain, do `python3 suite1.py`.
    - To run the tool on the the second suite of synthetic problems, do `./autobench.sh`.
* The tool has several 'modes'. The default mode is that of the main FOSSIL tool reported in the paper. The ablated versions of the tools can be obtained by following the instructions in `lemsynth/options.py`
    - If you want to run the tool on the first suite without any counterexamples (using cvc4sy for streaming solutions), use `./test_streaming.sh` instead of the usual python script.
* Check out our github repo for more specific instructions on running individual benchmarks.

### Notes
1. The project uses temporary files to store and read data during execution. Therefore, it is not advisable to run multiple instances of the same benchmark as they will each write to the same temporary files.
2. To clean up temporary files generated, run `./clean.sh`.

## Contact Authors

If you have any issues or wish to report a bug, please contact us by raising an issue on our github repo (preferred), or write to the contact author Adithya Murali at `adithya5@illinois.edu`.

## Citations

* [Z3](https://github.com/Z3Prover/z3)
* [Z3Py](https://pypi.org/project/z3-solver/)
* [CVC4](https://cvc4.github.io/)

## License

This work is licensed under the MIT License.  
Copyright (c) 2022 Adithya Murali
