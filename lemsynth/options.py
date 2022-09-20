# This is an options module that is used by the lemma synthesis source code.

import os
import importlib_resources

# SyGuS solver that supports only ground constraints and uses constraint-solving methods
minisy = 'minisy'
# Enumerative general-purpose SyGuS solver
cvc4sy = 'cvc4sy'

log_file_path = os.path.abspath(importlib_resources.files('lemsynth')/'../logs')

debug = True

# Verbosity as a positive number. 0 is completely silent.
verbose = 0
# Option to instrument code and time several parts of the pipeline
analytics = True


############################## USERS LOOK IN THIS BLOCK #################################################
# Setting lemma synthesis options here. Modifying these will give you ablated versions of the tool.
# fossil --- this is the default setting that uses all three kinds of counterexamples and the custom constraint based solver we implemented
# fossil-cvc4sy --- this is the same as above, except that it uses cvc4sy as the sygus solver
# no-type-2 --- this departs from the default tool by only using Type-3 counterexamples for unprovable/invalid lemmas and does not try to find Type-2 counterxamples
# no-cex --- this ablation does not use any counterexamples except Type-1 (for guidance towards the goal), and uses cvc4sy to stream solutions to sygus queries

settings = ['fossil','fossil-cvc4sy','no-type-2','no-cex']

mode = 'fossil' # Change this to a different setting to get other versions of the tool

###########################################################################################################



streaming_synthesis_switch = False
use_cex_models = False
use_cex_true_models = True
synthesis_solver = minisy

if mode == 'fossil':
    pass
elif mode == 'fossil-cvc4sy':
    synthesis_solver = cvc4sy
elif mode == 'no-type-2':
    use_cex_models = True
    use_cex_true_models = False
elif mode == 'no-cex':
    streaming_synthesis_switch = True
    use_cex_models = False
    use_cex_true_models = False
    synthesis_solver = cvc4sy
else:
    raise ValueError('Unknown tool configuration. Look at fossil/lemsynth/options.py and make sure the mode is one of the allowed options.')

