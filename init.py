import re
import os
import sys
from shutil import copyfile


def replace_in_file (path, subs):
    """ Performs a set of substitutions in a text file.

    Args:
        path (str): The path of the target file.
        subs (list of tuple): A list of pairs of terms and their replacements.
    """
    # Compile regular expressions.
    compiled_subs = []
    for old, new in subs:
        compiled_subs.append((re.compile(old), new))
    # Perform replacement.
    buffer = []
    with open(path) as file:
        for line in file:
            processed_line = line
            for old, new in compiled_subs:
                processed_line = re.sub(old, new, processed_line)
            buffer.append(processed_line)
    with open(path, 'w') as file:
        for line in buffer:
            file.write(line)


def bracket_sub (sub, commenting=False):
    """ Brackets a substitution pair.

    Args:
        sub (tuple): The substitution pair to bracket.
        commenting (bool): Whether or not to comment the bracketed pair.

    Returns:
        tuple: The bracketed substitution pair.
    """
    if commenting:
        return ('\(\*\s*\{\{\\s*' + sub[0] + '\\s*\}\}\s*\*\)', sub[1])
    else:
        return ('\{\{\\s*' + sub[0] + '\\s*\}\}', sub[1])


def fill_template (path, subs):
    """ Fills a template file.

    Args:
        path (str): The path of the target file.
    """
    # Substitute with and without commenting.
    all_subs = [bracket_sub(sub, True) for sub in subs] + [bracket_sub(sub) for sub in subs]
    replace_in_file(path, all_subs)


def build_param_bul (param):
    """ Builds a configuraiton parameter documentation bullet from a parameter tuple.

    Args:
        param (tuple): The paramter tuple.
    """
    return param[0] + ' (' + param[1] + '): ' + param[2]


# Makefile in and out paths.
MAKEFILE_DIST = './src/Makefile.dist'
MAKEFILE_OUT = './src/Makefile'

# Authority in and out paths.
AUTH_DIST = './src/Authority.v.dist'
AUTH_OUT =  './src/Authority.v'

# Copy Makefile template.
copyfile(MAKEFILE_DIST, MAKEFILE_OUT)
print('Copied', MAKEFILE_DIST, 'to', MAKEFILE_OUT)

# Customise Makefile.
root_ns = input('What root namespace would you like your code to reside under? ')
fill_template('./src/Makefile', [('root_ns', root_ns)])
print('Root namespace populated in', MAKEFILE_OUT)

# Copy authority template.
copyfile(AUTH_DIST, AUTH_OUT)
print('Copied', AUTH_DIST, 'to', AUTH_OUT)

# Gather config params from user.
config_params = []
buffer = input('Would you like to build your policy configuration parameters interactively now? [y/N] ')
while buffer.lower() == 'y':
    name = input('Please name your parameter: ')
    type = input(f'For parameter {name} please specify a type: ')
    description = input(f'Please describe the function of parameter {name}: ')
    config_params.append((name, type, description))
    buffer = input('Add another parameter? [y/N] ')

# Export config params and names to template.
fill_template(AUTH_OUT, [('config_param_types', ' * '.join([param[1] for param in config_params]))])
fill_template(AUTH_OUT, [('config_param_names', ', '.join([param[0] for param in config_params]))])
fill_template(AUTH_OUT, [('config_param_descs', '\n    - '.join([build_param_bul(param) for param in config_params]))])

# Interactively build policies.
buffer = input('Would you like to preconfigure some policies interactively now? [y/N] ')
pols = []
while buffer.lower() == 'y':
    name = input('Please name your policy: ')
    vals = []
    for config_param in config_params:
        val = input(f'For parameter {config_param[0]} please specify a value in type {config_param[1]}: ')
        vals.append(val)
    pols.append((name, ', '.join(vals)))
    buffer = input('Add another policy? [y/N] ')

# Export config lookups to template.
fill_template(AUTH_OUT, [('config_lookups', '\n  '.join([f'| "{pol[0]}" => Some ({pol[1]})' for pol in pols]))])

# Delete templates if requested.
buffer = input('All done, delete template files and this script now? [y/N] ')
if buffer == 'y':
    os.remove(MAKEFILE_DIST)
    os.remove(AUTH_DIST)
    os.remove(sys.argv[0])
