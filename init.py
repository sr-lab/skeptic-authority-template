import re
import os
import sys
from shutil import copyfile


def read_file (path):
    """ Reads the entire contents of a text file and returns it.

    Args:
        path (str): The path of the file to read.
    Returns:
        str: The contents of the file.
    """
    buffer = []
    with open(path) as file:
        for line in file:
            buffer.append(line)
    return ''.join(buffer)


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


def bracket_sub (sub, comment=False):
    """ Brackets a substitution pair.

    Args:
        sub (tuple): The substitution pair to bracket.
        comment (bool): Whether or not to comment the bracketed pair.

    Returns:
        tuple: The bracketed substitution pair.
    """
    if comment:
        return ('\(\*\s*\{\{\\s*' + sub[0] + '\\s*\}\}\s*\*\)', sub[1])
    else:
        return ('\{\{\\s*' + sub[0] + '\\s*\}\}', sub[1])


def fill_template (path, subs, comment=False):
    """ Fills a template file.

    Args:
        path (str): The path of the target file.
        subs (list of tuple): The list of substitution pairs.
        comment (bool): Whether or not to replace commented tempalating expressions.
    """
    # Substitute with and without commenting.
    all_subs = [bracket_sub(sub, comment) for sub in subs]
    replace_in_file(path, all_subs)


def build_param_bul (param):
    """ Builds a configuration parameter documentation bullet from a parameter tuple.

    Args:
        param (tuple): The parameter tuple.

    Returns:
        string: The documentation bullet markdown.
    """
    return param[0] + ' (' + param[1] + '): ' + param[2]


def build_policies (path, config_params, prompt=True):
    """ Builds policies interactively according to the given configuration parameters.

    Args:
        path (str): The path of the authority file to write to.
        config_params (list of tuple): The configuration parameter tuples.
        prompt (bool): If true, the user will be able to opt out.
    """
    buffer = input('Would you like to preconfigure some policies interactively now? [y/N] ') if prompt else 'y'
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
    fill_template(path, [('config_lookups', '\n  '.join([f'| "{pol[0]}" => Some ({pol[1]})' for pol in pols]
        + ['(* {{ config_lookups }} *)']))], True) # Comment is maintained here for future use.


def strip_all (lst):
    """ Strips leading and trailing whitespace from all strings in a list.

    Args:
        lst (list of str): The list of strings to strip.

    Returns:
        list of str: The list of stripped strings.
    """
    return list(map(lambda x: x.strip(), lst))


def append_policies (file):
    """ Attempts to append policies to an existing authority file.

    Args:
        file (str): The path of the existing authority file.
    """
    ex_file = read_file(AUTH_OUT) # Read in existing authority.
    # Try to pull out existing configuration parameter types.
    ex_types = re.findall(r'Definition\s*Configuration\s*:\s*Type\s*:=\s*\((.*?)\)\.', ex_file)
    if len(ex_types) == 0:
        print('Couldn\'t parse configuration parameter types out of your file. Aborting program.')
        exit(1)
    ex_types = strip_all(ex_types[0].split('*')) # Split along asterisks (type).
    # Try to pull out existing configuration parameter names.``
    ex_names = re.findall(r'match\s*config\s*with\s*\|\s*\((.*?)\)', ex_file)
    if len(ex_names) == 0:
        print('Couldn\'t parse configuration parameter names out of your file. Aborting program.')
        exit(1)
    ex_names = strip_all(ex_names[0].split(',')) # Split along commas (value).
    # Try to pull out existing configuration parameter descriptions.
    ex_desc_exps = [re.compile(pair[0] + '\s*\(\s*' + pair[1] + '\s*\):\s*(.+)') for pair in zip(ex_names, ex_types)]
    ex_descs = [re.findall(exp, ex_file) for exp in ex_desc_exps]
    if len(ex_descs) == 0:
        print('Couldn\'t parse configuration parameter descriptions out of your file. Aborting program.')
        exit(1)
    ex_descs = strip_all([ex_desc[0] for ex_desc in ex_descs]) # Split along commas (value).
    # Check for agreement.
    if any(map(lambda x: x != len(ex_types), [len(ex_names), len(ex_descs)])):
        print('Couldn\'t get consistent name, type and description for all configuration parameters. Aborting program.')
        exit(1)
    # Brief user on existing configuration parameters and confirm correctness.
    param_index = 1
    config_params = list(zip(ex_names, ex_types, ex_descs))
    print('The authority seems to support the following configuration parameters:')
    for config_param in config_params:
        print(f'{param_index}. {config_param[0]} in type {config_param[1]}')
        print(f'   {config_param[2]}')
        param_index += 1
    print('If this looks right, proceed. If it doesn\'t then ignoring this warning might mess up your file!')
    conf = input('Continue? [y/N] ')
    if conf.lower() != 'y':
        print('Aborting program.')
        exit(0)
    # Proceed to build policies interactively.
    build_policies(file, config_params, False)


# Makefile in and out paths.
MAKEFILE_DIST = './src/Makefile.dist'
MAKEFILE_OUT = './src/Makefile'

# Authority in and out paths.
AUTH_DIST = './src/Authority.v.dist'
AUTH_OUT =  './src/Authority.v'

# Check if output already generated.
if os.path.isfile(AUTH_OUT):
    print('It seems like you have already generated an authority. You now have two options:')
    print('\t1. Abort this program. No files will be changed.')
    print('\t2. Attempt to append polices to the existing authority.')
    print('\t3. Start over, discarding the authority completely.')
    opt = input('Please select an option [1-3]: ')
    if opt == '1':
        print('Aborting program.') # User explicitly aborts program.
        exit(0)
    elif opt == '2':
        append_policies(AUTH_OUT) # Different flow now.
        exit(0)
    elif opt == '3':
        print('This will destroy your existing file at: ' + AUTH_OUT)
        conf = input('Are you sure? [y/N] ')
        if conf.lower() != 'y':
            print('Aborting program.') # Only a yes here will overwrite old file.
            exit(0)
    else:
        print('Invalid option. Aborting program.') # Be safe and abort program.
        exit(0)

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
build_policies(AUTH_OUT, config_params)

# Delete templates if requested.
buffer = input('All done, delete template files and this script now? [y/N] ')
if buffer == 'y':
    os.remove(MAKEFILE_DIST)
    os.remove(AUTH_DIST)
    os.remove(sys.argv[0])
