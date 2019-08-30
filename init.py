import re
import os
import sys
from shutil import copyfile

#print re.findall(r'"(.*?)"', string)


def read_file (path):
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


def fill_template (path, subs, comms=False):
    """ Fills a template file.

    Args:
        path (str): The path of the target file.
    """
    # Substitute with and without commenting.
    all_subs = [bracket_sub(sub, comms) for sub in subs]
    replace_in_file(path, all_subs)


def build_param_bul (param):
    """ Builds a configuration parameter documentation bullet from a parameter tuple.

    Args:
        param (tuple): The paramter tuple.

    Returns:
        string: The documentation bullet markdown.
    """
    return param[0] + ' (' + param[1] + '): ' + param[2]


def build_policies (path, config_params):
    print(config_params)
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
    fill_template(path, [('config_lookups', '\n  '.join([f'| "{pol[0]}" => Some ({pol[1]})' for pol in pols]
        + ['(* {{ config_lookups }} *)']))], True) # Comment is maintained here for future use.


def strip_all (lst):
    return list(map(lambda x: x.strip(), lst))


def append_policies (file):
    existing_file = read_file(AUTH_OUT) # Read in existing authority.
    # Try to pull out types.
    rv_types = re.findall(r'Definition\s*Configuration\s*:\s*Type\s*:=\s*\((.*?)\)\.', existing_file)
    if len(rv_types) == 0:
        print('Couldn\'t parse configuration parameter types out of your file. Aborting program.')
        exit(0)
    rv_types = strip_all(rv_types[0].split('*')) # Split along asterisks (type).
    # Try to pull out names.``
    rv_names = re.findall(r'match\s*config\s*with\s*\|\s*\((.*?)\)', existing_file)
    if len(rv_names) == 0:
        print('Couldn\'t parse configuration parameter names out of your file. Aborting program.')
        exit(0)
    rv_names = strip_all(rv_names[0].split(',')) # Split along commas (value).
    # Try to pull out descriptions.
    rv_desc_exps = [re.compile(pair[0] + '\s*\(\s*' + pair[1] + '\s*\):\s*(.+)') for pair in zip(rv_names, rv_types)]
    rv_descs = [re.findall(exp, existing_file) for exp in rv_desc_exps]
    if len(rv_descs) == 0:
        print('Couldn\'t parse configuration parameter descriptions out of your file. Aborting program.')
        exit(0)
    rv_descs = strip_all([rv_desc[0] for rv_desc in rv_descs]) # Split along commas (value).
    # Check for agreement.
    if any(map(lambda x: x != len(rv_types), [len(rv_types), len(rv_names), len(rv_descs)])):
        print('Couldn\'t get consistent name, type and description for all configuration parameters. Aborting program.')
        exit(0)
    # Brief user on configuration parameters.
    param_index = 1
    config_params = list(zip(rv_names, rv_types, rv_descs))
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
    # Proceed to build policies.
    build_policies(file, config_params)


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
