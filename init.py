import re
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


def bracket_sub (sub):
    """ Brackets a substitution pair.

    Args:
        sub (tuple): The substitution pair to bracket.

    Returns:
        tuple: The bracketed substitution pair.
    """
    return ('\{\{\\s*' + sub[0] + '\\s*\}\}', sub[1])


def fill_template (path, subs):
    """ Fills a template file.

    Args:
        path (str): The path of the target file.
    """
    replace_in_file(path, [bracket_sub(sub) for sub in subs])


# Makefile in and out paths.
MAKEFILE_DIST = './src/Makefile.dist'
MAKEFILE_OUT = './src/Makefile'

# Copy Makefile template.
copyfile(MAKEFILE_DIST, MAKEFILE_OUT)
print('Copied', MAKEFILE_DIST, 'to', MAKEFILE_OUT)

# Customise Makefile.
root_ns = input('What root namespace would you like your code to reside under? ')
fill_template('./src/Makefile', [('root_ns', root_ns)])
print('Root namespace populated in', MAKEFILE_OUT)

# Gather config params from user.
config_params = []
buffer = input('Would you like to build your policy configuration parameters interactively now? [y/N] ')
while buffer.lower() == 'y':
    name = input('Please name your parameter: ')
    type = input(f'For parameter {name} please specify a type: ')
    config_params.append((name, type))
    buffer = input('Add another parameter? [y/N] ')

# Export config  params to template.
fill_template('./src/Authority.v', [('config_params', ' * '.join([param[1] for param in config_params]))])

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

fill_template('./src/Authority.v', [('config_lookups', '\n  '.join([f'| "{pol[0]}" => ({pol[1]})' for pol in pols]))])
