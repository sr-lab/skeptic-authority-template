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
    replace_in_file(path, list(map(bracket_sub, subs)))


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
