# Skeptic Authority Template
A basic template for a Skeptic authority.

## Overview
A Skeptic _authority_ is an application, written in Coq and utilising [Coq.io](http://coq.io/), that accepts or rejects passwords based on password composition policies refined from  configuration parameters specified with respect to some piece of password composition policy enforecment software. Because we do this from within Coq, we are granted the freedom to write theorems to verify that our transformation of software-specific configuration parameters to a low-level predicate-based representation of password composition policies is correct.

The low-level model of password composition policies used in this library is based on [the 2013 work by Blocki et al.](https://arxiv.org/pdf/1302.5101.pdf) extended with meta-rules, which are just predicates that allow us to create rules from attacks using set abstraction.

## Setup
Every piece of password composition policy enforecment software is different. For this reason, it's necessary to specify the type of their configuration options before we get started writing any proofs etc. An interactive script named `init.py` is provided to get you started with this. What follows is an example of how we would go about setting this project up for a piece of hypothetical password composition policy enforcement software that takes password length, required number of digits and a blacklist as input.

Firstly, run `init.py` like so:

```bash
python3 init.py
```

We'll then be asked to specify a root namespace for our project. In this case, let's just call it `HypotheticalAuthority`:

```bash
Copied ./src/Makefile.dist to ./src/Makefile
What root namespace would you like your code to reside under? HypotheticalAuthority
Root namespace populated in ./src/Makefile
```

Your Coq project is now set up (this will be important later).

You'll then be asked about the configuration parameters your piece of password composition policy enforement software takes. In this case, we specify that it takes a length (as a natural number), a number of digits (as a natural number) and a blacklist (as a list of strings).

```bash
Would you like to build your policy configuration parameters interactively now? [y/N] y
Please name your parameter: length
For parameter length please specify a type: nat
Add another parameter? [y/N] y
Please name your parameter: digits
For parameter digits please specify a type: nat
Add another parameter? [y/N] y
Please name your parameter: blacklist
For parameter blacklist please specify a type: list string
Add another parameter? [y/N] n
```

You've now made the script aware of the configuration parameters taken by the piece of software you're modelling, as well as their types. Next, we'll be able to pre-configure some policies. Let's informally specify what they do now:

* `basic8`: Passwords must have minimum length 8, no other constraints.
* `basic16`: Passwords must have minimum  length 16, no other constraints.
* `digit8`: Passwords must have minimum length 8 and at least 1 digit.
* `dict8`: Passwords must have minimum length 8 and cannot be `password` or `hunter2`.

Now let's get to specifying these:

```bash
Would you like to preconfigure some policies interactively now? [y/N] y
Please name your policy: basic8
For parameter length please specify a value in type nat: 8
For parameter digits please specify a value in type nat: 0
For parameter blacklist please specify a value in type list string: []
Add another policy? [y/N] y
Please name your policy: basic16
For parameter length please specify a value in type nat: 16
For parameter digits please specify a value in type nat: 0
For parameter blacklist please specify a value in type list string: []
Add another policy? [y/N] y
Please name your policy: digit8
For parameter length please specify a value in type nat: 8
For parameter digits please specify a value in type nat: 1
For parameter blacklist please specify a value in type list string: []
Add another policy? [y/N] y
Please name your policy: dict8
For parameter length please specify a value in type nat: 8
For parameter digits please specify a value in type nat: 0
For parameter blacklist please specify a value in type list string: ["password"; "hunter2"]
Add another policy? [y/N] n
```

Now we're done, we can go ahead and delete the template files and `init.py` script, which are just used for code generation and can be removed.

```bash
All done, delete template files and this script now? [y/N] y
```

Now, take a look in `/src/Authority.py`. You'll notice that a type has been generated for us which captures our configuration parameters. Notice the two natural numbers in `nat` for length and digits and a list of strings in `list string` for the blacklist:

```coq
(** Definition of the data type for the password composition policy enforcement
    software configuration parameters.
  *)
Definition Configuration : Type :=
  (nat * nat * list string).
```

Also notice that a lookup has been generated for finding configuration parameters based on policy name:

```Coq
(** Looks up a configuration parameters tuple by name.
    - [name] is the name of the tuple to look up
  *)
Definition lookup_config (name : string) : option Configuration :=
  match name with
  | "basic8" => Some (8, 0, [])
  | "basic16" => Some (16, 0, [])
  | "digit8" => Some (8, 1, [])
  | "dict8" => Some (8, 0, ["password"; "hunter2"])
  | _ => None
  end.
```
