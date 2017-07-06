# propcheck

This package provides several Haskell modules for interfacing with
propositional logic. It also provides an executable called check,
which automatically parses and checks a proof file in a format we
specify.

## Introduction

propcheck is intended as an educational tool provided as an aide to
those wanting to learn about proofs in propositional logic
(constructive and classical). It is both a code library and a
command-line tool. propcheck is a proof *checker* for propositional
logic proofs written in the Gentzen-style natural deduction. We
adapted our proof rules from the book "Type Theory and Functional
Programming" by Simon Thompson. The primitive connectives are &, |,
=>, and \_|\_. There are two abbreviated connectives, ~a (a => \_|\_) and
a <=> b (a => b & b => a).

## Installation

This is a Haskell project. I use the Haskell Stack tool to build and
maintain it, but you don't need that to build it. However, you do need
the basic Haskell command line tools, including ghc and
cabal. Assuming you have those tools, you can install it by standing
in the top-level directory and typing

```
$ cabal install
```

This should install all dependencies, as well as the project, in your
default installation directory (usually ~/.local/bin). If you add that
directory to your path, you should be able to run the "check"
executable.

## Running

Try running the check command:

```
$ check
Please specify a path.
For help on using check, run "check --help".
```

Okay, sure:

```
$ check --help
check [OPTIONS] [FILE]
  PropCheck propositional logic checker (check) 0.0.1, June 2017.
  Copyright 2017 Ben Selfridge. All rights reserved.

  -p --proof    Show the parsed proof along with the theorem.
     --rules    Print the complete list of derivation rules that can be used
                in a proof. Use this flag in conjunction with --sample to
                figure out the correct format for writing proof files.
  -s --sample   Print a sample proof to stdout. To test this, redirect the
                file to a file with > sample.pf and run `check sample.pf`.
  -? --help     Display help message
  -V --version  Print version information
```

Generate a simple proof with the -s command:

```
$ check -s > simple.pf
```

Take a look at this file to see an example of a proof, or just run check on it:

```
$ check simple.pf
Thm: [a => b, b => c] |- a => c
```

This output says that the proof supplied demonstrates the formula a =>
c is valid, given the top-level assumptions a => b and b => c.

To see the entire proof as parsed by check, use the -p option:

```
$ check -p simple.pf
Thm: [a => b, b => c] |- a => c
Proof:
a => c [ImpliesIntro]
  c [ImpliesElim]
    b [ImpliesElim]
      a [Assumption]*
      a => b [Assumption]
    b => c [Assumption]
```

To find out more about the proof format, take a look at the examples
in the examples/ folder. You can also get a complete listing of the
inference rules by running "check --rules".
