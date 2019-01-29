# lisp500
A mostly-joking implementation of a lisp in just 500 lines of C.

The original public posting of this has been lost, so I searched for it in my own archives and am reposting it.
This only really exists because of oneupmanship and a poorly-thought-out claim that you can implement lisp
in 500 lines of C. Well, you can, but it's not a very useful lisp. But then you can have an init file (in lisp)
fixing some of the problems in usefulness.

## compilation

gcc -m32 -o lisp500 lisp500.c
or
clang -m32 -o lisp500 lisp500.c

(It's really nothing but assumptions that the word size is 32 bits so -m32 is required.)

## running

./lisp500 init500.lisp

You can also run just ./lisp500 and use the barebones version.

## issues

The last three symbols (JREF, RUN-PROGRAM, UNAME) seem to be uninitialized even though the count is correct.
Has there been a bug there always, and it has just become uncovered by compiler advances? Couldn't tell at first
glance what would overwrite them. This means init500 does not work, so I have to fix it.
