# lisp500
A mostly-joking implementation of a lisp in just 500 lines of C.

The original public posting of this has been lost, so I searched for it in my own archives and am reposting it.
This only really exists because of oneupmanship and a poorly-thought-out claim that you can implement lisp
in 500 lines of C. Well, you can, but it's not a very useful lisp. But then you can have an init file (in lisp)
fixing some of the problems in usefulness.

It used to compile and work in 2004 when it was written, but the world has changed. I guess it could be made
to work again, and maybe I will.

## compilation

gcc -m32 -Wno-empty-body -o lisp500 lisp500.c

(It's really nothing but assumptions the word size is 32 bits.)

## issues

The last three symbols (JREF, RUN-PROGRAM, UNAME) seem to be uninitialized even though the count is correct.
Has there been a bug there always, and it has just become uncovered by compiler advances? Couldn't tell at first
glance what would overwrite them. This means init500 does not work, so I have to fix it.
