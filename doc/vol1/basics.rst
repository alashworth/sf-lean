================================================================================
Functional Programming in Lean
================================================================================

Source code: `basics.lean <../../../src/basics.lean>`_

Introduction
================================================================================

The functional programming style is founded on simple, everyday mathematical
intuition: if a procedure or method has no side effects, then (ignoring
efficiency) all we need to understand about it is how it maps inputs to outputs,
i.e. we can think of it as just a concrete method for computing a mathematical
function. This is one sense of the word "functional" in "functional
programming." The direct connection between programs and simple mathematical
objects supports both formal correctness proofs and sound informal reasoning
about program behavior. 

The other sense in which functional programming is "functional" is that it
emphasizes the use of functions (or methods) as first-class values — i.e.,
values that can be passed as arguments to other functions, returned as results,
included in data structures, etc. The recognition that functions can be treated
as data gives rise to a host of useful and powerful programming idioms. 

Other common features of functional languages include *algebraic data types* and
*pattern matching*, which make it easy to construct and manipulate rich data
structures, and sophisticated polymorphic type systems supporting abstraction
and code reuse. Lean offers all of these features. 

The first half of this chapter introduces the most essential elements of Lean.
The second half introduces some basic tactics that can be used to prove
properties of Lean programs.

Data and Functions
================================================================================

Enumerated Types
--------------------------------------------------------------------------------

One notable aspect of Lean is that its set of built-in features is *extremely*
small. For example, instead of providing the usual palette of atomic data types
(booleans, integers, strings, etc.), Lean offers a powerful mechanism for
defining new data types from scratch, with all these familiar types as
instances. Naturally, the Lean distribution comes preloaded with an extensive
standard library providing definitions of booleans, numbers, and many common
data structures like lists and hash tables. But there is nothing magic or
primitive about these library definitions. To illustrate this, we will
explicitly restate all the definitions we need, before importing them implicitly
from the library.

Days of the Week
--------------------------------------------------------------------------------

To see how this definition mechanism works, let's start with a very simple
example. The following declaration tells Lean that we are defining a new set of
data values — a *type*.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: inductive day : Type
  :end-at: saturday

The type is called day, and its members are monday, tuesday, etc. The second and
following lines of the definition can be read "monday is a day, tuesday is a
day, etc." Having defined day, we can write functions that operate on days.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: def next_weekday : day → day
  :end-at: | day.saturday := day.monday

One thing to note is that the argument and return types of this function are
explicitly declared. Like most functional programming languages, Lean can often
figure out these types for itself when they are not given explicitly — i.e., it
can do type inference — but we'll generally include them to make reading easier.

Having defined a function, we should check that it works on some examples. There
are actually three different ways to do this in Lean. First, we can use the
command ``#reduce`` to evaluate a compound expression involving
``next_weekday``.

.. code-block:: lean

  #reduce next_weekday day.sunday
  [Lean] day.monday

(We show Lean's responses in comments, but, if you have a computer handy, this
would be an excellent moment to fire up the Lean server under your favorite text
editor — either VSCode or Emacs — and try this for yourself. Load this file,
basics.lean, from the book's Lean sources, find the above example, submit it to
Lean, and observe the result.)

Second, we can record what we expect the result to be in the form of a Lean
example:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: example : next_weekday
  :lines: 1

This declaration makes an assertion (that the second weekday after saturday is tuesday). Having made the assertion, we ask Lean to verify it, using the ``rfl`` term. 

The details are not important for now (we'll come back to them in a bit), but essentially this can be read as "the assertion we've just made can be proved by observing that both sides of the equality evaluate to the same thing."

Third, we can ask Lean to extract, from our ``def``, a program in some other,
more conventional, programming language (C++) with a high-performance compiler.
This facility is very interesting, since it gives us a way to go from
proved-correct algorithms written in Lean to efficient machine code. (Of course,
we are trusting the correctness of the C++ compiler, and of Lean's extraction
facility itself, but this is still a big step forward from the way most software
is developed today.) Indeed, this is one of the main uses for which Lean was
developed. We'll come back to this topic in later chapters.

Booleans
--------------------------------------------------------------------------------

In a similar way, we can define the standard type ``bool`` of booleans, with members ``tt`` and ``ff``. 

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: bool'
  :lines: -2

Although we are rolling our own booleans here for the sake of building up everything from scratch, Lean does, of course, provide a default implementation of the booleans, together with a multitude of useful functions and lemmas. (Take a look at ``/library/init/core.lean/`` if you're interested.) Whenever possible, we'll name our own definitions and theorems so that they exactly coincide with the ones in the standard library, but with a quote mark.

Functions over booleans can be defined in the same way as above:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: bnot'
  :end-at: | tt tt := ff.

These examples show the use of Lean's *equation compiler* for definitions. The corresponding multi-argument application syntax is illustrated by the following "unit tests," which constitute a complete specification — a truth table — for the ``bor`` function:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-after: /- bor unit tests -/
  :lines: -4

Function Types
--------------------------------------------------------------------------------

Compound Types
--------------------------------------------------------------------------------

Modules
--------------------------------------------------------------------------------

Numbers
--------------------------------------------------------------------------------

Proof by Simplification
================================================================================

Proof by Rewriting
================================================================================

Proof by Case Analysis
================================================================================

More on Notation
--------------------------------------------------------------------------------

Fixpoints and Structural Recursion
--------------------------------------------------------------------------------

More Exercises
================================================================================