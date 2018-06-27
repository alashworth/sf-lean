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
  /- ==> day.monday -/

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

This declaration makes an assertion (that the second weekday after
saturday is tuesday). Having made the assertion, we ask Lean to verify
it, using the ``rfl`` term.

The details are not important for now (we'll come back to them in a
bit), but essentially this can be read as "the assertion we've just
made can be proved by observing that both sides of the equality
evaluate to the same thing."

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

In a similar way, we can define the standard type ``bool`` of
booleans, with members ``tt`` and ``ff``.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: bool'
  :lines: -2

Although we are rolling our own booleans here for the sake of building
up everything from scratch, Lean does, of course, provide a default
implementation of the booleans, together with a multitude of useful
functions and lemmas. (Take a look at ``/library/init/core.lean/`` if
you're interested.) Whenever possible, we'll name our own definitions
and theorems so that they exactly coincide with the ones in the
standard library, but with a quote mark.

Functions over booleans can be defined in the same way as above:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: bnot'
  :end-at: | tt tt := ff.

These examples show the use of Lean's *equation compiler* for
definitions. The corresponding multi-argument application syntax is
illustrated by the following "unit tests," which constitute a complete
specification — a truth table — for the ``bor`` function:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-after: /- bor unit tests -/
  :lines: -4

Exercise: 1 star (bnand)
************************

Remove ``sorry`` and complete the definition of the following
function; then make sure that the ``example`` assertions below can each be
verified by Lean. (Remove ``sorry`` and fill in each proof, following
the model of the ``bor'`` tests above.) The function should return ``tt`` if
either or both of its inputs are ``ff``.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-after: -- Exercise: 1 star (nandb)
  :lines: -8

Exercise: 1 star (band3)
************************

Do the same for the band3 function below. This function should return
true when all of its inputs are ``tt``, and ``ff`` otherwise.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-after: -- Exercise: 1 star (band3)
  :lines: -8

Function Types
--------------
..
   to be continued

Every expression in Lean has a type, describing what sort of thing it
computes. The ``#check`` command asks Lean to print the type of an
expression.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: #check bool'.tt
  :lines: -4

Functions like negb itself are also data values, just like true and
false. Their types are called function types, and they are written
with arrows.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: #check bnot'
  :lines: -2

The type of ``bnot'``, written ``bool → bool`` and pronounced "bool arrow
bool," can be read, "Given an input of type bool, this function
produces an output of type bool." Similarly, the type of ``band'``, written
``bool → bool → bool``, can be read, "Given two inputs, both of type bool,
this function produces an output of type bool."


Compound Types
--------------------------------------------------------------------------------

The types we have defined so far are examples of "enumerated types":
their definitions explicitly enumerate a finite set of elements, each
of which is just a bare constructor. Here is a more interesting type
definition, where one of the constructors takes an argument:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: inductive rgb : Type
  :end-at:   | primary : rgb → color

Let's look at this in a little more detail.

Every inductively defined type (``day``, ``bool``, ``rgb``, ``color``,
etc.) contains a set of constructor expressions built from
constructors like ``red``, ``primary``, ``tt``, ``ff``, ``monday``,
etc. The definitions of ``rgb`` and ``color`` say how expressions in
the sets ``rgb`` and ``color`` can be built:

 * ``red``, ``green``, and ``blue`` are the constructors of ``rgb``;
 * ``black``, ``white``, and ``primary`` are the constructors of
   ``color``;
 * the expression ``red`` belongs to the set ``rgb``, as do the
   expressions ``green`` and ``blue``;
 * the expressions ``black`` and ``white`` belong to the set ``color``;
 * if ``p`` is an expression belonging to the set ``rgb``, then
   ``primary p`` (pronounced "the constructor ``primary`` applied to
   the argument ``p``") is an expression belonging to the set
   ``color``; and
 * expressions formed in these ways are the only ones belonging to the
   sets ``rgb`` and ``color``.

We can define functions on colors using pattern matching just as we
have done for day and bool.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: def monochrome : color → bool'
  :end-at:    | (primary p) := ff

Since the primary constructor takes an argument, a pattern matching
primary should include either a variable (as above) or a constant of
appropriate type (as below).

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: def isred : color → bool'
  :end-at:   | (primary _)   := ff

The pattern ``primary _`` here is shorthand for "primary applied to any
rgb constructor except red." (The wildcard pattern ``_`` has the same
effect as the dummy pattern variable ``p`` in the definition of
``monochrome``.)

Namespaces
----------

Lean provides a name space system, to aid in organizing large
developments. If we enclose a collection of declarations between
``namespace X`` and ``end X`` markers, then, in the remainder of the
file after the End, these definitions are referred to by names like
``X.foo`` instead of just ``foo``. We will use this language feature
to introduce the definition of the type nat in an inner module so that
it does not interfere with the one from the standard library (which we
want to use in the rest because it comes with a tiny bit of convenient
special notation).

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: namespace nat_playground
  :lines: -1

Numbers
-------

An even more interesting way of defining a type is to allow its
constructors to take arguments from the very same type — that is, to
allow the rules describing its elements to be *inductive*.

For example, we can define (a unary representation of) natural numbers
as follows:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: inductive nat : Type
  :lines: -3

The clauses of this definition can be read:
 * ``zero`` is a natural number.
 * ``succ`` can be put in front of a natural number to yield another
   one — if ``n`` is a natural number, then ``succ n`` is too.

Again, let's look at this in a little more detail. The definition of
``nat`` says how expressions in the set ``nat`` can be built:
 * ``zero`` and ``succ`` are constructors;
 * the expression ``zero`` belongs to the set ``nat``;
 * if ``n`` is an expression belonging to the set ``nat``, then ``succ
   n`` is also an expression belonging to the set ``nat``; and
 * expressions formed in these two ways are the only ones belonging to
   the set ``nat``.

The same rules apply for our definitions of day, bool, color, etc.

The above conditions are the precise force of the Inductive
declaration. They imply that the expression ``zero``, the expression
``succ zero``, the expression ``succ (succ zero)``, the expression
``succ (succ (succ zero))``, and so on all belong to the set nat,
while other expressions built from data constructors, like ``tt``,
``andb tt ff``, ``succ (succ ff)``, and ``zero (zero (zero succ))`` do
not.

A critical point here is that what we've done so far is just to define
a representation of numbers: a way of writing them down. The names
``zero`` and ``succ`` are arbitrary, and at this point they have no
special meaning — they are just two different marks that we can use to
write down numbers (together with a rule that says any ``nat`` will be
written as some string of ``succ`` marks followed by a ``zero``). If
we like, we can write essentially the same definition this way:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: inductive nat' : Type
  :lines: -3

The *interpretation* of these marks comes from how we use them to
compute.

We can do this by writing functions that pattern match on
representations of natural numbers just as we did above with booleans
and days — for example, here is the predecessor function:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: open nat_playground.nat
  :lines: -4

The second branch can be read: "if ``n`` has the form ``succ n'`` for
some ``n'``, then return ``n'``."

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: end nat_playground
  :lines: -1

Because natural numbers are such a pervasive form of data, Lean
provides a tiny bit of built-in magic for parsing and printing them:
ordinary arabic numerals can be used as an alternative to the "unary"
notation defined by the constructors ``succ`` and ``zero``. Lean
prints numbers in arabic form by default:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-after: /- define minustwo -/
  :end-before: /- end minustwo -/

The constructor ``succ`` has the type ``nat → nat``, just like
``pred`` and functions like ``minustwo``:

.. code-block:: lean

    #check succ
    #check pred
    #check minustwo

These are all things that can be applied to a number to yield a
number. However, there is a fundamental difference between the first
one and the other two: functions like ``pred`` and ``minustwo`` come
with computation rules — e.g., the definition of ``pred`` says that
``pred 2`` can be simplified to ``1`` — while the definition of
``succ`` has no such behavior attached. Although it is like a function
in the sense that it can be applied to an argument, it does not do
anything at all! It is just a way of writing down numbers. (Think
about standard arabic numerals: the numeral ``1`` is not a
computation; it's a piece of data. When we write ``111`` to mean the
number one hundred and eleven, we are using ``1``, three times, to
write down a concrete representation of a number.)

For most function definitions over numbers, just pattern matching is
not enough: we also need recursion. For example, to check that a
number ``n`` is even, we may need to recursively check whether ``n-2``
is even:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: def evenb : nat → bool
  :lines: -4

We can define ``oddb`` by a similar recursive function, but here is a
simpler definition:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: def oddb (n:nat) : bool := bnot (evenb n)
  :end-at: example : oddb 4 = ff := rfl

(You will notice if you step through these proofs that simpl actually
has no effect on the goal — all of the work is done by
reflexivity. We'll see more about why that is shortly.)

Naturally, we can also define multi-argument functions by recursion.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: namespace nat_playground2
  :end-at:   | (succ n) m := succ (plus n m)

Adding three to two now gives us five, as we'd expect.

.. code-block:: lean

   #reduce (plus 3 2)

The simplification that Lean performs to reach this conclusion can be visualized as follows:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-after: /- plus eval -/
  :end-before:   /- plus eval (end) -/

You can match two expressions at once by putting a comma between them:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: def minus : nat → nat → nat
  :end-at:     | (succ n) (succ m) := minus n m

Again, the ``_`` in the first line is a wildcard pattern. Writing
``_`` in a pattern is the same as writing some variable that doesn't
get used on the right-hand side. This avoids the need to invent a
variable name.

As a notational convenience, if two or more arguments have the same
type, they can be written together. In the following definition, ``(n
m : nat)`` means just the same as if we had written ``(n : nat) (m :
nat)``.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-after: /- subtracted_from -/
  :lines: -1

So far, we have only displayed function arguments by either naming all
of them or matching them in a function's equation. The function
``mult`` below illustrates how we can mix and match the two styles:

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: def mult (m : nat) : nat → nat
  :end-at:    | (succ n) := plus m (mult n)

Notice how the recursive call to ``mult``, ``(mult n)`` is given only
one argument. This is because the named arguments --- ``m`` in our
case --- implicitly remain the same through recursive calls. It can
sometimes shorten the recursive calls in complex functions defined by
recursion.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: def exp (base : nat) : nat → nat
  :end-at: end nat_playground2

Exercise: 1 star (factorial)
****************************

Recall the standard mathematical factorial function:

.. code-block:: text

       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)

Translate this into Lean.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-after: -- Exercise: 1 star (factorial)
  :end-at: lemma test_factorial2

We can make numerical expressions a little easier to read and write by
introducing *notations* for addition, multiplication, and subtraction.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: infixl +
  :end-at: infixl *

(``infixl`` adds a new *infix*, *left-associative* operator. Other
keywords can be used for defining notation such as ``infix``,
``infixr`` (right-associative) and ``notation`` (for free-form
notation).  "More on Notation" section at the end of this chapter.)

Note that these do not change the definitions we've already made: they
are simply instructions to the Lean parser to accept ``x + y`` in
place of ``plus x y`` and, conversely, to the Lean pretty-printer to
display ``plus x y`` as ``x + y``.

When we say that Lean comes with almost nothing built-in, we really
mean it: even equality testing for numbers is a user-defined
operation! We now define a function ``beq_nat``, which tests natural
numbers for equality, yielding a boolean. Note the use of nested
matches (we could also have used a simultaneous match, as we did in
minus.)

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: def beq_nat
  :lines: -5

The leb function tests whether its first argument is less than or
equal to its second argument, yielding a boolean.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: def leb
  :end-at: lemma test_leb3

Exercise: 1 star (blt_nat)
****************************

The blt_nat function tests natural numbers for less-than, yielding a
boolean. Instead of making up a new recursive function for this one, define it
in terms of a previously defined functions.

.. literalinclude:: ../../src/basics.lean
  :language: lean
  :start-at: -- Exercise: 1 star (blt_nat)
  :end-at: lemma test_blt_nat3

Proof by Simplification
=======================

Proof by Rewriting
==================

Proof by Case Analysis
======================

More on Notation
----------------

Fixpoints and Structural Recursion
----------------------------------

More Exercises
==============
