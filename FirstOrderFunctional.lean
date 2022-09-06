/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat
-/

/-
Implementation of a partial evaluator for a simple
first order, function language with `call` instructions.

#### Language Δ from CFG
In this language, we have function arguments, as opposed to global mutable
variables in the CFG.

#### Division Δ 
In the CFG language, a division divided global vars into static/dynamic.
Here, we divide function arguments into static/dynamic.

Monovariant division: division per function *definition*
Polyvariant division: division per function *callsite*.

#### Specialiation points Δ

Can perform specialization at other locations, such as if/then/else.
This will be performed by lifting such defns to the toplevel.

#### Binding time analysis Δ
Can choose to perform either  dataflow style abstract interpretation (AI), or
constraint style AI, where the constraints are later solved. Constraint style
will be used for lambda calculus.
-/

