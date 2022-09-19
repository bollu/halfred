/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat
-/

/-
Implementation of a partial evaluator for a simple
lambda calculus with fixpoints.
-/

inductive Const where
| int: int -> Const

inductive Val where
| ValConst: Const -> Val
| ValFun: (Val -> Val)  -- encoding will not work in Lean due to universes. non-+ve
     -> Val


