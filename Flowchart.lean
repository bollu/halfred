/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat
-/

/-
Implementation of a partial evaluator for a simple
first order, control flow graph based language.
-/
import Lean
open Std 

namespace CFG

/- Names of variables. -/
abbrev Name := String 

/- The value domain of integers -/
inductive Val 
| int: Int → Val 
deriving Inhabited, BEq, Hashable 

/-
Stores map names to (static/dynamic) values.
Used to store statically known state of the partial evaluator
-/
abbrev Store := HashMap Name Val

def Val.int? (v: Val): Option Int := 
  match v with 
  | Val.int i => .some i 

/- Assembly instructions -/
inductive Op 
| add | sub | eqp 
deriving Inhabited, BEq 

/- Expressions are right hand sides of assignments -/
inductive Expr where  
| const: Val → Expr 
| var: Name → Expr 
| op: Op → Array Expr → Expr 
deriving Inhabited, BEq 


/-
Evaluate an expression, the heart of the partial evaluator:
evaluate expressions at compile time into known constants
-/
partial def Expr.eval (e: Expr) (f: Store): Val := 
  match e with 
  | Expr.const v => v 
  | Expr.var x => f.findD x (Val.int 0)
  | Expr.op o args => 
    let args := args.map (λ e => e.eval f)
    match o, args with 
    | Op.add, #[Val.int x, Val.int y] => Val.int (x + y)
    | Op.sub, #[Val.int x, Val.int y] => Val.int (x - y)
    | Op.eqp, #[Val.int x, Val.int y] => 
      Val.int (if x == y then 1 else 0)
    | _, _ => Val.int 0

partial def Expr.evaluable? (e: Expr): Bool := 
  match e with 
  | Expr.const _ => true 
  | Expr.var _ => false 
  | Expr.op _o args => 
    (args.map Expr.evaluable?).all id 

partial def Expr.reduce (e: Expr) (f: Store): Expr := 
  match e with 
  | Expr.const _v => e 
  | Expr.var x => 
    match f.find? x with 
    | .some v => Expr.const v 
    | .none => e
  | Expr.op o args =>
    let args := args.map (λ e => e.reduce f)
    match o, args with 
    | Op.add, #[Expr.const (Val.int x), Expr.const (Val.int y)] => 
      Expr.const (Val.int (x + y))
    | Op.sub, #[Expr.const (Val.int x), Expr.const (Val.int y)] => 
      Expr.const (Val.int (x - y))
    | Op.eqp, #[Expr.const (Val.int x), Expr.const (Val.int y)] => 
      Expr.const (Val.int (if x == y then 1 else 0))
    | _, _ => Expr.op o args


/- Substitute assignments from Store into Expr -/
partial def Expr.substVars (e: Expr) (f: Store) : Expr := 
  match e with 
  | Expr.const v => Expr.const v
  | Expr.var n => 
    match f.find? n with 
    | some v => Expr.const v
    | none => Expr.var n
  | Expr.op o es => Expr.op o (es.map (λ e => e.substVars f))

/- Control flow terminators -/
inductive Jump (ix: Type) where 
| goto: ix → Jump ix 
| condbr: Expr → ix → ix → Jump ix 
| return: Expr → Jump ix
deriving Inhabited 

namespace Jump
def mapIx {ix ix': Type} (f: ix → ix'): Jump ix →  Jump ix'
| Jump.goto ix => Jump.goto (f ix)
| Jump.return e => Jump.return e
| Jump.condbr e ixt ixf => Jump.condbr e (f ixt) (f ixf)
end Jump


instance [BEq ix] : BEq (Jump ix) where 
  beq j1 j2 := 
    match j1, j2 with 
    | Jump.goto i1, Jump.goto i2 => i1 == i2
    | Jump.condbr e1 bbl bbr, Jump.condbr e2 bbl' bbr' => 
        e1 == e2 && bbl == bbl' && bbr == bbr'
    | Jump.return e1, Jump.return e2 => e1 == e2
    | _, _ => false

/- Assignment (`lhs` := `rhs`) -/
structure Assignment where 
  lhs: Name 
  rhs: Expr
  deriving Inhabited, BEq 

def Assignment.substVars (a: Assignment) (args: Store): Assignment := 
  { lhs := a.lhs, rhs := a.rhs.substVars args }

def Assignment.reduce (a: Assignment) (args: Store): Assignment := 
  { lhs := a.lhs, rhs := a.rhs.reduce args }

/- 
A basic block has a label indexed by `ix`, a sequence
of assignments, and ends with an optional terminator.
-/
structure BasicBlock (ix: Type) where 
  label: ix
  stmts: Array Assignment := #[]
  jump: Option (Jump ix) := .none 

namespace BasicBlock
def mapIx {ix ix': Type} (f: ix → ix') (bb: BasicBlock ix): BasicBlock ix' where
  label := f bb.label
  stmts := bb.stmts
  jump := bb.jump.map (Jump.mapIx  f)

def setJump 
  (bb: BasicBlock ix) (j: Jump ix): BasicBlock ix := 
  { bb with jump := .some j }

def mapAssignments {ix: Type}
  (f: Assignment → Assignment) (bb: BasicBlock ix): BasicBlock ix := 
  {bb with stmts := bb.stmts.map f}

def appendAssignment {ix: Type} 
  (a: Assignment)
  (bb: BasicBlock ix): BasicBlock ix := 
  {bb with stmts := bb.stmts.push a}

instance [Inhabited ix] : Inhabited (BasicBlock ix) where 
  default := { label := default, stmts := #[], jump := default }

instance [BEq ix]: BEq (BasicBlock ix) where 
  beq b1 b2 := 
    b1.label == b2.label && 
    b1.stmts.toList == b2.stmts.toList && 
    b1.jump == b2.jump
end BasicBlock

structure Program (ix: Type) [BEq ix] [Hashable ix] where 
  reads: Array Name  -- program
  bbs: HashMap ix (BasicBlock ix)
  entryIx: ix
  deriving Inhabited

namespace Program

variable [BEq ix]
variable [Hashable ix]

def getEntryBlock [Inhabited ix] (p: Program ix): BasicBlock ix := 
  p.bbs.find! p.entryIx

def getBlock [Inhabited ix] [BEq ix] (p: Program ix) (i: ix):BasicBlock ix := p.bbs.find! i

-- Add a new block with the given label if none exists, or overwrite if one already does.
def addOrOverwriteBlock [Inhabited ix] [BEq ix] (p: Program ix) (bb: BasicBlock ix): Program ix := 
  { p with bbs := p.bbs.insert bb.label bb }

def mapIx [BEq ix'] [Hashable ix'] (f: ix → ix') (p: Program ix): Program ix' where 
  reads := p.reads
  entryIx := f p.entryIx
  bbs := p.bbs.fold (fun bbs' ix bb => bbs'.insert (f ix) (bb.mapIx f)) default


instance [BEq ix]: BEq (Program ix) where
  beq p1 p2 := 
    p1.reads == p2.reads && 
    p1.bbs.toArray == p2.bbs.toArray -- TODO: better [BEq] instance?
end Program 

structure ProgramPoint (ix: Type) where 
  bbix: ix 
  stmtix: Nat
  deriving Inhabited, BEq, Hashable

-- Terrible hash function for Store created by cascading hashes of kv pairs
instance : Hashable Store where 
  hash s := 
    let h := s.toList.foldl (fun h (n, v) => hash (h,  hash n, hash v)) (UInt64.ofNat 0)
    hash h

abbrev RegularIx := Nat
abbrev RegularProgramPoint := ProgramPoint RegularIx

structure SpecializedIx  where 
  pp: RegularIx
  vs: Store -- data the program is specialized for.  
  deriving Inhabited, Hashable 


def RegularIx.toSpecialized (vs: Store) (pp: RegularIx): SpecializedIx := 
  SpecializedIx.mk pp vs

instance : BEq SpecializedIx where 
  beq s1 s2 := 
    s1.pp == s2.pp && 
    s1.vs.toList == s2.vs.toList

-- Worklist driven specialization algorithm
partial def go (worklist: Array (BasicBlock SpecializedIx × Store))
  (division: HashSet Name)
  (prog: Program SpecializedIx): Program SpecializedIx := 
    if worklist.size == 0 then prog
    else Id.run $ do
     let mut worklist' := #[]
     let mut p' : Program SpecializedIx := prog
     for (bb, vs) in worklist do {
        let mut vs' := vs;
        let mut bb' := bb;
        for a in bb.stmts do {
          let a' := a.substVars vs';
          if a'.rhs.evaluable? then {
            let v := a'.rhs.eval vs;
            vs' := vs.insert a'.lhs v;
          } else  {
            let a' := a.reduce vs';
            bb' := bb'.appendAssignment a';
          }
        };
        match bb.jump.get! with 
        | Jump.return _xs => pure ()
        | Jump.goto l => 
            worklist' := worklist'.push (p'.getBlock l, vs')
        | Jump.condbr e ltrue lfalse =>
          let e := e.substVars vs';
          if e.evaluable? then {
            let v := e.eval vs';
            let lnext := if v.int? == .some 1 then ltrue else lfalse;
            bb' := bb'.setJump (Jump.goto lnext);
            worklist' := worklist'.push (p'.getBlock lnext, vs');
          } else { -- not evaluable
            -- do the boring work of giving up and forwarding information
            -- to successor basic blocks.
            bb' := bb'.setJump (Jump.condbr (e.reduce vs') ltrue lfalse)
          }
          p' := p'.addOrOverwriteBlock bb';
      }
     go worklist' division p' -- contnue for another iteration
      

def specialize (p: Program RegularIx)
  (division: HashSet Name)
  (vs: Store): Program SpecializedIx := 
    -- Start with the empty store since we 
    -- have not analyzed anything yet
    let p' := p.mapIx (RegularIx.toSpecialized (vs := {}))
    -- Add the entry block into the worklist, and run the specializer
    go (worklist := #[(p'.getEntryBlock, vs)])
       (division := division)
       p'

   

-- poly:
-- set of specialized program points that are reached
--   during execution.


-- reduce: specialize a static/dynamic thing
-- eval: evaluate a fully static value.
-- it would be weird to say "evaluate a mixed static/dynamic term",
--  but it seems totally chill to refer to it as
--  "reduce a mixed static/dynamic term".

-- a division which ensures `poly` is finite is called a 
-- finite division.

-- Undecidable which should be dynamic. Approximation in ch.14.
-- Given a division of the inputs, can compute
--  division for every other program point. This is called
--  **binding time analysis**.
end CFG

def main : IO Unit := pure ()
