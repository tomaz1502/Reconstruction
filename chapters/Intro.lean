import Lean

namespace Elab

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta

syntax (name := elabTerm) "#elab" term : command

@[commandElab elabTerm] def evalElab : CommandElab
  | `(#elab%$tk $term) => withoutModifyingEnv $ runTermElabM none fun _ => do
    let e ← Term.elabTerm term none
    unless e.isSyntheticSorry do
      logInfoAt tk m!"{e} ::: {repr e}"
  | _ => throwUnsupportedSyntax

end Elab

variable (A B C : Prop)

#elab A ∨ B ∨ C
-- app Or (app A ((app Or B) C)) 

#elab (A ∨ B) ∨ C
-- app ((app Or (app (app Or A) B))) C

-- Ensuring a given term have a given type
elab "assertType" termStx:term " : " typeStx:term : command =>
  open Lean Lean.Elab Command Term in
  liftTermElabM `bla
    try
      let tp ← elabType typeStx
      let tm ← elabTermEnsuringType termStx tp
      synthesizeSyntheticMVarsNoPostponing
      logInfo "success"
    catch | _ => throwError "failure"


assertType -4 : Int
assertType -4 : []

-- Building a simple DSL
-- inductive Arith : Type where
--   | add : Arith → Arith → Arith
--   | mul : Arith → Arith → Arith
--   | nat : Nat → Arith
--   | var : String → Arith

-- declare_syntax_cat arith
-- syntax num                  : arith
-- syntax str                  : arith
-- syntax arith " + " arith    : arith
-- syntax:75 arith " * " arith : arith
-- syntax " ( " arith " ) "    : arith


-- syntax " ⟪ " arith " ⟫ " : term

-- macro_rules
--   | `(⟪ $s:str ⟫)              => `(Arith.var $s)
--   | `(⟪ $num:num ⟫)            => `(Arith.var $num)
--   | `(⟪ $x:arith + $y:arith ⟫) => `(Arith.add ⟪$x⟫ ⟪$y⟫)
--   | `(⟪ $x:arith * $y:arith ⟫) => `(Arith.mul ⟪$x⟫ ⟪$y⟫)
--   | `(⟪ ($x) ⟫)                => `($x)

-- #check ⟪ "x" * "y" ⟫
-- #check ⟪ "x" + 23 ⟫


elab "traces" : tactic => do
  let array := List.replicate 2 (List.range 3)
  Lean.logInfo m!"logInfo: {array}"
  dbg_trace f!"dbg_trace: {array}"

example : True := by
  traces
  trivial

open Lean

def z := mkConst ``Nat.zero
def one := mkApp (mkConst ``Nat.succ) z

#eval one
#check one

def natExpr : Nat → Expr
| 0 => z
| n + 1 => mkApp (mkConst ``Nat.succ) (natExpr n)

#eval natExpr 4

def sumExpr : Nat → Nat → Expr
| n, m => mkAppN (mkConst ``Nat.add) #[natExpr n, natExpr m]

#check sumExpr

def constZero : Expr :=
  mkLambda `x BinderInfo.default (mkConst ``Nat) (mkConst ``Nat.zero)

#eval constZero


