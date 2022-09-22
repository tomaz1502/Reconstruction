import Lean
/- import Meta.Boolean -/

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


def f : Bool → Nat := sorry
def g : Nat → Prop := sorry

#elab Prop

#elab @Function.comp Bool Nat Prop g f

variable (P Q : Prop)
#check Lean.Expr



def main : IO Unit :=
  IO.println s!"Hello, world!"
