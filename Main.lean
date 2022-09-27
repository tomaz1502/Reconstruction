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

def main : IO Unit :=
  IO.println s!"Hello, world!"

