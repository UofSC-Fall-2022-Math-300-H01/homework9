import Hw7
import Lean.Elab.Print
import Lean.Elab.Command

theorem desiredType : ∀ (α : Type) (A B : α → Prop), (∃ x, A x) → ∃ y, A y ∨ B y := sorry 

open Lean
open Lean.Meta
open Lean.Elab.Command

def collectAxiomsOf (constName : Name) : MetaM (List String) := do
  let env ← getEnv
  let (_, s) := ((CollectAxioms.collect constName).run env).run {}
  let a := s.axioms.toList.map toString
  return a

#eval isDefEq (Expr.const ``desiredType []) (Expr.const ``problem2 [])
#eval collectAxiomsOf ``problem2
