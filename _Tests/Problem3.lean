import Hw7
import Lean.Elab.Print
import Lean.Elab.Command

theorem desiredType : ∀ (α : Type) (f : α → α) (A : α → Prop), (∀ (x : α), A x → A (f x)) → ∀ (y : α), A y → A (f (f y)) := sorry 

open Lean
open Lean.Meta
open Lean.Elab.Command

def collectAxiomsOf (constName : Name) : MetaM (List String) := do
  let env ← getEnv
  let (_, s) := ((CollectAxioms.collect constName).run env).run {}
  let a := s.axioms.toList.map toString
  return a

#eval isDefEq (Expr.const ``desiredType []) (Expr.const ``problem3 [])
#eval collectAxiomsOf ``problem3
