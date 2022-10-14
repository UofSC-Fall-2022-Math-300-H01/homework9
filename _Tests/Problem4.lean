import Hw7
import Lean.Elab.Print
import Lean.Elab.Command

theorem desiredType : ∀ (α : Type) (A B C : α → Prop),
  (∀ (x : α), A x ∨ B x) → (∀ (x : α), A x → C x) → (∀ (x : α), B x → C x) → ∀ (x : α), C x:= sorry 

open Lean
open Lean.Meta
open Lean.Elab.Command

def collectAxiomsOf (constName : Name) : MetaM (List String) := do
  let env ← getEnv
  let (_, s) := ((CollectAxioms.collect constName).run env).run {}
  let a := s.axioms.toList.map toString
  return a

#eval isDefEq (Expr.const ``desiredType []) (Expr.const ``problem4 [])
#eval collectAxiomsOf ``problem4
