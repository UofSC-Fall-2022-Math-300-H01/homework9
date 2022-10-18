import Hw9
import Sets.Basic
import Lean.Elab.Print
import Lean.Elab.Command

open Set 

variable (α β : Type)
variable (X Y Z : Set α)
variable (W : Set β) 

theorem desiredType1 : ∅ ∈ 𝒫  X := sorry 

theorem desiredType2 (U : β → Set α) : ∀ b, U b ⊆ BigUnion U := sorry 

theorem desiredType3 (h : X ⊆ Y) : (X ×ˢ W) ⊆ (Y ×ˢ W) := sorry

theorem desiredType4 (h : Y ∩ Z = ∅) : Yᶜ ∪ Zᶜ = Univ := sorry 

theorem desiredType5 : (X \ Y) ∪ (Y \ X) = (X ∪ Y) \ (X ∩ Y) := sorry 

open Lean
open Lean.Meta
open Lean.Elab.Command

def n : String := "4"

def problem : String := "problem"++n

def desired : String := "desiredType"++n

def collectAxiomsOf (constName : Name) : MetaM (List String) := do
  let env ← getEnv
  let (_, s) := ((CollectAxioms.collect constName).run env).run {}
  let a := s.axioms.toList.map toString
  return a

#eval isDefEq (Expr.const desired []) (Expr.const problem [])
#eval collectAxiomsOf problem
