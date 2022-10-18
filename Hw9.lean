import Sets.Basic

open Set

variable (α β : Type)
variable (X Y Z : Set α)
variable (W : Set β) 


theorem problem1 : ∅ ∈ 𝒫  X := sorry 

theorem problem2 (U : β → Set α) : ∀ b, U b ⊆ BigUnion U := sorry 

theorem problem3 (h : X ⊆ Y) : (X ×ˢ W) ⊆ (Y ×ˢ W) := sorry

theorem problem4 (h : Y ∩ Z = ∅) : Yᶜ ∪ Zᶜ = Univ := sorry 

theorem problem5 : (X \ Y) ∪ (Y \ X) = (X ∪ Y) \ (X ∩ Y) := sorry 
