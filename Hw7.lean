variable (α : Type)
variable (f : α → α) 
variable (A B C : α → Prop)
variable (D : Prop) 

theorem problem1 (h₁ : ∀ x, A x → B x) (h₂ : ∃ y, A y) : ∃ z, B z := sorry

theorem problem2 (h : ∃ x, A x) : ∃ y, A y ∨ B y := sorry 

theorem problem3 (h : ∀ x, A x → A (f x)) : ∀ y, A y → A (f (f y)) := sorry

theorem problem4 (h₁ : ∀ x, A x ∨ B x) (h₂ : ∀ x, A x → C x) (h₃ : ∀ x, B x → C x) : ∀ x, C x := sorry

theorem problem5 (a : α) : (∀ (x:α), D) ↔ D := sorry 
