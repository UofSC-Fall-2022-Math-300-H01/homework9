namespace Set

def Set (α : Type) := α → Prop 

def Mem {α : Type} : α → Set α → Prop := fun a X => X a 

instance {α : Type} : Membership α (Set α) where
  mem := Mem 

def SetOf {α : Type} (p : α → Prop) : Set α := p

declare_syntax_cat binder_construct
syntax "{" binder_construct "|" term "}" : term

syntax ident " : " term : binder_construct
syntax ident " ∈ " term : binder_construct

macro_rules
| `({ $var:ident : $ty:term | $body:term }) => `(SetOf (fun ($var : $ty) => $body)) 
| `({ $var:ident ∈ $s:term | $body:term }) => `(SetOf (fun $var => $var ∈ $s ∧ $body))

def Insert {α : Type} (a' : α) (X : Set α) : Set α := fun a => a = a' ∨ a ∈ X

def Subset {α : Type} (X Y : Set α) : Prop := ∀ a, a ∈ X → a ∈ Y
infix:60 " ⊆ " => Subset

def Univ { α : Type } : Set α := fun _ => True 

def Emptyset { α : Type } : Set α := fun _ => False  

instance {α : Type} : EmptyCollection (Set α) where 
  emptyCollection := Emptyset

def Singleton {α : Type} (a : α) : Set α := Insert a ∅ 

def Union {α : Type} (X Y : Set α) : Set α := fun a => a ∈ X ∨ a ∈ Y 
infixl:65 " ∪ " => Union

def Inter {α : Type} (X Y : Set α) : Set α := fun a => a ∈ X ∧ a ∈ Y
infixl:65 " ∩ " => Inter 

def Diff {α : Type} (X Y : Set α) : Set α := fun a => a ∈ X ∧ a ∉ Y 
infixl:65 " \\ " => Diff 

def Comp {α : Type} (X : Set α) : Set α := fun x => x ∉ X 
postfix:100 "ᶜ " => Comp

def BigUnion {α β : Type} (X : β → Set α) : Set α := fun a => ∃ b, a ∈ X b 

def BigInter {α β : Type} (X : β → Set α) : Set α := fun a => ∀ b, a ∈ X b 

declare_syntax_cat big_operators
syntax "∪ " big_operators "," term : term
syntax "∩ " big_operators "," term : term

syntax ident " : " term : big_operators 

macro_rules
| `(∪ $var:ident : $ty:term , $body:term $var:ident ) => `(@BigUnion _ $ty $body) 
| `(∩ $var:ident : $ty:term , $body:term $var:ident ) => `(@BigInter _ $ty $body)

def PowerSet {α : Type} (X : Set α) : Set (Set α) := fun Y => Y ⊆ X
prefix:100 "𝒫" => PowerSet

def Prod {α β : Type} (X : Set α) (Y : Set β) : Set (α × β) := fun x => x.1 ∈ X ∧ x.2 ∈ Y
infixl:75 " ×ˢ " => Prod 

variable {α β : Type} 
variable {a₁ a₂ : α}
variable {X Y Z: Set α} 
variable {U : β → Set α} 

#check ∪ b:β, U b  
#check ∩ b:β, U x

theorem sub_refl : X ⊆ X := fun _ h => h  

theorem sub_trans (h₁ : X ⊆ Y) (h₂ : Y ⊆ Z) : X ⊆ Z := fun x h => h₂ x (h₁ x h) 

theorem sub_of_eq (h : X = Y) : X ⊆ Y := by 
  rw [←h]
  exact fun _ h => h 

theorem set_ext : X = Y ↔ (∀ (x:α), x ∈ X ↔ x ∈ Y) := by 
  apply Iff.intro 
  · intro h x 
    apply Iff.intro 
    · exact sub_of_eq h x 
    · rw [h]
      exact fun h => h 
  · intro h 
    apply funext 
    intro x 
    exact propext (h x) 

syntax (name := set_extensionality) "set_extensionality" ident : tactic
macro_rules
| `(tactic| set_extensionality $e:ident ) => 
    `(tactic| apply set_ext.mpr ; intro $e:ident ; constructor ) 

syntax (name := assume) "assume" "("ident":" term")": tactic
macro_rules
| `(tactic| assume ($e:ident:$ty:term)) => `(tactic| intro ($e:ident:$ty:term) ) 

-- syntax "set_extensionality" : tactic
-- macro_rules
-- | `(tactic| set_extensionality ) => `(tactic| apply set_ext.mpr) -- <;> intro h $(x?)? <;> constructor ) 

theorem sub_left_of_union : X ⊆ X ∪ Y := by 
  assume (x:α) 
  assume (h:x ∈ X) 
  exact Or.inl h 

theorem sub_right_of_union : Y ⊆ X ∪ Y := by 
  intro x h 
  exact Or.inr h 

theorem inter_sub_left : X ∩ Y ⊆ X := by 
  intro a h
  exact And.left h 

theorem inter_sub_right : X ∩ Y ⊆ Y := by 
  intro a h
  exact And.right h 

theorem diff_sub : X \ Y ⊆ X := fun _ h => And.left h 

theorem comm_union : X ∪ Y = Y ∪ X := by 
  apply set_ext.mpr 
  intro x 
  constructor 
  · intro h 
    cases h with 
    | inl g => exact sub_right_of_union x g 
    | inr g => exact sub_left_of_union x g 
  · intro h 
    cases h with 
    | inl g => exact sub_right_of_union x g 
    | inr g => exact sub_left_of_union x g 

theorem comm_inter : X ∩ Y = Y ∩ X := by 
  apply set_ext.mpr 
  intro x 
  constructor 
  repeat {exact fun h => ⟨h.right,h.left⟩}

theorem diff_union_eq : X \ Y ∪ (X ∩ Y) = X := by 
  apply set_ext.mpr 
  intro x 
  constructor 
  · intro h 
    apply Or.elim h 
    repeat {exact fun g => And.left g}
  · intro h 
    have g : x ∈ Y ∨ x ∉ Y := Classical.em (x ∈ Y) 
    cases g with 
    | inl g₁ => exact Or.inr ⟨h,g₁⟩ 
    | inr g₁ => exact Or.inl ⟨h,g₁⟩ 

theorem comp_comp_eq : (Xᶜ)ᶜ = X := by
  set_extensionality x
  · intro h 
    apply Classical.byContradiction
    exact fun n => h n 
  · exact fun h v => v h
  
theorem comp_eq_univ_diff : Xᶜ = Univ \ X := by 
  set_extensionality x 
  · exact fun h => ⟨trivial,h⟩ 
  · exact fun h => h.right 

theorem union_assoc : X ∪ Y ∪ Z = X ∪ (Y ∪ Z) := by 
  set_extensionality x
  · intro h 
    cases h with 
    | inl g₁ => cases g₁ with
      | inl g₂ => exact Or.inl g₂ 
      | inr g₂ => exact Or.inr <| Or.inl g₂ 
    | inr g₁ => exact Or.inr <| Or.inr g₁
  · intro h 
    cases h with 
    | inl g₁ => exact Or.inl <| Or.inl g₁ 
    | inr g₁ => cases g₁ with 
      | inl g₂ => exact Or.inl <| Or.inr g₂ 
      | inr g₂ => exact Or.inr g₂ 

theorem empty_union_eq : ∅ ∪ X = X := by 
  set_extensionality x
  · intro h 
    cases h with 
    | inl g => exact False.elim g 
    | inr g => assumption 
  · intro h 
    exact .inr h 

theorem empty_inter_empty : ∅ ∩ X = ∅ := by 
  set_extensionality x 
  · exact fun h => False.elim h.left 
  · exact fun h => False.elim h 

theorem not_mem_empty (x : α) : x ∉ Emptyset := fun h => h 

theorem diff_empty_eq : X \ ∅ = X := by 
  set_extensionality x 
  · exact fun h => And.left h 
  · exact fun h => ⟨h,not_mem_empty x⟩  

theorem univ_union_univ : Univ ∪ X = Univ := by 
  set_extensionality x
  · exact fun _ => trivial  
  · exact sub_left_of_union _ 

theorem dist_inter_union : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := by
  set_extensionality x 
  · intro h  
    cases h.right with 
    | inl g₃ => exact Or.inl ⟨h.left,g₃⟩  
    | inr g₃ => exact Or.inr ⟨h.left,g₃⟩  
  · intro h 
    cases h with 
    | inl g => exact ⟨g.left,Or.inl g.right⟩ 
    | inr g => exact ⟨g.left,Or.inr g.right⟩ 

theorem dist_union_inter : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := by 
  set_extensionality x 
  · intro h 
    cases h with 
    | inl g => exact ⟨ Or.inl g, Or.inl g⟩ 
    | inr g => exact ⟨ Or.inr g.left, Or.inr g.right ⟩ 
  · intro h 
    have ⟨l,r⟩ := h 
    cases l with 
    | inl g₁ => exact Or.inl g₁ 
    | inr g₁ => cases r with 
      | inl g₂ => exact Or.inl g₂ 
      | inr g₂ => exact Or.inr ⟨g₁,g₂⟩ 

theorem eq_empty_not_in (h : X = ∅) (x:α) : x ∉ X :=  (set_ext.mp h x).mp 

theorem mem_singleton (x : α) : x ∈ Singleton x := by 
  apply Or.inl 
  rfl 

theorem singleton_elim {x y : α} (h : y ∈ Singleton x) : x = y := by 
  cases h with 
  | inl g => exact Eq.symm g  
  | inr g => exact False.elim g 

theorem mem_iff_singleton_sub (x : α) : x ∈ X ↔ Singleton x ⊆ X := by
  constructor 
  · intro h y g 
    have e : x = y := singleton_elim g 
    rw [←e] 
    exact h 
  · intro h 
    exact h x (mem_singleton x) 

theorem mem_iff_singleton_mem_powerset (x : α) : x ∈ X ↔ Singleton x ∈ 𝒫 X := mem_iff_singleton_sub x 

end Set 
