import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Opposites

/-!
Exercise 1.2.iii from Emily Riehl, "Category Theory in Context"
-/

open CategoryTheory Opposite

universe v u

variable {C : Type u} [Category.{v} C]

/- -------------------------------------------------------------------------
   Part (i): Composition of monomorphisms is a monomorphism.
   ------------------------------------------------------------------------- -/
lemma mono_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] :
    Mono (f ≫ g) := by
  constructor
  intro W h₁ h₂ h
  -- h gives h₁ ≫ (f ≫ g) = h₂ ≫ (f ≫ g)
  -- Re-associate to (h₁ ≫ f) ≫ g = (h₂ ≫ f) ≫ g
  rw [← Category.assoc, ← Category.assoc] at h
  -- g is mono, so h₁ ≫ f = h₂ ≫ f
  have h' := Mono.right_cancellation _ _ h
  -- f is mono, so h₁ = h₂
  exact Mono.right_cancellation _ _ h'

/- -------------------------------------------------------------------------
   Part (ii): If g ∘ f is mono, then f is mono.
   ------------------------------------------------------------------------- -/
lemma mono_of_mono_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono (f ≫ g)] :
    Mono f := by
  constructor
  intro W h₁ h₂ h
  -- We have h₁ ≫ f = h₂ ≫ f; we want h₁ = h₂.
  -- Because f ≫ g is mono, it suffices to show h₁ ≫ (f ≫ g) = h₂ ≫ (f ≫ g).
  apply Mono.right_cancellation (f ≫ g) h₁ h₂
  -- This follows by associativity from our assumption.
  rw [Category.assoc, Category.assoc, h]

/- -------------------------------------------------------------------------
   By duality: (i′) and (ii′) follow from (i) and (ii) applied to Cᵒᵖ.
   
   In Mathlib the dictionary is:
     • f is epi in C  ↔  f.op is mono in Cᵒᵖ
     • (f ≫ g).op    =  g.op ≫ f.op
   ------------------------------------------------------------------------- -/
lemma epi_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] [Epi g] :
    Epi (f ≫ g) := by
  -- f ≫ g is epi in C  iff  (f ≫ g).op is mono in Cᵒᵖ
  rw [epi_iff_mono_op]
  -- Translate the composite into the opposite category
  rw [op_comp]
  -- g.op and f.op are mono in Cᵒᵖ because g and f are epi in C.
  -- Now apply (i) in Cᵒᵖ.
  apply mono_comp g.op f.op

lemma epi_of_epi_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ g)] :
    Epi g := by
  -- g is epi in C  iff  g.op is mono in Cᵒᵖ
  rw [epi_iff_mono_op]
  -- Rewrite the hypothesis in the opposite category
  rw [op_comp] at *
  -- Apply (ii) in Cᵒᵖ: if g.op ≫ f.op is mono, then g.op is mono.
  apply mono_of_mono_comp g.op f.op

/- -------------------------------------------------------------------------
   Conclusion: the monomorphisms form a wide subcategory.
   ------------------------------------------------------------------------- -/
def MonoCat (C : Type u) [Category.{v} C] := C

instance : Category (MonoCat C) where
  Hom X Y       := {f : X ⟶ Y // Mono f}
  id X          := ⟨𝟙 X, by infer_instance⟩
  comp f g      := ⟨f.val ≫ g.val, mono_comp f.val g.val⟩
  id_comp f     := by ext; simp
  comp_id f     := by ext; simp
  assoc f g h   := by ext; simp

/- -------------------------------------------------------------------------
   Dually, the epimorphisms form a wide subcategory.
   ------------------------------------------------------------------------- -/
def EpiCat (C : Type u) [Category.{v} C] := C

instance : Category (EpiCat C) where
  Hom X Y       := {f : X ⟶ Y // Epi f}
  id X          := ⟨𝟙 X, by infer_instance⟩
  comp f g      := ⟨f.val ≫ g.val, epi_comp f.val g.val⟩
  id_comp f     := by ext; simp
  comp_id f     := by ext; simp
  assoc f g h   := by ext; simp
