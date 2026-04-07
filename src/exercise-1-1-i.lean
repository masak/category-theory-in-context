import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- A morphism has at most one two-sided inverse.
    If g and h are both left and right inverses of f, then g = h. -/
theorem iso_inv_unique {X Y : C} {f : X → Y} {g h : Y → X}
    (hf : h ≫ f = 𝟙 Y) (fg : f ≫ g = 𝟙 X)
    g = h := by
  calc
    g = 𝟙 Y ≫ g       := by simp
    _ = (h ≫ f) ≫ g   := by rw [hf]
    _ = h ≫ (f ≫ g)   := by simp
    _ = h ≫ 𝟙 X       := by rw [fg]
    _ = h

/-- If f has a left inverse g and a right inverse h,
    then f is an isomorphism. -/
theorem section_retraction_isIso {X Y : C} {f : X ⟶ Y} {g h : Y ⟶ X}
    (fg : f ≫ g = 𝟙 X) (hf : h ≫ f = 𝟙 Y) :
    IsIso f := by
  have gh : g = h := iso_inv_unique hf fg
  exact ⟨g, fg, by rw [gh]; exact hf⟩
