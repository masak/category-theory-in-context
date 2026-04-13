import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- Exercise 1.1.i
    (i) Show that a morphism can have at most one inverse isomorphism. --/
theorem iso_inv_unique {X Y : C} {f : X → Y} {g h : Y → X}
    (fg : f ≫ g = 𝟙 X) (hf : h ≫ f = 𝟙 Y) :
    g = h := by
  calc
    g = 𝟙 Y ≫ g       := by simp
    _ = (h ≫ f) ≫ g   := by rw [hf]
    _ = h ≫ (f ≫ g)   := by simp
    _ = h ≫ 𝟙 X       := by rw [fg]
    _ = h

/-- (ii) Consider a morphism f : x ⟶ y. Show that if there exists a
    pair of morphisms g, h: y ⟶ x so that g f = 1_x and f h = 1_y,
    then g = h and f is an isomorphism. -/
theorem section_retraction_isIso {X Y : C} {f : X ⟶ Y} {g h : Y ⟶ X}
    (fg : f ≫ g = 𝟙 X) (hf : h ≫ f = 𝟙 Y) :
    IsIso f := by
  have gh : g = h := iso_inv_unique fg hf
  have gf : g ≫ f = 𝟙 Y := by 
    rw [gh]
    exact hf
  exact ⟨g, fg, gf⟩
