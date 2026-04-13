import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Core

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- Exercise 1.1.ii. Let C be a category. Show that the collection of
    isomorphisms in C defines a subcategory, the **maximal groupoid**
    inside C. --/
theorem core_is_subcategory : (Core.inclusion C).Faithful := by
  sorry

theorem core_is_groupoid : Groupoid.{v} (Core C) := by
  sorry

theorem core_is_maximal {G : Type u} [Groupoid.{v} G] (F : G ⥤ C) :
    ∃ (F' : G ⥤ Core C), F' ⋙ Core.inclusion C = F := by
  sorry
