import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Opposites

/-!
# Exercise 1.2.ii from Riehl's "Category Theory in Context"

(i) Show that a morphism f: x → y is a split epimorphism in a category C
    if and only if for all c ∈ C, post-composition f_* : C(c, x) → C(c, y)
    defines a surjective function.

(ii) Argue by duality that f is a split monomorphism if and only if for all
     c ∈ C, pre-composition f^* : C(y, c) → C(x, c) is a surjective function.
-/

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y)

section SplitEpiCharacterization

/-- Post-composition by f, i.e. f_* : C(c, X) → C(c, Y) sending g ↦ g ≫ f -/
def postcomp (c : C) : (c ⟶ X) → (c ⟶ Y) :=
  fun g => g ≫ f

/-- Pre-composition by f, i.e. f^* : C(Y, c) → C(X, c) sending g ↦ f ≫ g -/
def precomp (c : C) : (Y ⟶ c) → (X ⟶ c) :=
  fun g => f ≫ g

theorem isSplitEpi_iff_surjective_postcomp :
    IsSplitEpi f ↔ ∀ (c : C), Function.Surjective (postcomp f c) := by
  sorry

end SplitEpiCharacterization

section SplitMonoCharacterization

theorem isSplitMono_iff_surjective_precomp :
    IsSplitMono f ↔ ∀ (c : C), Function.Surjective (precomp f c) := by
  sorry

end SplitMonoCharacterization
