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
  constructor
  · -- (→) Assume f is a split epi; prove post-composition is surjective.
    intro hf c g
    use g ≫ section_ f
    dsimp [postcomp]
    rw [Category.assoc, IsSplitEpi.id f, Category.comp_id]
  · -- (←) Assume post-composition is surjective for all c; prove f is a split epi.
    intro hsurj
    have hY := hsurj Y
    obtain ⟨s, hs⟩ := hY (𝟙 Y)
    dsimp [postcomp] at hs
    exact IsSplitEpi.mk' ⟨s, hs⟩

end SplitEpiCharacterization

section SplitMonoCharacterization

theorem isSplitMono_iff_surjective_precomp :
    IsSplitMono f ↔ ∀ (c : C), Function.Surjective (precomp f c) := by
  -- Step 1: f is split mono in C iff f.op is split epi in Cᵒᵖ
  have h1 : IsSplitMono f ↔ IsSplitEpi f.op := by
    constructor
    · -- Forward: IsSplitMono f → IsSplitEpi f.op
      intro hf
      have hsm : SplitMono f := hf.exists_splitMono.some
      refine IsSplitEpi.mk' ⟨hsm.retraction.op, ?_⟩
      rw [← CategoryTheory.op_comp, hsm.id, CategoryTheory.op_id]
    · -- Backward: IsSplitEpi f.op → IsSplitMono f
      intro hf
      have hse : SplitEpi f.op := hf.exists_splitEpi.some
      refine IsSplitMono.mk' ⟨hse.section_.unop, ?_⟩
      rw [← CategoryTheory.unop_comp, hse.id, CategoryTheory.unop_id]
  rw [h1]

  -- Step 2: Apply part (i) to f.op in the opposite category
  have h2 := isSplitEpi_iff_surjective_postcomp (C := Cᵒᵖ) f.op
  rw [h2]

  -- Step 3: Show the two surjectivity conditions are equivalent
  constructor
  · -- Forward: ∀ c in Cᵒᵖ, postcomp surjective → ∀ c in C, precomp surjective
    intro h c g
    have h_surj := h (Opposite.op c) (Quiver.Hom.op g)
    obtain ⟨k', hk'⟩ := h_surj
    use Quiver.Hom.unop k'
    dsimp [precomp]
    rw [← CategoryTheory.unop_comp, hk', Quiver.Hom.unop_op]
  · -- Backward: ∀ c in C, precomp surjective → ∀ c in Cᵒᵖ, postcomp surjective
    intro h c g
    have h_surj := h (unop c) (Quiver.Hom.unop g)
    obtain ⟨k', hk'⟩ := h_surj
    use Quiver.Hom.op k'
    dsimp [postcomp]
    rw [← CategoryTheory.op_comp, hk', Quiver.Hom.op_unop]

end SplitMonoCharacterization
