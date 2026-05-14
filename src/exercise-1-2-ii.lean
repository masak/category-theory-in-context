import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Opposites

/-!
# Exercise 1.2.ii from Riehl's "Category Theory in Context"

(i) Show that a morphism f: x → y is a split epimorphism in a category C
    if and only if for all c ∈ C, post-composition f_* : C(c, x) → C(c, y)
    defines a surjective function.

(ii) Argue by duality that f is a split monomorphism if and only if for all c ∈ C,
     pre-composition f^* : C(y, c) → C(x, c) is a surjective function.
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

/-!
## Part (i): Split epimorphism ↔ post-composition is surjective

Mathematical proof:

(→) Assume f is a split epimorphism. Then there exists a section s : Y ⟶ X
    such that s ≫ f = 𝟙 Y. To show post-composition is surjective, let g : c ⟶ Y
    be arbitrary. We claim g ≫ s is a preimage of g:

        (g ≫ s) ≫ f = g ≫ (s ≫ f) = g ≫ 𝟙 Y = g

    So every g has a preimage, hence f_* is surjective.

(←) Assume f_* : C(c, X) → C(c, Y) is surjective for all c. Take c = Y.
    Then 𝟙 Y : Y ⟶ Y has a preimage s : Y ⟶ X, meaning s ≫ f = 𝟙 Y.
    Thus f is a split epimorphism.
-/

theorem isSplitEpi_iff_surjective_postcomp :
    IsSplitEpi f ↔ ∀ (c : C), Function.Surjective (postcomp f c) := by
  constructor
  · -- Forward: split epi → post-composition surjective
    intro hf c
    -- The section s : Y ⟶ X satisfies s ≫ f = 𝟙 Y
    have hsec : section_ f ≫ f = 𝟙 Y := IsSplitEpi.id f
    -- To prove surjectivity, we must show every g : c ⟶ Y has a preimage
    intro g
    -- The preimage is g ≫ section_ f
    use g ≫ section_ f
    -- Verify: (g ≫ section_ f) ≫ f = g
    dsimp [postcomp]
    rw [Category.assoc, hsec, Category.comp_id]
  · -- Backward: post-composition surjective → split epi
    intro hsurj
    -- Instantiate the surjectivity condition at c = Y
    have hY := hsurj Y
    -- The identity 𝟙 Y has a preimage s : Y ⟶ X
    obtain ⟨s, hs⟩ := hY (𝟙 Y)
    -- This means s ≫ f = 𝟙 Y
    dsimp [postcomp] at hs
    -- Construct the SplitEpi structure from s
    exact IsSplitEpi.mk' ⟨s, hs⟩

end SplitEpiCharacterization

section SplitMonoCharacterization

/-!
## Part (ii): Split monomorphism ↔ pre-composition is surjective

We argue by duality. The slogan is: "Turn the arrows around."

In the opposite category Cᵒᵖ:
  • Objects are the same as in C
  • Morphisms are reversed: a morphism X ⟶ Y in Cᵒᵖ is a morphism Y ⟶ X in C
  • Composition is reversed: g ≫_op h in Cᵒᵖ equals h ≫ g in C

Key observations:
  1. f : X ⟶ Y is a split mono in C  ⟺  f.op : Y ⟶ X is a split epi in Cᵒᵖ
     (If f ≫ r = 𝟙 X in C, then r.op ≫_op f.op = (f ≫ r).op = (𝟙 X).op = 𝟙 X in Cᵒᵖ.)

  2. Pre-composition by f in C corresponds to post-composition by f.op in Cᵒᵖ:
     For g : Y ⟶ c in C (which is g.op : c ⟶ Y in Cᵒᵖ):
     • Pre-composition by f:   f ≫ g  : X ⟶ c  in C
     • Post-composition by f.op: g.op ≫_op f.op = (f ≫ g).op  in Cᵒᵖ

     So surjectivity of pre-composition by f in C is equivalent to surjectivity
     of post-composition by f.op in Cᵒᵖ.

So by part (i) applied to f.op in Cᵒᵖ:
    f.op is a split epi in Cᵒᵖ
    ⟺ post-composition by f.op is surjective in Cᵒᵖ
    ⟺ pre-composition by f is surjective in C

And f.op is a split epi in Cᵒᵖ ⟺ f is a split mono in C.
-/

theorem isSplitMono_iff_surjective_precomp :
    IsSplitMono f ↔ ∀ (c : C), Function.Surjective (precomp f c) := by
  -- Step 1: f is split mono in C iff f.op is split epi in Cᵒᵖ
  have h1 : IsSplitMono f ↔ IsSplitEpi f.op := by
    constructor
    · -- Forward: IsSplitMono f → IsSplitEpi f.op
      -- mathlib provides this instance automatically
      intro hf
      infer_instance
    · -- Backward: IsSplitEpi f.op → IsSplitMono f
      -- mathlib does NOT provide this as a direct instance (would need Cᵒᵖᵒᵖ equivalence)
      -- So we construct it manually by unpacking the SplitEpi structure
      intro hf
      -- Extract the SplitEpi structure for f.op in Cᵒᵖ
      have hse : SplitEpi f.op := hf.exists_splitEpi.some
      -- The section of f.op is a morphism s : Opposite.op X ⟶ Opposite.op Y in Cᵒᵖ
      -- Taking unop gives s.unop : Y ⟶ X in C, which will be our retraction
      let r := hse.section_.unop
      -- We need to show f ≫ r = 𝟙 X
      have hr : f ≫ r = 𝟙 X := by
        have h_id : hse.section_ ≫ f.op = 𝟙 (Opposite.op X) := hse.id
        have h_unop_comp : (hse.section_ ≫ f.op).unop = (f.op).unop ≫ hse.section_.unop := by
          simp [CategoryTheory.unop_comp]
        have h_unop_op : (f.op).unop = f := by
          simp [Quiver.Hom.unop_op]
        calc
          f ≫ r = (f.op).unop ≫ hse.section_.unop := by rw [show r = hse.section_.unop by rfl, h_unop_op]
          _ = (hse.section_ ≫ f.op).unop           := by rw [h_unop_comp]
          _ = (𝟙 (Opposite.op X)).unop              := by rw [h_id]
          _ = 𝟙 X                                   := by simp [CategoryTheory.unop_id]
      exact ⟨Nonempty.intro ⟨r, hr⟩⟩
  rw [h1]

  -- Step 2: Apply part (i) to f.op in the opposite category
  have h2 := isSplitEpi_iff_surjective_postcomp (C := Cᵒᵖ) f.op
  rw [h2]

  -- Step 3: Show the two surjectivity conditions are equivalent
  apply forall_congr'
  intro c
  dsimp [postcomp, precomp]

  -- The correspondence: a morphism g : c ⟶ Y in Cᵒᵖ is g.op : Y ⟶ c in C,
  -- and post-composition by f.op corresponds to pre-composition by f.
  constructor
  · -- Assume post-composition by f.op is surjective in Cᵒᵖ
    intro h g
    -- g : X ⟶ c in C, so g.op : Opposite.op c ⟶ Opposite.op X in Cᵒᵖ
    have h_surj := h (Quiver.Hom.op g)
    obtain ⟨k, hk⟩ := h_surj
    -- k : Opposite.op c ⟶ Opposite.op Y in Cᵒᵖ, so k.unop : Y ⟶ c in C
    use Quiver.Hom.unop k
    -- We need to show f ≫ k.unop = g in C
    -- We know k ≫ f.op = g.op in Cᵒᵖ
    -- Taking unop of both sides: (k ≫ f.op).unop = (g.op).unop = g
    have h_unop : Quiver.Hom.unop (k ≫ f.op) = g := by
      rw [hk]
      simp  -- simplifies (g.op).unop to g using Quiver.Hom.unop_op
    -- But (k ≫ f.op).unop = f ≫ k.unop by the definition of opposite composition
    have h_comp : Quiver.Hom.unop (k ≫ f.op) = f ≫ Quiver.Hom.unop k := by
      simp  -- uses CategoryTheory.unop_comp
    rw [h_comp] at h_unop
    exact h_unop
  · -- Assume pre-composition by f is surjective in C
    intro h g
    -- g : Opposite.op c ⟶ Opposite.op X in Cᵒᵖ, so g.unop : X ⟶ c in C
    have h_surj := h (Quiver.Hom.unop g)
    obtain ⟨k, hk⟩ := h_surj
    -- k : Y ⟶ c in C, so k.op : Opposite.op c ⟶ Opposite.op Y in Cᵒᵖ
    use Quiver.Hom.op k
    -- We need to show k.op ≫ f.op = g in Cᵒᵖ
    -- We know f ≫ k = g.unop in C
    -- Taking op of both sides: (f ≫ k).op = (g.unop).op = g
    have h_op : Quiver.Hom.op (f ≫ k) = g := by
      rw [hk]
      simp  -- simplifies (g.unop).op to g using Quiver.Hom.op_unop
    -- But (f ≫ k).op = k.op ≫ f.op by the definition of opposite composition
    have h_comp : Quiver.Hom.op (f ≫ k) = Quiver.Hom.op k ≫ f.op := by
      simp  -- uses CategoryTheory.op_comp
    rw [h_comp] at h_op
    exact h_op

end SplitMonoCharacterization
