import Mathlib.CategoryTheory.Comma.Over.Basic
-- import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Opposites

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (c : C)

/-- Exercise 1.2.i. Show that C/c ≅ (c/(Cᵒᵖ))ᵒᵖ. Defining C/c to be
    (c/(Cᵒᵖ))ᵒᵖ, deduce Exercise 1.1.iii(ii) from Exercise 1.1.iii(i).
    -/
def OverUnderOpEquiv : Over c ≌ (Under c.op)ᵒᵖ :=
  Comma.opEquiv (𝟙 C) (Functor.fromPUnit c)

-- Make sure that (c/(Cᵒᵖ))ᵒᵖ is a Category.
#synth Category ((Under (op c))ᵒᵖ)
