import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Core

open CategoryTheory

universe v₁ u₁

variable {T : Type u₁} [Category.{v₁} T]

/-- Exercise 1.1.iii. For any category C and any object c ∈ C,
    show that:

    (i) There is a category c/C whose objects are morphisms f: c → x
        with domain c and in which a morphism from f : c → x to
        g : c → y is a map h : x → y between the codomains so that
        the triangle

                                    c
                                f /   \ g
                                 v     v
                                x -----> y
                                    h

        **commutes**, i.e. so that g = h f.

    (ii) There is a category C/c whose objects are morphisms f: x → c
         with codomain c and in which a morphism from f : x → c to
         g : y → c is a map h : x → y between the domains so that
         the triangle

                                    h
                                x ----> y
                                 \     /
                                f \   / g
                                   v v
                                    c

        **commutes**, i.e. so that f = g h.

    The categories c/C and C/c are called **slice categories** of C
    **under** and **over** c, respectively.
-/

/-- "Slice categories of C under and over c" are called "Under" and
    "Over" in mathlib, and are defined in
    https://github.com/leanprover-community/mathlib4/ and the file
    Mathlib/CategoryTheory/Comma/Over/Basic.lean;
    All the commented-out code is taken from there.

```
def Under (X : T) :=
  StructuredArrow X (𝟭 T)

def Over (X : T) :=
  CostructuredArrow (𝟭 T) X
```
    -/
