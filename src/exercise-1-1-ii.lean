import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Core

open CategoryTheory

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

-- Exercise 1.1.ii. Let C be a category. Show that the collection of
-- isomorphisms in C defines a subcategory, the **maximal groupoid**
-- inside C.

-- "Maximal groupoid" is called "Core" in mathlib, and is defined in
-- https://github.com/leanprover-community/mathlib4/ and the file
-- Mathlib/CategoryTheory/Core.lean;
-- All the commented-out code is taken from there.
--
-- ```
-- structure Core (C : Type u₁) where
--   /-- The object of the base category underlying an object in `Core C`. -/
--   of : C

-- There are three things to prove here: subcategory, groupoid, and
-- maximal.

-- Subcategory:

-- ```
-- variable (C) in
-- /-- The core of a category is naturally included in the category. -/
-- @[simps!]
-- def inclusion : Core C ⥤ C where
--   obj := of
--   map f := f.iso.hom
-- ```
#check Core.inclusion C

-- Groupoid:

-- ```
-- @[simps!]
-- instance coreCategory : Groupoid.{v₁} (Core C) where
--   Hom (X Y : Core C) := CoreHom X Y
--   id (X : Core C) := .mk <| Iso.refl X.of
--   comp f g := .mk <| Iso.trans f.iso g.iso
--   inv {_ _} f := .mk <| Iso.symm f.iso
-- ```
#check (inferInstance : Groupoid (Core C))

-- Maximal:

-- ```
-- instance : (inclusion C).Faithful where
--     -- (intentionally left blank)
--
-- variable {C} {G : Type u₂} [Groupoid.{v₂} G]
--
-- -- Note that this function is not functorial
-- -- (consider the two functors from [0] to [1], and the natural transformation
-- -- between them).
--
-- /-- A functor from a groupoid to a category C factors through the core of C. -/
-- @[simps!]
-- def functorToCore (F : G ⥤ C) : G ⥤ Core C where
--   obj X := .mk <| F.obj X
--   map f := .mk <| { hom := F.map f, inv := F.map (Groupoid.inv f) }
-- ```
#check Core.functorToCore
