/-
Copyright (c) 2025 [Your Name]. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import CartesianFibrations.CartesianArrows
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Cartesian Fibrations

This file formalizes the notion of cartesian fibrations between categories, following
Definition 5.2.1 from Elements of ∞-Category Theory by Emily Riehl and Dominic Verity.

## Main Definitions

* `IsCartesianFibration p`: A functor `p : E ⥤ B` is a cartesian fibration if it admits
  cartesian lifts for all arrows.
* `CartesianFibration E B`: The type of cartesian fibrations from E to B.

## Implementation Notes

This is a simplified version using ordinary category theory that compiles with Mathlib only.
The full ∞-categorical version will integrate with the ∞-cosmos project.

## References

* [Riehl & Verity, Elements of ∞-Category Theory][elements]

## Tags

infinity categories, fibrations, cartesian fibrations
-/

namespace CategoryTheory

universe u v

open Category Limits

/-- A functor `p : E ⥤ B` is a cartesian fibration if for every object `e : E` and
every morphism `f : b ⟶ p(e)` in B, there exists a cartesian lift of `f`.

A cartesian lift of `f : b → p(e)` is an arrow `lift : e' → e` such that:
- `p(e') = b`
- `p(lift) = f` (after transporting via the equality `p(e') = b`)
- `lift` is cartesian over `p`

This is Definition 5.2.1 from Elements. -/
def IsCartesianFibration {E B : Type u} [Category.{v} E] [Category.{v} B]
    (p : E ⥤ B) : Prop :=
  ∀ (e : E) (b : B) (f : b ⟶ p.obj e),
    ∃ (e' : E) (lift : e' ⟶ e) (he' : p.obj e' = b),
      p.map lift = eqToHom he' ≫ f ∧ IsCartesianArrow p lift

/-- The type of cartesian fibrations from E to B. -/
structure CartesianFibration (E B : Type u) [Category.{v} E] [Category.{v} B] where
  functor : E ⥤ B
  is_cartesian_fibration : IsCartesianFibration functor

namespace CartesianFibration

variable {E B : Type u} [Category.{v} E] [Category.{v} B]

/-- Extract the underlying functor from a cartesian fibration. -/
instance : Coe (CartesianFibration E B) (E ⥤ B) := ⟨fun p => p.functor⟩

/-- The identity functor is a cartesian fibration. -/
def id : CartesianFibration E E where
  functor := Functor.id E
  is_cartesian_fibration := by
    intro e b f
    -- For the identity functor, Functor.id.obj e = e, so f : b ⟶ e
    -- We can use b as the domain of the cartesian lift, with f itself as the lift
    use b, f, rfl
    constructor
    · -- Prove Functor.id.map f = eqToHom rfl ≫ f
      simp only [Functor.id_map, eqToHom_refl, Category.id_comp]
    · -- Prove f is a cartesian arrow over Functor.id
      intro x h g hcomm
      -- We have h : x → e, g : x → b (since Functor.id.obj x = x)
      -- Condition: Functor.id.map h = g ≫ Functor.id.map f, i.e., h = g ≫ f
      -- We need φ : x → b such that φ ≫ f = h and Functor.id.map φ = g
      -- Clearly φ = g works
      use g
      constructor
      · constructor
        · -- Prove g ≫ f = h
          simp only [Functor.id_obj, Functor.id_map] at hcomm
          exact hcomm.symm
        · -- Prove Functor.id.map g = g
          simp only [Functor.id_map]
      · -- Prove uniqueness
        intro φ ⟨hφ_comp, hφ_map⟩
        -- From hφ_map: Functor.id.map φ = g, i.e., φ = g
        simp only [Functor.id_map] at hφ_map
        exact hφ_map

end CartesianFibration

end CategoryTheory
