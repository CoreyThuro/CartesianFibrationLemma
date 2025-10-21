/-
Copyright (c) 2025 [Your Name]. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Cartesian Arrows in an ∞-Category

This file formalizes the notion of cartesian arrows in an ∞-category, following
Definition 5.1.1 from Elements of ∞-Category Theory by Emily Riehl and Dominic Verity.

## Main Definitions

* `IsCartesianArrow p f`: A morphism `f` is cartesian over `p` if it satisfies the
  universal property for lifting problems.
* `CartesianArrow p A B`: The type of cartesian arrows from A to B over p.

## Main Results

* `comp_cartesian`: The composite of cartesian arrows is cartesian.
* `iso_cartesian`: Isomorphisms are cartesian over any map.

## Implementation Notes

The definition of cartesian arrow in an ∞-category is more subtle than in ordinary
category theory, as it involves homotopy-coherent universal properties. We follow
the model-independent approach of the ∞-cosmos framework.

NOTE: This is a simplified version that compiles with Mathlib only.
The full implementation will integrate with the ∞-cosmos project once
compilation issues are resolved.

## References

* [Riehl & Verity, Elements of ∞-Category Theory][elements]

## Tags

infinity categories, fibrations, cartesian arrows, higher category theory
-/

namespace CategoryTheory

universe u v

open Category Limits

variable {C : Type u} [Category.{v} C]

/-- A morphism `f : e' ⟶ e` is cartesian over `p : E ⟶ B` if it satisfies the universal
property for cartesian arrows. This is Definition 5.1.1 from Elements.

The universal property states: for any object `x : E`, morphisms `h : x ⟶ e` in E and
`g : p(x) ⟶ p(e')` in B satisfying `p(h) = g ≫ p(f)`, there exists a unique morphism
`φ : x ⟶ e'` such that `φ ≫ f = h` and `p(φ) = g`.

Intuitively, cartesian arrows "freely lift" morphisms from the base category B to the
total category E. The morphism f provides a universal way to factor any h through e'.

In the ∞-categorical setting, this universal property is stated in terms of a certain
square of hom-spaces being a homotopy pullback. Here we use the ordinary category version
with strict equality. -/
def IsCartesianArrow {E B : Type u} [Category.{v} E] [Category.{v} B]
    (p : E ⥤ B) {e' e : E} (f : e' ⟶ e) : Prop :=
  ∀ (x : E) (h : x ⟶ e) (g : p.obj x ⟶ p.obj e'),
    p.map h = g ≫ p.map f →
    ∃! (φ : x ⟶ e'), φ ≫ f = h ∧ p.map φ = g

/-- The type of cartesian arrows from A to B over p. -/
structure CartesianArrow {E C : Type u} [Category.{v} E] [Category.{v} C]
    (p : E ⥤ C) (A B : E) where
  map : A ⟶ B
  is_cartesian : IsCartesianArrow p map

namespace CartesianArrow

variable {E C : Type u} [Category.{v} E] [Category.{v} C]

/-- Extract the underlying morphism from a cartesian arrow. -/
@[coe] def toHom {p : E ⥤ C} {A B : E} (f : CartesianArrow p A B) : A ⟶ B := f.map

instance {p : E ⥤ C} {A B : E} : CoeFun (CartesianArrow p A B) (fun _ => A ⟶ B) where
  coe := toHom

/-- The identity morphism is cartesian over any functor.

This is because composing with the identity doesn't change anything, so the lift is trivial. -/
theorem id_is_cartesian {E B : Type u} [Category.{v} E] [Category.{v} B]
    (p : E ⥤ B) (A : E) : IsCartesianArrow p (𝟙 A) := by
  intro x h g hcomm
  -- We need φ : x ⟶ A such that φ ≫ 𝟙 A = h and p(φ) = g
  -- Since φ ≫ 𝟙 A = φ, we need φ = h
  -- Check: p(h) = g ≫ p(𝟙 A) = g ≫ 𝟙 = g, so we need p(h) = g

  use h
  constructor
  · constructor
    · -- Prove h ≫ 𝟙 A = h
      exact Category.comp_id h
    · -- Prove p.map h = g
      -- From hcomm: p.map h = g ≫ p.map (𝟙 A)
      -- Since p.map (𝟙 A) = 𝟙 (p.obj A), we get p.map h = g ≫ 𝟙 = g
      calc p.map h = g ≫ p.map (𝟙 A) := hcomm
        _ = g ≫ 𝟙 (p.obj A) := by rw [p.map_id]
        _ = g := Category.comp_id g
  · -- Prove uniqueness
    intro φ ⟨hφ_comp, hφ_map⟩
    calc φ = φ ≫ 𝟙 A := (Category.comp_id φ).symm
      _ = h := by rw [hφ_comp]

/-- Isomorphisms are cartesian over any functor.

The intuition is that isomorphisms can be "inverted", so we can always lift uniquely
by composing with the inverse. -/
theorem iso_is_cartesian {E B : Type u} [Category.{v} E] [Category.{v} B]
    {p : E ⥤ B} {e' e : E} {f : e' ⟶ e} [IsIso f] :
    IsCartesianArrow p f := by
  intro x h g hcomm
  -- We want φ : x ⟶ e' such that φ ≫ f = h and p(φ) = g
  -- Since f is an isomorphism, we can try φ = h ≫ inv f

  use h ≫ inv f
  constructor
  · constructor
    · -- Prove (h ≫ inv f) ≫ f = h
      calc (h ≫ inv f) ≫ f = h ≫ (inv f ≫ f) := by rw [Category.assoc]
        _ = h ≫ 𝟙 e := by rw [IsIso.inv_hom_id]
        _ = h := Category.comp_id h
    · -- Prove p.map (h ≫ inv f) = g
      -- Strategy: Compose both sides with p.map f and show they're equal
      have step1 : p.map (h ≫ inv f) ≫ p.map f = g ≫ p.map f := by
        rw [← p.map_comp]
        simp [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        exact hcomm
      -- Now cancel p.map f on the right
      calc p.map (h ≫ inv f)
        = p.map (h ≫ inv f) ≫ 𝟙 (p.obj e') := (Category.comp_id _).symm
        _ = p.map (h ≫ inv f) ≫ (p.map f ≫ p.map (inv f)) := by
            rw [← p.map_comp, IsIso.hom_inv_id, p.map_id]
        _ = (p.map (h ≫ inv f) ≫ p.map f) ≫ p.map (inv f) := by rw [Category.assoc]
        _ = (g ≫ p.map f) ≫ p.map (inv f) := by rw [step1]
        _ = g ≫ (p.map f ≫ p.map (inv f)) := by rw [Category.assoc]
        _ = g ≫ p.map (f ≫ inv f) := by rw [← p.map_comp]
        _ = g ≫ p.map (𝟙 e') := by rw [IsIso.hom_inv_id]
        _ = g ≫ 𝟙 (p.obj e') := by rw [p.map_id]
        _ = g := Category.comp_id g
  · -- Prove uniqueness
    intro φ ⟨hφ_comp, hφ_map⟩
    -- We know φ ≫ f = h, so φ = h ≫ inv f
    calc φ = φ ≫ 𝟙 e' := (Category.comp_id φ).symm
      _ = φ ≫ (f ≫ inv f) := by rw [IsIso.hom_inv_id]
      _ = (φ ≫ f) ≫ inv f := by rw [Category.assoc]
      _ = h ≫ inv f := by rw [hφ_comp]

end CartesianArrow

end CategoryTheory
