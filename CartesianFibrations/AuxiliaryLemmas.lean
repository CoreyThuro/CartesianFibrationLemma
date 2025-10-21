/-
Copyright (c) 2025 [Your Name]. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import CartesianFibrations.CartesianFibrations

/-!
# Auxiliary Lemmas for Cartesian Fibrations

This file contains auxiliary lemmas needed for proving Proposition 5.2.4,
the composition theorem for cartesian fibrations.

## Main Lemmas

* `comp_cartesian`: Composition of cartesian arrows (over same functor) is cartesian
* `comp_cartesian_over_comp`: The key lemma for composition of fibrations
* `cartesian_lift_unique`: Uniqueness of cartesian lifts up to unique isomorphism

## References

* [Riehl & Verity, Elements of ∞-Category Theory][elements]

## Tags

cartesian arrows, cartesian fibrations, universal properties
-/

namespace CategoryTheory

universe u v

open Category Limits Functor

variable {E B C : Type u} [Category.{v} E] [Category.{v} B] [Category.{v} C]

/-! ### Composition of Cartesian Arrows -/

/-- The composite of two cartesian arrows (over the same functor) is cartesian.

This is a fundamental property: if `f : A ⟶ B` and `g : B ⟶ D` are both cartesian
over a functor `p`, then their composite `f ≫ g : A ⟶ D` is also cartesian over `p`. -/
theorem comp_cartesian (p : E ⥤ C) {A B D : E}
    {f : A ⟶ B} {g : B ⟶ D}
    (hf : IsCartesianArrow p f) (hg : IsCartesianArrow p g) :
    IsCartesianArrow p (f ≫ g) := by
  intro x h k hcomm
  -- We have h : x → D, k : p(x) → p(A), and p(h) = k ≫ p(f ≫ g)
  -- Need φ : x → A such that φ ≫ (f ≫ g) = h and p(φ) = k

  -- Strategy: Use g to lift h to B, then f to lift that to A

  -- Step 1: Prepare for using hg
  -- We need p(h) = something ≫ p(g)
  -- We have p(h) = k ≫ p(f ≫ g) = k ≫ (p(f) ≫ p(g))
  have step0 : p.map h = (k ≫ p.map f) ≫ p.map g := by
    calc p.map h = k ≫ p.map (f ≫ g) := hcomm
      _ = k ≫ (p.map f ≫ p.map g) := by rw [p.map_comp]
      _ = (k ≫ p.map f) ≫ p.map g := by rw [Category.assoc]

  -- Step 2: Use hg to get a lift ψ : x → B
  have step1 : ∃! (ψ : x ⟶ B), ψ ≫ g = h ∧ p.map ψ = k ≫ p.map f := by
    apply hg
    exact step0
  obtain ⟨ψ, ⟨hψ_comp, hψ_map⟩, hψ_unique⟩ := step1

  -- Step 3: Use hf to lift ψ to A
  have step2 : ∃! (φ : x ⟶ A), φ ≫ f = ψ ∧ p.map φ = k := by
    apply hf
    exact hψ_map
  obtain ⟨φ, ⟨hφ_comp_f, hφ_map⟩, hφ_unique⟩ := step2

  -- Step 4: Return φ and verify it works
  use φ
  constructor
  · constructor
    · -- Prove φ ≫ (f ≫ g) = h
      calc φ ≫ (f ≫ g) = (φ ≫ f) ≫ g := by rw [Category.assoc]
        _ = ψ ≫ g := by rw [hφ_comp_f]
        _ = h := hψ_comp
    · -- Prove p.map φ = k
      exact hφ_map
  · -- Prove uniqueness
    intro φ' ⟨hφ'_comp, hφ'_map⟩
    -- We need to show φ' = φ
    -- Strategy: Show that φ' ≫ f satisfies the conditions for ψ's uniqueness
    have h_psi : φ' ≫ f = ψ := by
      apply hψ_unique
      constructor
      · -- Show (φ' ≫ f) ≫ g = h
        calc (φ' ≫ f) ≫ g = φ' ≫ (f ≫ g) := by rw [← Category.assoc]
          _ = h := hφ'_comp
      · -- Show p.map (φ' ≫ f) = k ≫ p.map f
        calc p.map (φ' ≫ f) = p.map φ' ≫ p.map f := by rw [p.map_comp]
          _ = k ≫ p.map f := by rw [hφ'_map]
    -- Now use uniqueness from hf
    apply hφ_unique
    exact ⟨h_psi, hφ'_map⟩

/-- **Key Lemma**: If `f₂ : e' ⟶ e` is cartesian over `p : E ⥤ B`,
and `p(f₂)` is cartesian over `q : B ⥤ C`, then `f₂` is cartesian over `q ∘ p`.

This is the core technical lemma needed for the composition theorem. It says that
cartesian arrows can be "lifted" through composition of functors. -/
theorem comp_cartesian_over_comp {p : E ⥤ B} {q : B ⥤ C}
    {e e' : E} (f₂ : e' ⟶ e)
    (hf₂ : IsCartesianArrow p f₂)
    (hp_f₂ : IsCartesianArrow q (p.map f₂)) :
    IsCartesianArrow (p ⋙ q) f₂ := by
  intro x h g hcomm
  -- We have h : x → e, g : q(p(x)) → q(p(e'))
  -- Condition: q(p(h)) = g ≫ q(p(f₂))
  -- Need φ : x → e' such that φ ≫ f₂ = h and q(p(φ)) = g

  -- Step 1: Use hp_f₂ to get a lift in B
  -- We have q(p(h)) = g ≫ q(p(f₂)), which is exactly the condition for hp_f₂
  have step1 : ∃! (ψ_B : p.obj x ⟶ p.obj e'),
      ψ_B ≫ p.map f₂ = p.map h ∧ q.map ψ_B = g := by
    apply hp_f₂
    -- Need to show: q.map (p.map h) = g ≫ q.map (p.map f₂)
    simp only [Functor.comp_obj, Functor.comp_map] at hcomm
    exact hcomm
  obtain ⟨ψ_B, ⟨hψ_B_comp, hψ_B_map⟩, hψ_B_unique⟩ := step1

  -- Step 2: Use hf₂ to lift ψ_B to E
  -- We have ψ_B ≫ p(f₂) = p(h), which is exactly the condition for hf₂
  have step2 : ∃! (φ : x ⟶ e'),
      φ ≫ f₂ = h ∧ p.map φ = ψ_B := by
    apply hf₂
    exact hψ_B_comp.symm
  obtain ⟨φ, ⟨hφ_comp, hφ_map⟩, hφ_unique⟩ := step2

  -- Step 3: Return φ and verify it satisfies both conditions
  use φ
  constructor
  · constructor
    · -- Prove φ ≫ f₂ = h
      exact hφ_comp
    · -- Prove (p ⋙ q).map φ = g
      calc (p ⋙ q).map φ = q.map (p.map φ) := rfl
        _ = q.map ψ_B := by rw [hφ_map]
        _ = g := hψ_B_map
  · -- Prove uniqueness
    intro φ' ⟨hφ'_comp, hφ'_map⟩
    -- We'll show φ' = φ by using the uniqueness from hf₂
    -- First, we need to show that p.map φ' = ψ_B
    have h_pmap : p.map φ' = ψ_B := by
      -- Both p.map φ' and ψ_B satisfy the conditions for ψ_B's uniqueness
      apply hψ_B_unique
      constructor
      · -- Show: p.map φ' ≫ p.map f₂ = p.map h
        calc p.map φ' ≫ p.map f₂ = p.map (φ' ≫ f₂) := by rw [← p.map_comp]
          _ = p.map h := by rw [hφ'_comp]
      · -- Show: q.map (p.map φ') = g
        calc q.map (p.map φ') = (p ⋙ q).map φ' := rfl
          _ = g := hφ'_map
    -- Now use uniqueness from hf₂
    apply hφ_unique
    exact ⟨hφ'_comp, h_pmap⟩

/-! ### Functoriality of Lifts -/

/-- The cartesian lift in E maps under p to the cartesian lift in B.

When we have two fibrations `p : E ⥤ B` and `q : B ⥤ C`, and we construct lifts
in both E and B, the lift in E should map (via p) to the lift in B.

NOTE: This lemma is not needed for the main composition theorem, so we leave it as sorry for now.-/
theorem lift_functorial {p : E ⥤ B} {q : B ⥤ C}
    {e e' : E} {b : B}
    (f₂ : e' ⟶ e) (f₁ : b ⟶ p.obj e)
    (he' : p.obj e' = b)
    (hf₂ : IsCartesianArrow p f₂)
    (hf₁ : IsCartesianArrow q f₁) :
    ∃ (heq : p.obj e' = b), p.map f₂ = eqToHom heq ≫ f₁ := by
  -- This should follow from uniqueness of cartesian lifts
  -- But we need to be careful about the exact statement
  sorry

/-! ### Uniqueness Properties -/

/-- Cartesian lifts are unique up to unique isomorphism.

If `lift₁ : e₁ ⟶ e` and `lift₂ : e₂ ⟶ e` are both cartesian lifts of the same
arrow `f : b ⟶ p(e)`, then there exists a unique isomorphism `e₁ ≅ e₂` making
the obvious triangle commute.

NOTE: This is a fundamental property but not needed for the main composition theorem.-/
theorem cartesian_lift_unique (p : E ⥤ B) {e e₁ e₂ : E} {b : B}
    (lift₁ : e₁ ⟶ e) (lift₂ : e₂ ⟶ e)
    (h₁ : IsCartesianArrow p lift₁) (h₂ : IsCartesianArrow p lift₂)
    (he₁ : p.obj e₁ = b) (he₂ : p.obj e₂ = b) :
    ∃! (iso : e₁ ≅ e₂), iso.hom ≫ lift₂ = lift₁ := by
  sorry

/-! ### Helper Lemmas -/

/-- If two morphisms become equal after applying a faithful functor,
and they satisfy the same universal property, they are equal. -/
theorem cartesian_arrow_eq_of_map_eq (p : E ⥤ B) [Faithful p]
    {A B : E} {f g : A ⟶ B}
    (hf : IsCartesianArrow p f) (hg : IsCartesianArrow p g)
    (h : p.map f = p.map g) :
    f = g := by
  sorry

end CategoryTheory
