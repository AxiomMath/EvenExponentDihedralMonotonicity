/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Basic

/-!
# Inverse orbits, one-rate families, and the centred power sum

The inverse orbit `{s, s⁻¹}` of a group element, the rate function obtained from `λ` by resetting
the rate at a single involution, and the centred power sum `Φ_m(λ, t)`.

## Main definitions

* `Lyons.invOrbit`: `O s = {s, s⁻¹}`.
* `Lyons.RateFn.setAt`: a rate function with one involution's rate replaced.
* `Lyons.Phi`: `Φ_m(λ, t) = ∑ g, ‖p_t^λ(g) - 1/|G|‖ ^ (2m)`.

## Main results

* `Lyons.inv_mem_invOrbit`: an inverse orbit is closed under inversion.
-/

open Finset

namespace Lyons

variable {G : Type*} [Group G] [DecidableEq G]

/-- The **inverse orbit** of `s`, namely `{s, s⁻¹}`. -/
@[lyons_tag "def_inverse_orbit"]
def invOrbit (s : G) : Finset G := {s, s⁻¹}

@[simp] theorem mem_invOrbit {s g : G} : g ∈ invOrbit s ↔ g = s ∨ g = s⁻¹ := by
  simp [invOrbit]

/-- An inverse orbit is closed under inversion. -/
theorem inv_mem_invOrbit {s g : G} (h : g ∈ invOrbit s) : g⁻¹ ∈ invOrbit s := by
  rcases mem_invOrbit.mp h with rfl | rfl
  · exact mem_invOrbit.mpr (Or.inr rfl)
  · exact mem_invOrbit.mpr (Or.inl (inv_inv _))

/-- **Replacing the rate at a single involution:** the rate function `λ[s ↦ α]`, which takes the
value `α` at `s` and agrees with `λ` elsewhere.

Only `s⁻¹ = s` is assumed of `s`, and symmetry of the result needs exactly that, since the
singleton `{s}` must be closed under inversion. -/
@[lyons_tag "def_refl_family"]
noncomputable def RateFn.setAt (lam : RateFn G) {s : G} (hs : s⁻¹ = s) (hs1 : s ≠ 1)
    {α : ℝ} (hα : 0 ≤ α) : RateFn G where
  toFun g := if g = s then α else lam g
  nonneg' g := by
    by_cases h : g = s
    · simpa [h] using hα
    · simpa [h] using lam.nonneg g
  symm' g := by
    by_cases h : g = s
    · subst h; simp [hs]
    · have h' : g⁻¹ ≠ s := fun hcon => h (by rw [← hs, ← hcon, inv_inv])
      simp only [h, h', if_false]
      exact lam.symm g
  atOne := by
    have : (1 : G) ≠ s := fun hcon => hs1 hcon.symm
    simp [this]

@[simp] theorem RateFn.setAt_apply_self (lam : RateFn G) {s : G} (hs : s⁻¹ = s)
    (hs1 : s ≠ 1) {α : ℝ} (hα : 0 ≤ α) : lam.setAt hs hs1 hα s = α := by
  simp [RateFn.setAt]

theorem RateFn.setAt_apply_of_ne (lam : RateFn G) {s : G} (hs : s⁻¹ = s)
    (hs1 : s ≠ 1) {α : ℝ} (hα : 0 ≤ α) {g : G} (hg : g ≠ s) :
    lam.setAt hs hs1 hα g = lam g := by
  simp [RateFn.setAt, hg]

/-- The **centred power sum** `Φ_m(λ, t) = ∑ g, ‖p_t^λ(g) - 1/|G|‖ ^ (2m)`.

The centred coefficients are `ℂ`-valued matrix entries, so the norm is taken; this agrees with
`∑ g, ((a_t)_g) ^ (2m)` whenever they are real, since `|x| ^ (2m) = x ^ (2m)` for even
exponents. -/
@[lyons_tag "def_Phi"]
noncomputable def Phi [Fintype G] (lam : RateFn G) (t : ℝ) (m : ℕ) : ℝ :=
  ∑ g : G, ‖centeredHeatCoeff lam t g‖ ^ (2 * m)

end Lyons
