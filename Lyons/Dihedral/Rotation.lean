/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Dihedral.Central
import Lyons.Walk.Centered

/-!
# Increasing a rotation rate does not increase the power sum

Raising the rate on the inverse orbit of a rotation `s` adds `c ζ_s` to the Laplacian, and `ζ_s`
is central (`Lyons.orbitElt_central_r`), so the added generator commutes with the original and the
exponentials factor:

`h_t^{λ'} = h_t^ν h_t^λ`,  `ν` the rate function that is `c` on `O(s)` and `0` elsewhere.

Absorption `h_t^ν π_G = π_G` turns that into a statement about the *centred* elements,
`a_t^{λ'} = h_t^ν a_t^λ`, and `h_t^ν` is a probability element: its coefficients are nonnegative
and sum to one, so convolving by it can only contract the power sum.

## Main results

* `Lyons.heatElt_addOrbit_r`: the heat element of a rotation increment factors.
* `Lyons.centeredElt_addOrbit_r`: the same factorisation for the centred element.
* `Lyons.Phi_addOrbit_r_le`: increasing a rotation rate does not increase the power sum.
-/

open Finset DihedralGroup

namespace Lyons

/-! ### The zero rate function -/

section Zero

variable {G : Type*} [Group G]

/-- The zero rate function: no jumps at all. -/
instance instZeroRateFn : Zero (RateFn G) where
  zero :=
    { toFun := 0
      nonneg' := fun _ => le_refl 0
      symm' := fun _ => rfl
      atOne := rfl }

@[simp] theorem RateFn.zero_apply (g : G) : (0 : RateFn G) g = 0 := rfl

variable [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
@[simp] theorem laplacian_zero : laplacian (0 : RateFn G) = 0 := by
  rw [laplacian]
  simp

end Zero

/-! ### The rotation step -/

variable {n : ℕ} [NeZero n]

set_option linter.unusedDecidableInType false in
/-- The Laplacian of the single-orbit rate function is `c ζ_s`. -/
theorem laplacian_zero_addOrbit {s : DihedralGroup n} (hs1 : s ≠ 1) {c : ℝ}
    (hc : 0 ≤ c) :
    laplacian ((0 : RateFn (DihedralGroup n)).addOrbit hs1 hc) = c • orbitElt s := by
  rw [laplacian_addOrbit, laplacian_zero, zero_add]

set_option linter.unusedDecidableInType false in
/-- The heat element of an orbit increment factors, because the increment is central. -/
theorem heatElt_addOrbit_r (lam : RateFn (DihedralGroup n)) (k : ZMod n)
    (hs1 : DihedralGroup.r k ≠ 1) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    heatElt (lam.addOrbit hs1 hc) t
      = heatElt ((0 : RateFn (DihedralGroup n)).addOrbit hs1 hc) t * heatElt lam t := by
  refine L_injective ?_
  rw [L_mul, L_heatElt, L_heatElt, L_heatElt, heatMat, heatMat, heatMat]
  have hcentral : L (laplacian ((0 : RateFn (DihedralGroup n)).addOrbit hs1 hc)) *
      L (laplacian lam) = L (laplacian lam) *
        L (laplacian ((0 : RateFn (DihedralGroup n)).addOrbit hs1 hc)) := by
    rw [← L_mul, ← L_mul, laplacian_zero_addOrbit hs1 hc, smul_mul_assoc,
      mul_smul_comm, orbitElt_central_r]
  have hcomm : Commute (-(t : ℂ) • L (laplacian
      ((0 : RateFn (DihedralGroup n)).addOrbit hs1 hc)))
      (-(t : ℂ) • L (laplacian lam)) :=
    (Commute.smul_left (Commute.smul_right hcentral _) _)
  rw [← Matrix.exp_add_of_commute _ _ hcomm, ← smul_add, ← L_add,
    laplacian_addOrbit, laplacian_zero_addOrbit hs1 hc]
  congr 2
  abel_nf

set_option linter.unusedDecidableInType false in
/-- Centring commutes with the factorisation: absorption removes the extra `π_G`. -/
theorem centeredElt_addOrbit_r (lam : RateFn (DihedralGroup n)) (k : ZMod n)
    (hs1 : DihedralGroup.r k ≠ 1) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    centeredElt (lam.addOrbit hs1 hc) t
      = heatElt ((0 : RateFn (DihedralGroup n)).addOrbit hs1 hc) t
          * centeredElt lam t := by
  rw [centeredElt, centeredElt, heatElt_addOrbit_r lam k hs1 hc t, mul_sub,
    heatElt_mul_uniform]

set_option linter.unusedDecidableInType false in
/-- `Phi` in terms of the centred element's coefficients. -/
theorem Phi_eq_sum_co (lam : RateFn (DihedralGroup n)) (t : ℝ) (m : ℕ) :
    Phi lam t m = ∑ g : DihedralGroup n, (co (centeredElt lam t) g) ^ (2 * m) := by
  rw [Phi_eq_sum_real]
  exact Finset.sum_congr rfl fun g _ ↦ by rw [co_centeredElt]

set_option linter.unusedDecidableInType false in
/-- **Increasing a rotation rate does not increase the power sum.** -/
@[lyons_tag "lem_rotation_step"]
theorem Phi_addOrbit_r_le (lam : RateFn (DihedralGroup n)) (k : ZMod n)
    (hs1 : DihedralGroup.r k ≠ 1) {c : ℝ} (hc : 0 ≤ c) {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    Phi (lam.addOrbit hs1 hc) t m ≤ Phi lam t m := by
  set nu := (0 : RateFn (DihedralGroup n)).addOrbit hs1 hc with hnu
  have hnonneg : ∀ g : DihedralGroup n, 0 ≤ co (heatElt nu t) g := by
    intro g
    rw [co_heatElt]
    exact heatCoeffReal_nonneg nu ht g
  have hone : ∑ g : DihedralGroup n, co (heatElt nu t) g = 1 := by
    rw [Finset.sum_congr rfl fun g _ ↦ co_heatElt nu t g]
    exact sum_heatCoeffReal nu t
  rw [Phi_eq_sum_co, Phi_eq_sum_co, centeredElt_addOrbit_r lam k hs1 hc t]
  exact sum_pow_conv_le _ _ hnonneg hone m

end Lyons
