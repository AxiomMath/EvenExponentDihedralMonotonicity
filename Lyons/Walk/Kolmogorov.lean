/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Nonneg

/-!
# The Kolmogorov forward equation

`p_t^λ` is defined as an entry of a matrix exponential. Together with
`Lyons.heatCoeffReal_nonneg` and `Lyons.sum_heatCoeffReal`, which make its values a probability
distribution, the forward equation proved here is what licenses calling it a transition function:
the distribution evolves by the generator `Δ_λ`.

The walk jumps `x ↦ x s` at rate `λ_s` — right multiplication — while the generator acts by left
convolution. The two agree because the heat matrix's entries depend only on `g h⁻¹`, so
`H g u = H (g u⁻¹) 1` and the right-translated form `p_t(g s⁻¹)` falls out of the entry sum. The
sum runs over all of `G`, not `G \ {1}`; the identity's term is `λ 1 = 0` and contributes nothing.

## Main results

* `Lyons.heatCoeffReal_zero`: `p_0^λ` is the point mass at the identity.
* `Lyons.hasDerivAt_exp_smul`: the derivative of `t ↦ exp (t • A)` is `exp (t • A) * A`.
* `Lyons.hasDerivAt_heatCoeffReal_forward`: the forward equation.
-/

open Matrix
-- `NormedSpace.exp`'s derivative lemma needs the `NormedRing` instance on matrices from this
-- scope.
open scoped Norms.Operator

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### The initial condition -/

set_option linter.unusedDecidableInType false in
/-- **The walk starts at the identity.** -/
@[lyons_tag "lem_kolmogorov_forward"]
theorem heatCoeffReal_zero (lam : RateFn G) (g : G) :
    heatCoeffReal lam 0 g = if g = 1 then 1 else 0 := by
  rw [heatCoeffReal, heatCoeff, heatMat]
  norm_num
  by_cases hg : g = 1 <;> simp [Matrix.one_apply, hg]

/-! ### Differentiating the semigroup -/

omit [Group G] in
/-- **The derivative of a matrix exponential in its time parameter.** -/
@[lyons_tag "lem_ext_exp_deriv"]
theorem hasDerivAt_exp_smul (A : Matrix G G ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A)) (NormedSpace.exp (t • A) * A) t :=
  hasDerivAt_exp_smul_const A t

set_option linter.unusedDecidableInType false in
/-- The heat matrix as `exp (t • A)` with a fixed `A`. -/
theorem heatMat_eq_exp_smul (lam : RateFn G) (t : ℝ) :
    heatMat lam t = NormedSpace.exp (t • (-(L (laplacian lam)))) := by
  rw [heatMat]
  congr 1
  ext g h
  simp [Complex.real_smul]

set_option linter.unusedDecidableInType false in
/-- The semigroup is differentiable in time, with derivative `H_t · (-Δ_λ)`. -/
theorem hasDerivAt_heatMat (lam : RateFn G) (t : ℝ) :
    HasDerivAt (fun u : ℝ => heatMat lam u)
      (heatMat lam t * (-(L (laplacian lam)))) t := by
  simp only [heatMat_eq_exp_smul]
  exact hasDerivAt_exp_smul _ t

omit [Group G] in
/-- Entry evaluation as a continuous `ℝ`-linear map. -/
noncomputable def entryCLM (g h : G) : Matrix G G ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj h : (G → ℂ) →L[ℝ] ℂ).comp
    (ContinuousLinearMap.proj g : (G → G → ℂ) →L[ℝ] (G → ℂ))

set_option linter.unusedDecidableInType false in
theorem hasDerivAt_heatMat_entry (lam : RateFn G) (t : ℝ) (g h : G) :
    HasDerivAt (fun u : ℝ => heatMat lam u g h)
      ((heatMat lam t * (-(L (laplacian lam)))) g h) t :=
  (entryCLM g h).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_heatMat lam t)

set_option linter.unusedDecidableInType false in
theorem hasDerivAt_heatCoeffReal (lam : RateFn G) (t : ℝ) (g : G) :
    HasDerivAt (fun u : ℝ => heatCoeffReal lam u g)
      (((heatMat lam t * (-(L (laplacian lam)))) g 1).re) t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_heatMat_entry lam t g 1)

/-! ### Identifying the derivative -/

set_option linter.unusedDecidableInType false in
/-- The `(g, 1)` entry of `H_t (-Δ_λ)`, as a rate-weighted sum of the increments
`p_t(g s⁻¹) - p_t(g)`. -/
theorem deriv_heatCoeffReal_eq (lam : RateFn G) (t : ℝ) (g : G) :
    ((heatMat lam t * (-(L (laplacian lam)))) g 1).re
      = ∑ s : G, lam s * (heatCoeffReal lam t (g * s⁻¹) - heatCoeffReal lam t g) := by
  classical
  set f : G → ℝ := fun u => heatCoeffReal lam t (g * u⁻¹) with hf
  have hf1 : f 1 = heatCoeffReal lam t g := by simp [hf]
  have hentry : ∀ u : G, heatMat lam t g u = ((f u : ℝ) : ℂ) := by
    intro u
    rw [heatMat_conv lam t g u]
    exact heatCoeff_eq_real lam t (g * u⁻¹)
  have hc : (heatMat lam t * (-(L (laplacian lam)))) g 1
      = ((∑ u : G, f u * (-(co (laplacian lam) u)) : ℝ) : ℂ) := by
    rw [Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [hentry u, Matrix.neg_apply, L_apply, inv_one, mul_one]
  rw [hc, Complex.ofReal_re]
  have hterm : ∀ u : G, f u * (-(co (laplacian lam) u))
      = lam u * f u - (if u = 1 then (∑ s : G, lam s) * f 1 else 0) := by
    intro u
    rw [coe_laplacian]
    by_cases hu : u = 1
    · subst hu; simp; ring
    · simp [hu]; ring
  have hL : ∑ u : G, f u * (-(co (laplacian lam) u))
      = (∑ u : G, lam u * f u) - (∑ s : G, lam s) * heatCoeffReal lam t g := by
    rw [Finset.sum_congr rfl fun u _ ↦ hterm u, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ (1 : G) (fun _ => (∑ s : G, lam s) * f 1)]
    simp [hf1]
  have hR : ∑ s : G, lam s * (f s - heatCoeffReal lam t g)
      = (∑ u : G, lam u * f u) - (∑ s : G, lam s) * heatCoeffReal lam t g := by
    rw [Finset.sum_congr rfl fun s _ ↦ mul_sub (lam s) (f s) (heatCoeffReal lam t g),
      Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hL, hR]

set_option linter.unusedDecidableInType false in
/-- **The Kolmogorov forward equation.** -/
@[lyons_tag "lem_kolmogorov_forward"]
theorem hasDerivAt_heatCoeffReal_forward (lam : RateFn G) (t : ℝ) (g : G) :
    HasDerivAt (fun u : ℝ => heatCoeffReal lam u g)
      (∑ s : G, lam s * (heatCoeffReal lam t (g * s⁻¹) - heatCoeffReal lam t g)) t := by
  rw [← deriv_heatCoeffReal_eq lam t g]
  exact hasDerivAt_heatCoeffReal lam t g

end Lyons
