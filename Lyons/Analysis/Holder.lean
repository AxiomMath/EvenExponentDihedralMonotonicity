/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.MeanInequalities
import Lyons.Meta.Tag

/-!
# Hölder's inequality in counting-norm form

Mathlib's `Real.inner_le_Lp_mul_Lq_of_nonneg` states Hölder's inequality with the two exponents
arbitrary reals in `HolderConjugate` position and the powers taken as `Real.rpow`. Recorded here is
the shape with natural powers and with the `(k+2)`-th root of a sum in place of a norm.

Everything is indexed by `k : ℕ`, the large exponent being `k + 2`, so that the paired exponent
`k + 1` is a numeral-free natural number and no truncated subtraction appears.

## Main definitions

* `Lyons.rootSum` : the `(k+2)`-th root of `∑ f i ^ (k+2)`, i.e. the counting
  `ℓ^{k+2}` norm of a nonnegative family.

## Main results

* `Lyons.rootSum_pow` : the root recovers the sum on raising to the `(k+2)`-th power.
* `Lyons.sum_pow_succ_mul_le` : Hölder's inequality,
  `∑ f i ^ (k+1) * g i ≤ rootSum f k ^ (k+1) * rootSum g k`.
-/

open Finset

namespace Lyons

variable {ι : Type*} (s : Finset ι)

/-- The counting `ℓ^{k+2}` norm of a family of reals: the `(k+2)`-th root of
`∑ f i ^ (k+2)`. -/
noncomputable def rootSum (f : ι → ℝ) (k : ℕ) : ℝ :=
  (∑ i ∈ s, f i ^ (k + 2)) ^ (((k + 2 : ℕ) : ℝ)⁻¹)

variable {s}

/-- A sum of powers of nonnegative reals is nonnegative. -/
theorem sum_pow_nonneg {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (m : ℕ) :
    (0 : ℝ) ≤ ∑ i ∈ s, f i ^ m :=
  Finset.sum_nonneg fun i hi => pow_nonneg (hf i hi) m

theorem rootSum_nonneg {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (k : ℕ) :
    0 ≤ rootSum s f k :=
  Real.rpow_nonneg (sum_pow_nonneg hf _) _

/-- Raising the root back to the `(k+2)`-th power recovers the sum. -/
theorem rootSum_pow {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (k : ℕ) :
    rootSum s f k ^ (k + 2) = ∑ i ∈ s, f i ^ (k + 2) := by
  have hq : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [rootSum, ← Real.rpow_natCast (_ ^ _) (k + 2),
    ← Real.rpow_mul (sum_pow_nonneg hf _)]
  rw [show (((k + 2 : ℕ) : ℝ)⁻¹ * ((k + 2 : ℕ) : ℝ)) = 1 from inv_mul_cancel₀ hq,
    Real.rpow_one]

/-- Monotonicity of the root in the sum. -/
theorem rootSum_le_rootSum {f g : ι → ℝ} {k : ℕ} (hf : ∀ i ∈ s, 0 ≤ f i)
    (h : ∑ i ∈ s, f i ^ (k + 2) ≤ ∑ i ∈ s, g i ^ (k + 2)) :
    rootSum s f k ≤ rootSum s g k :=
  Real.rpow_le_rpow (sum_pow_nonneg hf _) h (by positivity)

/-- **Hölder's inequality**, in counting-norm form. -/
@[lyons_tag "lem_ext_holder"]
theorem sum_pow_succ_mul_le {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) (k : ℕ) :
    ∑ i ∈ s, f i ^ (k + 1) * g i
      ≤ rootSum s f k ^ (k + 1) * rootSum s g k := by
  have hqne : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hq1 : (1 : ℝ) < ((k + 2 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨p, hcq⟩ : ∃ p : ℝ, (((k + 2 : ℕ) : ℝ)).HolderConjugate p :=
    ⟨_, Real.HolderConjugate.conjExponent hq1⟩
  have hsub : (((k + 2 : ℕ) : ℝ) - 1) * p = ((k + 2 : ℕ) : ℝ) := hcq.sub_one_mul_conj
  have hinv : p⁻¹ + ((k + 2 : ℕ) : ℝ)⁻¹ = 1 := hcq.symm.inv_add_inv_eq_one
  have hk1 : ((k + 1 : ℕ) : ℝ) = ((k + 2 : ℕ) : ℝ) - 1 := by push_cast; ring
  have hF : ∀ i ∈ s, (0 : ℝ) ≤ f i ^ (k + 1) := fun i hi => pow_nonneg (hf i hi) _
  have key := Real.inner_le_Lp_mul_Lq_of_nonneg s
    (p := p) (q := ((k + 2 : ℕ) : ℝ)) hcq.symm hF hg
  have hfp : ∀ i ∈ s, (f i ^ (k + 1)) ^ p = f i ^ (k + 2) := fun i hi => by
    rw [← Real.rpow_natCast (f i) (k + 1), ← Real.rpow_mul (hf i hi), hk1, hsub,
      Real.rpow_natCast]
  have hgq : ∀ i ∈ s, g i ^ ((k + 2 : ℕ) : ℝ) = g i ^ (k + 2) := fun i _ =>
    Real.rpow_natCast (g i) (k + 2)
  rw [Finset.sum_congr rfl hfp, Finset.sum_congr rfl hgq] at key
  refine key.trans (le_of_eq ?_)
  have hexp : 1 / p = ((k + 2 : ℕ) : ℝ)⁻¹ * ((k + 1 : ℕ) : ℝ) := by
    have hp' : p⁻¹ = 1 - ((k + 2 : ℕ) : ℝ)⁻¹ := by linarith
    rw [one_div, hp']
    field_simp
    push_cast
    ring
  rw [rootSum, rootSum, ← Real.rpow_natCast (_ ^ ((k + 2 : ℕ) : ℝ)⁻¹) (k + 1),
    ← Real.rpow_mul (sum_pow_nonneg hf _), ← hexp]
  simp only [one_div]

end Lyons
