/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.GroupAlgebra.Conj
import Lyons.GroupAlgebra.Rpow

/-!
# The square root of a positive group-algebra element

A positive `x` factors as `y⋆ y` with `y` again in the group algebra. Positivity of `x` is defined
through `L x`, so this factorisation is what makes positivity transportable along a representation
other than `L`.

The square root is taken with the **unital real** functional calculus, `cfc Real.sqrt`, rather than
Mathlib's `CFC.sqrt`. `CFC.sqrt` is defined as `cfcₙ NNReal.sqrt`, in the non-unital `ℝ≥0`
calculus, where the conjugation lemma of `Lyons.GroupAlgebra.Conj` — an `ℝ`-algebra star hom — does
not apply. Staying unital keeps `conjHom_cfc_L` usable.

## Main definitions

* `Lyons.msqrt`: the positive square root of a matrix.
* `Lyons.sqrtElt`: the group-algebra square root, read off column one.
* `Lyons.mpow`: the `θ`-th power of a matrix.
* `Lyons.powElt`: the group-algebra `θ`-th power, read off column one.

## Main results

* `Lyons.msqrt_mul_self`: `msqrt M * msqrt M = M` for `0 ≤ M`.
* `Lyons.sqrtElt_mul_self`: `sqrtElt x * sqrtElt x = x`.
* `Lyons.invol_sqrtElt`: `sqrtElt x` is self-adjoint.
* `Lyons.eq_invol_mul_self`: a positive element factors as `invol y * y`.
* `Lyons.mpow_nonneg`, `Lyons.mpow_mul_mpow`: fractional matrix powers are positive and add.
* `Lyons.L_powElt`: `L (powElt x θ) = mpow (L x) θ`.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The positive square root, via the unital real functional calculus. -/
noncomputable def msqrt (M : Matrix G G ℂ) : Matrix G G ℂ := cfc Real.sqrt M

omit [Group G] in
/-- The `ℝ`-spectrum of a positive matrix is nonnegative. -/
theorem spectrum_nonneg_of_nonneg {M : Matrix G G ℂ} (hM : 0 ≤ M) :
    ∀ r ∈ spectrum ℝ M, 0 ≤ r :=
  (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) M).mp hM

omit [Group G] in
/-- `msqrt` squares to the original matrix. -/
theorem msqrt_mul_self {M : Matrix G G ℂ} (hM : 0 ≤ M) : msqrt M * msqrt M = M := by
  have hsa : IsSelfAdjoint M := (Matrix.nonneg_iff_posSemidef.mp hM).isHermitian
  rw [msqrt, ← cfc_mul Real.sqrt Real.sqrt M]
  rw [cfc_congr (g := fun r : ℝ => r)
    fun r hr => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hM r hr)]
  exact cfc_id' ℝ M

omit [Group G] in
/-- `msqrt` is positive. -/
theorem msqrt_nonneg (M : Matrix G G ℂ) (hM : 0 ≤ M) : 0 ≤ msqrt M := by
  have hsa : IsSelfAdjoint M := (Matrix.nonneg_iff_posSemidef.mp hM).isHermitian
  exact cfc_nonneg fun r _ => Real.sqrt_nonneg r

/-- The group-algebra square root of a positive element, read off the first column of
`msqrt (L x)`. -/
noncomputable def sqrtElt (x : MonoidAlgebra ℝ G) : MonoidAlgebra ℝ G :=
  ofFun (fun g => (msqrt (L x) g 1).re)

/-- The left regular matrix of `sqrtElt x` is `msqrt (L x)`. -/
theorem L_sqrtElt (x : MonoidAlgebra ℝ G) (hx : IsPos x) :
    L (sqrtElt x) = msqrt (L x) := by
  have hle : (0 : Matrix G G ℂ) ≤ L x := (isPos_iff_le x).mp hx
  have hsa : IsSelfAdjoint (L x) := (Matrix.nonneg_iff_posSemidef.mp hle).isHermitian
  have hcont : ContinuousOn Real.sqrt (spectrum ℝ (L x)) := by fun_prop
  ext g h
  have hreal : (msqrt (L x) (g * h⁻¹) 1).im = 0 := by
    rw [msqrt]; exact cfc_L_im_eq_zero x Real.sqrt hcont hsa _ _
  have hconv : msqrt (L x) g h = msqrt (L x) (g * h⁻¹) 1 := by
    rw [msqrt]; exact cfc_L_conv x Real.sqrt g h
  rw [L_apply, sqrtElt, co_ofFun, hconv]
  apply Complex.ext <;> simp [hreal]

/-- **The group-algebra square root squares to `x`.** -/
theorem sqrtElt_mul_self (x : MonoidAlgebra ℝ G) (hx : IsPos x) :
    sqrtElt x * sqrtElt x = x := by
  have hle : (0 : Matrix G G ℂ) ≤ L x := (isPos_iff_le x).mp hx
  refine L_injective ?_
  rw [L_mul, L_sqrtElt x hx, msqrt_mul_self hle]

/-- **The group-algebra square root is self-adjoint.** -/
theorem invol_sqrtElt (x : MonoidAlgebra ℝ G) (hx : IsPos x) :
    invol (sqrtElt x) = sqrtElt x := by
  have hle : (0 : Matrix G G ℂ) ≤ L x := (isPos_iff_le x).mp hx
  refine L_injective ?_
  rw [L_invol, L_sqrtElt x hx]
  exact (Matrix.nonneg_iff_posSemidef.mp (msqrt_nonneg (L x) hle)).isHermitian

/-- **A positive element factors as `y⋆ y` inside the group algebra.** This is what makes
positivity transferable along *any* star representation, including ones unrelated to `L`. -/
theorem eq_invol_mul_self (x : MonoidAlgebra ℝ G) (hx : IsPos x) :
    x = invol (sqrtElt x) * sqrtElt x := by
  rw [invol_sqrtElt x hx, sqrtElt_mul_self x hx]

/-! ### General fractional powers

The square root above is the case `θ = 1/2`. For a general exponent `θ ≥ 0` the same three steps
apply: define the power via the unital calculus, read it off column one, and identify the result
with the matrix power. -/

/-- The `θ`-th power via the unital real functional calculus. -/
noncomputable def mpow (M : Matrix G G ℂ) (θ : ℝ) : Matrix G G ℂ :=
  cfc (fun t : ℝ => t ^ θ) M

omit [Group G] in
/-- **Fractional powers of a positive matrix are positive.** -/
@[lyons_tag "lem_ext_rpow"]
theorem mpow_nonneg {M : Matrix G G ℂ} (hM : 0 ≤ M) (θ : ℝ) : 0 ≤ mpow M θ := by
  have hsa : IsSelfAdjoint M := (Matrix.nonneg_iff_posSemidef.mp hM).isHermitian
  exact cfc_nonneg fun r hr => Real.rpow_nonneg (spectrum_nonneg_of_nonneg hM r hr) θ

omit [Group G] in
/-- **Fractional powers add, for strictly positive exponents.** No invertibility hypothesis is
needed, so the spectrum of `M` may contain `0`. -/
@[lyons_tag "lem_ext_rpow_add"]
theorem mpow_mul_mpow {M : Matrix G G ℂ} (hM : 0 ≤ M) {θ θ' : ℝ}
    (hθ : 0 < θ) (hθ' : 0 < θ') :
    mpow M θ * mpow M θ' = mpow M (θ + θ') := by
  have hsa : IsSelfAdjoint M := (Matrix.nonneg_iff_posSemidef.mp hM).isHermitian
  have hc : Continuous (fun t : ℝ => t ^ θ) := Real.continuous_rpow_const hθ.le
  have hc' : Continuous (fun t : ℝ => t ^ θ') := Real.continuous_rpow_const hθ'.le
  rw [mpow, mpow, mpow, ← cfc_mul _ _ M hc.continuousOn hc'.continuousOn]
  refine cfc_congr fun r hr => ?_
  exact (Real.rpow_add' (spectrum_nonneg_of_nonneg hM r hr) (by positivity)).symm

/-- **The group-algebra `θ`-th power** of a positive element, read off column one. -/
@[lyons_tag "def_algebra_rpow"]
noncomputable def powElt (x : MonoidAlgebra ℝ G) (θ : ℝ) : MonoidAlgebra ℝ G :=
  ofFun (fun g => (mpow (L x) θ g 1).re)

/-- `L` of the group-algebra power is the matrix power; the general-exponent analogue of
`L_sqrtElt`. -/
@[lyons_tag "lem_algebra_rpow_L"]
theorem L_powElt (x : MonoidAlgebra ℝ G) (hx : IsPos x) {θ : ℝ} (hθ : 0 ≤ θ) :
    L (powElt x θ) = mpow (L x) θ := by
  have hle : (0 : Matrix G G ℂ) ≤ L x := (isPos_iff_le x).mp hx
  have hsa : IsSelfAdjoint (L x) := (Matrix.nonneg_iff_posSemidef.mp hle).isHermitian
  have hcont : ContinuousOn (fun t : ℝ => t ^ θ) (spectrum ℝ (L x)) :=
    (Real.continuous_rpow_const hθ).continuousOn
  ext g h
  have hreal : (mpow (L x) θ (g * h⁻¹) 1).im = 0 := by
    rw [mpow]; exact cfc_L_im_eq_zero x _ hcont hsa _ _
  have hconv : mpow (L x) θ g h = mpow (L x) θ (g * h⁻¹) 1 := by
    rw [mpow]; exact cfc_L_conv x _ g h
  rw [L_apply, powElt, co_ofFun, hconv]
  apply Complex.ext <;> simp [hreal]

end Lyons
