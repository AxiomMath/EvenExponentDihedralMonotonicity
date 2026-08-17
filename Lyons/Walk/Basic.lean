/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Order
import Lyons.GroupAlgebra.Commutant

/-!
# Symmetric rate functions, the Laplacian, and the heat element

A symmetric rate function on a finite group determines a group-algebra Laplacian, whose
exponential is the heat semigroup; centering by the uniform element gives the object whose
`ℓ^{2m}` norm the main theorem controls.

Rates are defined on all of `G`, with value `0` at the identity, rather than on `G \ {1}`. The
identity's contribution to the Laplacian is `λ₁ • (1 - 1) = 0`, so extending a rate function by
zero at `1` changes no Laplacian and no heat element, and it keeps a subtype out of every
downstream statement.

The heat and centered-heat elements are the coefficient functions read off the first column of
the matrix exponential rather than group-algebra elements: by translation invariance the first
column determines the whole matrix.

## Main definitions

* `Lyons.RateFn`: a symmetric rate function.
* `Lyons.laplacian`: `Δ_λ = ∑ s, λ s • (1 - s)`.
* `Lyons.uniform`: the uniform element `π_G`.
* `Lyons.heatMat`: `exp (-t Δ_λ)`, acting by left convolution.
* `Lyons.heatCoeff`: `p_t^λ`, the coefficient function of `exp (-t Δ_λ)`.
* `Lyons.centeredHeatCoeff`: `p_t^λ - 1/|G|`.

## Main results

* `Lyons.centeredHeatCoeff_apply`: the coefficients of the centered transition function.
* `Lyons.coe_uniform`: every coefficient of `π_G` is `1/|G|`.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- A **symmetric rate function** on a finite group: nonnegative, invariant under inversion, and
vanishing at the identity. The domain is all of `G`, with `atOne : toFun 1 = 0` in place of a
subtype `G \ {1}`; the identity contributes `λ₁ • (1 - 1) = 0` to the Laplacian, so extending by
zero there is harmless. -/
@[lyons_tag "def_rate"]
structure RateFn (G : Type*) [Group G] where
  /-- The rate assigned to each group element. -/
  toFun : G → ℝ
  /-- Rates are nonnegative. -/
  nonneg' : ∀ g, 0 ≤ toFun g
  /-- Rates are symmetric under inversion. -/
  symm' : ∀ g, toFun g⁻¹ = toFun g
  /-- The identity carries no rate. -/
  atOne : toFun 1 = 0

namespace RateFn

section
variable {G : Type*} [Group G]

instance : FunLike (RateFn G) G ℝ where
  coe := RateFn.toFun
  coe_injective f g h := by cases f; cases g; congr

@[simp] theorem coe_mk (f : G → ℝ) (h₁ h₂ h₃) :
    ((⟨f, h₁, h₂, h₃⟩ : RateFn G) : G → ℝ) = f := rfl

theorem nonneg (lam : RateFn G) (g : G) : 0 ≤ lam g := lam.nonneg' g

theorem symm (lam : RateFn G) (g : G) : lam g⁻¹ = lam g := lam.symm' g

@[simp] theorem apply_one (lam : RateFn G) : lam 1 = 0 := lam.atOne

end

end RateFn

/-- The **group-algebra Laplacian** of a symmetric rate function, `Δ_λ = ∑ s, λ s • (1 - s)`.

The sum runs over all of `G`; the identity term vanishes because `λ 1 = 0`, so this agrees with
the sum over `G \ {1}`. -/
@[lyons_tag "def_laplacian"]
noncomputable def laplacian (lam : RateFn G) : MonoidAlgebra ℝ G :=
  ∑ s : G, lam s • (1 - MonoidAlgebra.single s (1 : ℝ))

/-- The **uniform element** `π_G`, with every coefficient `1/|G|`. -/
@[lyons_tag "def_uniform"]
noncomputable def uniform (G : Type*) [Group G] [Fintype G] : MonoidAlgebra ℝ G :=
  ∑ g : G, MonoidAlgebra.single g ((Fintype.card G : ℝ)⁻¹)

/-- The heat semigroup as a matrix: `exp (-t Δ_λ)` acting by left convolution. -/
noncomputable def heatMat (lam : RateFn G) (t : ℝ) : Matrix G G ℂ :=
  NormedSpace.exp (-(t : ℂ) • L (laplacian lam))

/-- The **transition function** `p_t^λ`, defined as the coefficient function of `exp (-t Δ_λ)` —
that is, its first column. By translation invariance the first column determines the whole
matrix, so no group-algebra element need be constructed. -/
@[lyons_tag "def_heat_element"]
noncomputable def heatCoeff (lam : RateFn G) (t : ℝ) : G → ℂ :=
  fun g => heatMat lam t g 1

/-- The **centered** transition function, `p_t^λ(g) - 1/|G|`. -/
noncomputable def centeredHeatCoeff (lam : RateFn G) (t : ℝ) : G → ℂ :=
  fun g => heatCoeff lam t g - ((Fintype.card G : ℝ) : ℂ)⁻¹

/-- Coefficients of the centered heat element. -/
@[lyons_tag "lem_centered_coeff", simp]
theorem centeredHeatCoeff_apply (lam : RateFn G) (t : ℝ) (g : G) :
    centeredHeatCoeff lam t g = heatCoeff lam t g - ((Fintype.card G : ℝ) : ℂ)⁻¹ :=
  rfl

omit [DecidableEq G] in
/-- Coefficients of the uniform element. -/
@[simp] theorem coe_uniform (g : G) :
    co (uniform G) g = (Fintype.card G : ℝ)⁻¹ := by
  classical
  simp [co, uniform, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]

end Lyons
