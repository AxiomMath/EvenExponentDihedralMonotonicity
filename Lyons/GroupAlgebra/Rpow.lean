/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.Matrix.Order
import Lyons.GroupAlgebra.Commutant

/-!
# Fractional powers of positive elements of the group algebra

Fractional powers are taken on the operator side, in `Matrix G G ℂ`, via the continuous functional
calculus. `Lyons.cfc_L_conv` shows the result is again a left convolution, so the coefficient
function of `x ^ θ` can be read off the first column without ever constructing a group-algebra
element.

The Loewner order on matrices is `scoped[MatrixOrder]`, so `open scoped MatrixOrder ComplexOrder`
is required before `Matrix G G ℂ` has a `PartialOrder`, hence before `M ^ (θ : ℝ)` elaborates.

## Main results

* `Lyons.mrpow_nonneg`: `0 ≤ (L x) ^ θ`, with no hypothesis needed.
* `Lyons.mrpow_add`: `(L x) ^ (θ + θ') = (L x) ^ θ * (L x) ^ θ'` for `θ, θ' > 0`, with no
  invertibility hypothesis.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
/-- Positivity of `L x` in the Loewner order is exactly `IsPos x`. -/
theorem isPos_iff_le (x : MonoidAlgebra ℝ G) : IsPos x ↔ 0 ≤ L x :=
  Matrix.nonneg_iff_posSemidef.symm

-- `DecidableEq G` is needed for the `Matrix G G ℂ` ring structure these statements are about, but
-- Lean sees it used only inside the proof terms.
set_option linter.unusedDecidableInType false in
/-- Fractional powers of `L x` are positive, with **no** hypothesis on `x`: `nnrpow` is built from
`cfcₙ`, which preserves the nonnegativity predicate unconditionally. -/
theorem mrpow_nonneg (x : MonoidAlgebra ℝ G) (θ : NNReal) :
    (0 : Matrix G G ℂ) ≤ (L x) ^ θ :=
  CFC.nnrpow_nonneg

set_option linter.unusedDecidableInType false in
/-- Fractional powers add, for strictly positive exponents and with **no** invertibility
hypothesis. -/
@[lyons_tag "lem_algebra_rpow_add"]
theorem mrpow_add (x : MonoidAlgebra ℝ G) {θ θ' : NNReal}
    (hθ : 0 < θ) (hθ' : 0 < θ') :
    (L x) ^ (θ + θ') = (L x) ^ θ * (L x) ^ θ' :=
  CFC.nnrpow_add hθ hθ'

end Lyons
