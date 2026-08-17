/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-! # The formal challenge file, written by humans

This is a human-written file certifying the formal statement that this repository proves.

-/

open Finset

namespace Lyons

variable {G : Type*}

/-- The coefficient of `x` at `g`. -/
def co (x : MonoidAlgebra ℝ G) (g : G) : ℝ := x.coeff g

/-- The left regular representation, as a complex `G × G` matrix. -/
def L [Group G] (x : MonoidAlgebra ℝ G) : Matrix G G ℂ :=
  Matrix.of fun g h => ((co x (g * h⁻¹) : ℝ) : ℂ)

/-- A symmetric rate function on a finite group: nonnegative, invariant under
inversion, and vanishing at the identity.

Rates live on all of `G`, with value `0` at the identity, rather than on
`G \ {1}`: the identity contributes `λ₁ • (1 - 1) = 0` to the Laplacian below, so
extending a rate by zero at `1` changes nothing it feeds. -/
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

end

end RateFn

variable [Group G] [Fintype G] [DecidableEq G]

/-- The group-algebra Laplacian `Δ_λ = ∑ s, λ s • (1 - s)`. -/
noncomputable def laplacian (lam : RateFn G) : MonoidAlgebra ℝ G :=
  ∑ s : G, lam s • (1 - MonoidAlgebra.single s (1 : ℝ))

/-- The heat semigroup as a matrix: `exp (-t Δ_λ)` acting by left convolution. -/
noncomputable def heatMat (lam : RateFn G) (t : ℝ) : Matrix G G ℂ :=
  NormedSpace.exp (-(t : ℂ) • L (laplacian lam))

/-- The transition function `p_t^λ`, the first column of `exp (-t Δ_λ)`. -/
noncomputable def heatCoeff (lam : RateFn G) (t : ℝ) : G → ℂ :=
  fun g => heatMat lam t g 1

/-- The transition function `p_t^λ`, as an honestly `ℝ`-valued function.

The source defines `p_t^λ(g)` probabilistically, as the chance that the walk
started at the identity with jump rates `λ` sits at `g` at time `t`. Its
Proposition 2.3 identifies that probability with this matrix entry. -/
noncomputable def heatCoeffReal (lam : RateFn G) (t : ℝ) : G → ℝ :=
  fun g => (heatCoeff lam t g).re

end Lyons

namespace Lyons.Challenge

/-- **`thm_main` — the main theorem.** Raising every rate cannot increase the
`ℓ^{2m}` distance of the walk's time-`t` distribution from uniform. `D_n` has
`2n` elements, so `(2 * n)⁻¹` is the uniform value at each point. -/
theorem thm_main (n : ℕ) [NeZero n] (hn : 2 ≤ n) (m : ℕ) (hm : 1 ≤ m)
    (lam mu : Lyons.RateFn (DihedralGroup n))
    (hle : ∀ s : DihedralGroup n, s ≠ 1 → lam s ≤ mu s) (t : ℝ) (ht : 0 ≤ t) :
    ∑ g : DihedralGroup n, |Lyons.heatCoeffReal mu t g - (2 * n : ℝ)⁻¹| ^ (2 * m)
      ≤ ∑ g : DihedralGroup n, |Lyons.heatCoeffReal lam t g - (2 * n : ℝ)⁻¹| ^ (2 * m) :=
  sorry

end Lyons.Challenge
