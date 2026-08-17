/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons

/-! # Satisfying the formal challenge -/

open Finset

namespace Lyons.Challenge

set_option linter.unusedVariables false in
/-- **`thm_main` — the main theorem.** Raising every rate cannot increase the
`ℓ^{2m}` distance of the walk's time-`t` distribution from uniform. `D_n` has
`2n` elements, so `(2 * n)⁻¹` is the uniform value at each point. -/
theorem thm_main (n : ℕ) [NeZero n] (hn : 2 ≤ n) (m : ℕ) (hm : 1 ≤ m)
    (lam mu : Lyons.RateFn (DihedralGroup n))
    (hle : ∀ s : DihedralGroup n, s ≠ 1 → lam s ≤ mu s) (t : ℝ) (ht : 0 ≤ t) :
    ∑ g : DihedralGroup n, |Lyons.heatCoeffReal mu t g - (2 * n : ℝ)⁻¹| ^ (2 * m)
      ≤ ∑ g : DihedralGroup n, |Lyons.heatCoeffReal lam t g - (2 * n : ℝ)⁻¹| ^ (2 * m) :=
  Lyons.sum_abs_centered_pow_le lam mu hle ht hm

end Lyons.Challenge
