/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Lyons.Meta.Tag

/-!
# Bounding a spectrum by an annihilating polynomial

An annihilating polynomial confines the spectrum to its roots. For a `2 × 2` dihedral block `M`
this gives the spectrum without ever computing it, since `(M - μ₊)(M - μ₋) = 0`.

## Main results

* `Lyons.spectrum_subset_pair_of_mul_eq_zero` : if `(M - a)(M - b) = 0` then
  `spectrum ℝ M ⊆ {a, b}`.
-/

namespace Lyons

/-- If `(M - a)(M - b) = 0` then every spectral value of `M` is `a` or `b`. -/
@[lyons_tag "lem_spectrum_pair"]
theorem spectrum_subset_pair_of_mul_eq_zero {A : Type*} [Ring A] [Algebra ℝ A]
    [Nontrivial A] (M : A) (a b : ℝ)
    (h : (M - algebraMap ℝ A a) * (M - algebraMap ℝ A b) = 0) :
    spectrum ℝ M ⊆ {a, b} := by
  intro l hl
  have hp := spectrum.subset_polynomial_aeval M
    ((Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b))
  have hmem : Polynomial.eval l
      ((Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b))
      ∈ spectrum ℝ (Polynomial.aeval M
        ((Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b))) :=
    hp ⟨l, hl, rfl⟩
  rw [map_mul] at hmem
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, h] at hmem
  rw [spectrum.zero_eq] at hmem
  simp only [Set.mem_singleton_iff, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero, sub_eq_zero] at hmem
  exact hmem

end Lyons
