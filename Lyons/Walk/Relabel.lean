/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Laplacian

/-!
# Relabelling a rate function along a group automorphism

An automorphism `φ` of a finite group transports a rate function to `λ^φ = λ ∘ φ`, and the
Laplacian, the transition function and the centred power sum transport with it. For the dihedral
group this is what carries a statement proved at one distinguished reflection to an arbitrary
one, since any two reflections are exchanged by an automorphism.

The transport is proved without building the induced algebra automorphism of `ℝ[G]`, whose
multiplicativity would have to be proved. Instead `Lyons.coe_laplacian` writes the Laplacian's
coefficients out in closed form, from which `L (Δ_{λ^φ})` is visibly `L (Δ_λ)` with rows and
columns permuted by `φ`. Reindexing is an algebra isomorphism of the matrix algebra and is
continuous, so it commutes with the exponential, and reading off column one gives the transported
transition function.

## Main definitions

* `Lyons.RateFn.comp`: `λ^φ`, the relabelled rate function.

## Main results

* `Lyons.exp_reindex`: reindexing rows and columns commutes with the matrix exponential.
* `Lyons.heatCoeffReal_comp`: the transition function transports.
* `Lyons.Phi_comp`: the centred power sum is unchanged.
* `Lyons.comp_setAt`: relabelling commutes with setting one reflection's rate.
-/

open Matrix
-- `NormedSpace.map_exp` needs the `NormedRing` instance on matrices that this scope provides;
-- opening it does not touch the `‖·‖` on `ℂ` that `Lyons.Phi` uses.
open scoped Norms.Operator

namespace Lyons

/-! ### The relabelled rate function -/

section Rate

variable {G : Type*} [Group G] [DecidableEq G]

/-- **The relabelled rate function** `λ^φ`, with `λ^φ g = λ (φ g)`. An automorphism fixes the
identity, so `λ^φ` again vanishes there. -/
@[lyons_tag "def_rate_comp"]
def RateFn.comp (lam : RateFn G) (φ : G ≃* G) : RateFn G where
  toFun g := lam (φ g)
  nonneg' g := lam.nonneg _
  symm' g := by rw [map_inv, lam.symm]
  atOne := by rw [map_one, lam.apply_one]

omit [DecidableEq G] in
@[simp] theorem RateFn.comp_apply (lam : RateFn G) (φ : G ≃* G) (g : G) :
    lam.comp φ g = lam (φ g) := rfl

omit [DecidableEq G] in
/-- **The relabelled function is a symmetric rate function**: nonnegative, invariant under
inversion, and vanishing at the identity. -/
@[lyons_tag "lem_rate_comp_symmetric"]
theorem RateFn.comp_isRate (lam : RateFn G) (φ : G ≃* G) :
    (∀ g : G, 0 ≤ lam.comp φ g) ∧ (∀ g : G, lam.comp φ g⁻¹ = lam.comp φ g) ∧
      lam.comp φ 1 = 0 :=
  ⟨fun g => (lam.comp φ).nonneg g, fun g => (lam.comp φ).symm g,
    (lam.comp φ).apply_one⟩

/-- **Relabelling commutes with setting one reflection's rate.** The hypotheses on `b` follow
from those on `s` together with `φ b = s`, since `φ` is an isomorphism. -/
@[lyons_tag "lem_refl_family_relabel"]
theorem comp_setAt (lam : RateFn G) (φ : G ≃* G) {s b : G} (hsb : φ b = s)
    (hs : s⁻¹ = s) (hs1 : s ≠ 1) (hb : b⁻¹ = b) (hb1 : b ≠ 1) {α : ℝ}
    (hα : 0 ≤ α) :
    (lam.setAt hs hs1 hα).comp φ = (lam.comp φ).setAt hb hb1 hα := by
  refine DFunLike.ext _ _ fun g => ?_
  rw [RateFn.comp_apply]
  by_cases hg : g = b
  · subst hg
    rw [hsb, lam.setAt_apply_self hs hs1 hα,
      (lam.comp φ).setAt_apply_self hb hb1 hα]
  · have hφg : φ g ≠ s := fun h => hg (φ.injective (h.trans hsb.symm))
    rw [lam.setAt_apply_of_ne hs hs1 hα hφg,
      (lam.comp φ).setAt_apply_of_ne hb hb1 hα hg, RateFn.comp_apply]

end Rate

/-! ### The Laplacian in coordinates -/

section Transport

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

set_option linter.unusedDecidableInType false in
/-- Relabelling the rate function relabels the Laplacian's coefficients. -/
theorem co_laplacian_comp (lam : RateFn G) (φ : G ≃* G) (u : G) :
    co (laplacian (lam.comp φ)) u = co (laplacian lam) (φ u) := by
  have hsum : ∑ s : G, lam.comp φ s = ∑ s : G, lam s :=
    Fintype.sum_equiv φ.toEquiv _ _ fun s => by simp
  rw [coe_laplacian, coe_laplacian, RateFn.comp_apply, hsum]
  by_cases hu : u = 1
  · subst hu; simp
  · have hφu : φ u ≠ 1 := fun h => hu (by simpa using φ.injective (h.trans (map_one φ).symm))
    simp [hu, hφu]

/-! ### Transport along the reindexing

`Matrix.reindex e e` with `e = φ⁻¹` sends a matrix `A` to `fun g h => A (φ g) (φ h)`. -/

omit [Group G] [Fintype G] [DecidableEq G] in
/-- Reindexing rows and columns is continuous: each entry of the image is one entry of the
argument. -/
theorem continuous_reindex (e : G ≃ G) :
    Continuous (Matrix.reindex e e : Matrix G G ℂ → Matrix G G ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (continuous_apply (e.symm j)).comp (continuous_apply (e.symm i))

set_option linter.unusedDecidableInType false in
/-- The left regular matrix of the relabelled Laplacian is the original one with
rows and columns permuted by `φ`. -/
theorem L_laplacian_comp (lam : RateFn G) (φ : G ≃* G) :
    L (laplacian (lam.comp φ))
      = Matrix.reindex φ.toEquiv.symm φ.toEquiv.symm (L (laplacian lam)) := by
  ext g h
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, L_apply, L_apply,
    co_laplacian_comp]
  congr 2
  simp [map_mul, map_inv]

omit [Group G] in
/-- **Reindexing rows and columns commutes with the exponential.** -/
@[lyons_tag "lem_ext_exp_reindex"]
theorem exp_reindex (e : G ≃ G) (A : Matrix G G ℂ) :
    NormedSpace.exp (Matrix.reindex e e A)
      = Matrix.reindex e e (NormedSpace.exp A) :=
  (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom
    (continuous_reindex _) A).symm

/-- The heat matrix transports: reindexing commutes with the exponential. -/
theorem heatMat_comp (lam : RateFn G) (φ : G ≃* G) (t : ℝ) :
    heatMat (lam.comp φ) t
      = Matrix.reindex φ.toEquiv.symm φ.toEquiv.symm (heatMat lam t) := by
  have hsmul : (-(t : ℂ)) •
        Matrix.reindex φ.toEquiv.symm φ.toEquiv.symm (L (laplacian lam))
      = Matrix.reindex φ.toEquiv.symm φ.toEquiv.symm
          ((-(t : ℂ)) • L (laplacian lam)) := rfl
  rw [heatMat, heatMat, L_laplacian_comp, hsmul]
  exact exp_reindex _ _

/-- **The transition function transports along a relabelling**, on the `ℂ`-valued
coefficient. -/
theorem heatCoeff_comp (lam : RateFn G) (φ : G ≃* G) (t : ℝ) (g : G) :
    heatCoeff (lam.comp φ) t g = heatCoeff lam t (φ g) := by
  rw [heatCoeff, heatCoeff, heatMat_comp, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  simp

/-- **The transition function transports along a relabelling.** -/
@[lyons_tag "lem_heat_relabel"]
theorem heatCoeffReal_comp (lam : RateFn G) (φ : G ≃* G) (t : ℝ) (g : G) :
    heatCoeffReal (lam.comp φ) t g = heatCoeffReal lam t (φ g) := by
  rw [heatCoeffReal, heatCoeffReal, heatCoeff_comp]

/-- **The centred power sum is unchanged by a relabelling**: the summands correspond term by
term under `φ`, which is a bijection of `G`. -/
@[lyons_tag "lem_Phi_relabel"]
theorem Phi_comp (lam : RateFn G) (φ : G ≃* G) (t : ℝ) (m : ℕ) :
    Phi (lam.comp φ) t m = Phi lam t m := by
  rw [Phi, Phi]
  refine Fintype.sum_equiv φ.toEquiv _ _ fun g => ?_
  have hce : centeredHeatCoeff (lam.comp φ) t g
      = centeredHeatCoeff lam t (φ.toEquiv g) := by
    simp only [centeredHeatCoeff, heatCoeff_comp]
    rfl
  rw [hce]

end Transport

end Lyons
