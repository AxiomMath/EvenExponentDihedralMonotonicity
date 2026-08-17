/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Dihedral.RpowForm
import Lyons.Dihedral.Sandwich
import Lyons.GroupAlgebra.Transfer

/-!
# The block form of the reflection sandwich

The sandwich `x_{a,θ} = a^θ · b · a^{1-θ}` is built in the left regular representation. Its image
under `ρ_k` is a `2 × 2` matrix whose four entries are products of the eigenvalue powers
`α, β, γ, δ` of the block `ρ_k(a)`, and the two transforms `U` and `V` of the sandwich are read off
that matrix.

## Main results

* `Lyons.rhoAlg_powElt` : `ρ_k` commutes with fractional powers.
* `Lyons.rhoAlg_eq_blockM` : `ρ_k(a)` is a dihedral block.
* `Lyons.rhoAlg_sandwich` : the block form of the sandwich.
* `Lyons.re_Ublock_sandwich` : the sandwich preserves the real part of the
  reflection transform.
* `Lyons.norm_Vblock_sandwich_le` : the sandwich's reflection transform is
  dominated by `U^a`.
* `Lyons.evenPart_rotCoeff_sandwich`, `Lyons.sum_rotCoeff_pow_mul_sandwich`,
  `Lyons.sum_norm_reflCoeff_sandwich_le` : the same two facts, in terms of the
  coefficient functions.
-/

open Matrix DihedralGroup
open scoped ComplexConjugate ComplexOrder MatrixOrder

namespace Lyons

variable {n : ℕ} [NeZero n]

/-! ### `ρ_k` commutes with the functional calculus -/

/-- `ρ_k` carries self-adjoint elements to self-adjoint matrices. -/
theorem rhoAlg_isSelfAdjoint (k : ZMod n) (x : MonoidAlgebra ℝ (DihedralGroup n))
    (hsa : invol x = x) : IsSelfAdjoint (rhoAlg k x) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, ← rhoAlg_invol, hsa]

/-- **`ρ_k` commutes with fractional powers.**

There is no unital homomorphism `Matrix G G ℂ → Matrix (Fin 2) (Fin 2) ℂ` carrying
`L x` to `ρ_k x`, so this is not an instance of `StarAlgHomClass.map_cfc`; it holds
one level down, for two representations of a common group algebra. -/
@[lyons_tag "lem_ext_rpow_hom"]
theorem rhoAlg_powElt (k : ZMod n) (x : MonoidAlgebra ℝ (DihedralGroup n))
    (hx : IsPos x) {θ : ℝ} (hθ : 0 ≤ θ) :
    rhoAlg k (powElt x θ) = cfc (fun t : ℝ => t ^ θ) (rhoAlg k x) := by
  have hle : (0 : Matrix (DihedralGroup n) (DihedralGroup n) ℂ) ≤ L x :=
    (isPos_iff_le x).mp hx
  have hL : IsSelfAdjoint (L x) := (Matrix.nonneg_iff_posSemidef.mp hle).isHermitian
  exact algHom_eq_cfc_of_L (rhoAlg k) (fun t : ℝ => t ^ θ) hL
    (rhoAlg_isSelfAdjoint k x hx.invol_eq) (L_powElt x hx hθ)

/-! ### `ρ_k(a)` as a dihedral block -/

/-- Every complex number is a unit phase times its norm. At `z = 0` any phase
does, and `1` is chosen. -/
theorem exists_unit_phase (z : ℂ) : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ z = ζ * (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · exact ⟨1, norm_one, by simp [hz]⟩
  · have hne : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using norm_ne_zero_iff.mpr hz
    refine ⟨z / (‖z‖ : ℂ), ?_, (div_mul_cancel₀ z hne).symm⟩
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hz)]

/-- **`ρ_k(a)` is a dihedral block.** For self-adjoint `a` the diagonal entry is
real and the off-diagonal entries are conjugate, which is exactly the shape of
`Lyons.blockM`. -/
theorem rhoAlg_eq_blockM (k : ZMod n) (a : MonoidAlgebra ℝ (DihedralGroup n))
    (hsa : invol a = a) {U w : ℝ} {ζ : ℂ}
    (hU : ((U : ℝ) : ℂ) = Ublock a k) (hV : Vblock a k = ζ * (w : ℂ)) :
    rhoAlg k a = blockM U w ζ := by
  rw [rhoAlg_block_selfAdjoint k a hsa, ← hU, hV, blockM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.conj_ofReal]

/-! ### The block form of the sandwich -/

/-- **The block form of the reflection sandwich.**

The reflection is `sr 0`, Mathlib's `b`, whose image under `ρ_k` is the swap
`!![0, 1; 1, 0]`.

Only *some* unit `ζ` and *some* `w ≥ 0` with `V^a(k) = ζ w` are asked for, rather
than the canonical choice `w = ‖V^a(k)‖`. No hypothesis `w ≤ U` is needed, and the
degenerate case `w = 0` is admitted. -/
@[lyons_tag "lem_sandwich_block"]
theorem rhoAlg_sandwich (k : ZMod n) (a : MonoidAlgebra ℝ (DihedralGroup n))
    (hpos : IsPos a) {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    {U w : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hw : 0 ≤ w)
    (hU : ((U : ℝ) : ℂ) = Ublock a k) (hV : Vblock a k = ζ * (w : ℂ)) :
    rhoAlg k (sandwich a (sr 0) θ)
      = !![ζ * ((bpBeta U w θ * bpGamma U w θ : ℝ) : ℂ)
              + conj ζ * ((bpAlpha U w θ * bpDelta U w θ : ℝ) : ℂ),
           ((bpAlpha U w θ * bpGamma U w θ : ℝ) : ℂ)
              + ζ ^ 2 * ((bpBeta U w θ * bpDelta U w θ : ℝ) : ℂ);
           ((bpAlpha U w θ * bpGamma U w θ : ℝ) : ℂ)
              + (conj ζ) ^ 2 * ((bpBeta U w θ * bpDelta U w θ : ℝ) : ℂ),
           ζ * ((bpAlpha U w θ * bpDelta U w θ : ℝ) : ℂ)
              + conj ζ * ((bpBeta U w θ * bpGamma U w θ : ℝ) : ℂ)] := by
  have hM : rhoAlg k a = blockM U w ζ :=
    rhoAlg_eq_blockM k a hpos.invol_eq hU hV
  have hb : rhoAlg k (MonoidAlgebra.single (sr 0 : DihedralGroup n) (1 : ℝ))
      = !![0, 1; 1, 0] := by
    rw [rhoAlg_single, one_smul, rho_apply_sr]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [sandwich_eq_mul a hpos _ hθ hθ', map_mul, map_mul, hb,
    rhoAlg_powElt k a hpos hθ,
    rhoAlg_powElt k a hpos (by linarith : (0 : ℝ) ≤ 1 - θ), hM,
    blockM_cfc_rpow hζ hw, blockM_cfc_rpow hζ hw,
    bpAlpha_one_sub, bpBeta_one_sub]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockS, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    ring

/-! ### Reading the two transforms off the block

`Lyons.rhoAlg_block` puts the frequency sign flip on `U`, so `U^x(k)` is the
**lower-right** entry of the block and `V^x(k)` the upper-right; the upper-left
entry agrees with the lower-right only for self-adjoint arguments. The two entry
lemmas below are therefore unconditional. -/

/-- The rotation transform at `k` is the lower-right entry of the block. -/
theorem Ublock_eq_entry (k : ZMod n) (x : MonoidAlgebra ℝ (DihedralGroup n)) :
    Ublock x k = rhoAlg k x 1 1 := by
  rw [rhoAlg_block]; simp

/-- The reflection transform at `k` is the upper-right entry of the block. -/
theorem Vblock_eq_entry (k : ZMod n) (x : MonoidAlgebra ℝ (DihedralGroup n)) :
    Vblock x k = rhoAlg k x 0 1 := by
  rw [rhoAlg_block]; simp

section Transforms

variable (k : ZMod n) (a : MonoidAlgebra ℝ (DihedralGroup n)) (hpos : IsPos a)
  {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)

include hpos hθ hθ'

/-- The rotation transform of the sandwich, from the lower-right entry. -/
theorem Ublock_sandwich {U w : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hw : 0 ≤ w)
    (hU : ((U : ℝ) : ℂ) = Ublock a k) (hV : Vblock a k = ζ * (w : ℂ)) :
    Ublock (sandwich a (sr 0) θ) k
      = ζ * ((bpAlpha U w θ * bpDelta U w θ : ℝ) : ℂ)
        + conj ζ * ((bpBeta U w θ * bpGamma U w θ : ℝ) : ℂ) := by
  rw [Ublock_eq_entry, rhoAlg_sandwich k a hpos hθ hθ' hζ hw hU hV]
  simp

/-- The reflection transform of the sandwich, from the upper-right entry. -/
theorem Vblock_sandwich {U w : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hw : 0 ≤ w)
    (hU : ((U : ℝ) : ℂ) = Ublock a k) (hV : Vblock a k = ζ * (w : ℂ)) :
    Vblock (sandwich a (sr 0) θ) k
      = ((bpAlpha U w θ * bpGamma U w θ : ℝ) : ℂ)
        + ζ ^ 2 * ((bpBeta U w θ * bpDelta U w θ : ℝ) : ℂ) := by
  rw [Vblock_eq_entry, rhoAlg_sandwich k a hpos hθ hθ' hζ hw hU hV]
  simp

/-- **The sandwich preserves the real part of the reflection transform.**

Both block entries carry the same real factor `αδ + βγ`, which is `w` by the
off-diagonal relation, and `ζ` and `conj ζ` have the same real part — so the
whole expression collapses to `Re(ζ w) = Re V^a(k)`. -/
@[lyons_tag "lem_Re_Q_eq_Re_V"]
theorem re_Ublock_sandwich :
    (Ublock (sandwich a (sr 0) θ) k).re = (Vblock a k).re := by
  obtain ⟨ζ, hζ, hVz⟩ := exists_unit_phase (Vblock a k)
  have hU : (((Ublock a k).re : ℝ) : ℂ) = Ublock a k :=
    Ublock_ofReal_re a hpos.invol_eq k
  have hw : (0 : ℝ) ≤ ‖Vblock a k‖ := norm_nonneg _
  have hwU : ‖Vblock a k‖ ≤ (Ublock a k).re :=
    Ublock_ge_norm_Vblock k a hpos hpos.invol_eq
  have hoff : bpAlpha (Ublock a k).re ‖Vblock a k‖ θ *
        bpDelta (Ublock a k).re ‖Vblock a k‖ θ +
      bpBeta (Ublock a k).re ‖Vblock a k‖ θ *
        bpGamma (Ublock a k).re ‖Vblock a k‖ θ = ‖Vblock a k‖ :=
    bp_rel_off hw hwU
  rw [Ublock_sandwich k a hpos hθ hθ' hζ hw hU hVz]
  conv_rhs => rw [hVz]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, mul_zero, sub_zero]
  linear_combination ζ.re * hoff

/-- **The sandwich transform is dominated.**

The upper-right entry is `αγ + ζ²βδ`; the triangle inequality drops the unit
`ζ²`, and the diagonal relation identifies `αγ + βδ` with `U^a(k)`. -/
@[lyons_tag "lem_absY_le_U"]
theorem norm_Vblock_sandwich_le :
    ‖Vblock (sandwich a (sr 0) θ) k‖ ≤ (Ublock a k).re := by
  obtain ⟨ζ, hζ, hVz⟩ := exists_unit_phase (Vblock a k)
  have hU : (((Ublock a k).re : ℝ) : ℂ) = Ublock a k :=
    Ublock_ofReal_re a hpos.invol_eq k
  have hw : (0 : ℝ) ≤ ‖Vblock a k‖ := norm_nonneg _
  have hwU : ‖Vblock a k‖ ≤ (Ublock a k).re :=
    Ublock_ge_norm_Vblock k a hpos hpos.invol_eq
  obtain ⟨hα, hβ, hγ, hδ⟩ := bp_nonneg hw hwU hθ hθ'
  rw [Vblock_sandwich k a hpos hθ hθ' hζ hw hU hVz]
  calc ‖((bpAlpha (Ublock a k).re ‖Vblock a k‖ θ *
              bpGamma (Ublock a k).re ‖Vblock a k‖ θ : ℝ) : ℂ)
          + ζ ^ 2 * ((bpBeta (Ublock a k).re ‖Vblock a k‖ θ *
              bpDelta (Ublock a k).re ‖Vblock a k‖ θ : ℝ) : ℂ)‖
      ≤ _ + _ := norm_add_le _ _
    _ = bpAlpha (Ublock a k).re ‖Vblock a k‖ θ *
            bpGamma (Ublock a k).re ‖Vblock a k‖ θ +
          bpBeta (Ublock a k).re ‖Vblock a k‖ θ *
            bpDelta (Ublock a k).re ‖Vblock a k‖ θ := by
        rw [norm_mul, norm_pow, hζ, one_pow, one_mul, Complex.norm_real,
          Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hα hγ),
          Real.norm_of_nonneg (mul_nonneg hβ hδ)]
    _ = (Ublock a k).re := bp_rel_diag hw hwU

/-! ### Consequences for the coefficient functions

The two statements above concern the *transforms*; these three pull them back to
the coefficient functions themselves. -/

/-- **The sandwich preserves the even part of the rotation coefficients.**

Equal real parts of the transforms force equal even parts, by injectivity of the
transform. -/
@[lyons_tag "lem_sandwich_even_part"]
theorem evenPart_rotCoeff_sandwich :
    ZMod.evenPart (rotCoeff (sandwich a (sr 0) θ)) = ZMod.evenPart (reflCoeff a) :=
  ZMod.evenPart_eq_of_re_dft_eq (conj_rotCoeff _) (conj_reflCoeff _)
    fun k => re_Ublock_sandwich k a hpos hθ hθ'

/-- **Pairing against a power of the rotation coefficients is unchanged by the
sandwich.**

Stated for an arbitrary natural exponent `p`, not just an odd one: the proof needs
only that `u^a` is even, hence that every power of it is. -/
@[lyons_tag "lem_sandwich_pairing"]
theorem sum_rotCoeff_pow_mul_sandwich (p : ℕ) :
    ∑ j : ZMod n, rotCoeff a j ^ p * rotCoeff (sandwich a (sr 0) θ) j
      = ∑ j : ZMod n, rotCoeff a j ^ p * reflCoeff a j := by
  have heven : ∀ j : ZMod n, rotCoeff a (-j) ^ p = rotCoeff a j ^ p := fun j => by
    rw [(invol_eq_iff_rotCoeff_even a).mp hpos.invol_eq j]
  rw [ZMod.sum_mul_evenPart (fun j => rotCoeff a j ^ p) _ heven,
    ZMod.sum_mul_evenPart (fun j => rotCoeff a j ^ p) (reflCoeff a) heven,
    evenPart_rotCoeff_sandwich a hpos hθ hθ']

/-- **Norm domination for the sandwich.**

`U^a` is a nonnegative real dominating `|V^{x}|` pointwise, which is exactly the
hypothesis of the majorant inequality. -/
@[lyons_tag "lem_sandwich_norm"]
theorem sum_norm_reflCoeff_sandwich_le {m : ℕ} (hm : 1 ≤ m) :
    ∑ j : ZMod n, ‖reflCoeff (sandwich a (sr 0) θ) j‖ ^ (2 * m)
      ≤ ∑ j : ZMod n, ‖rotCoeff a j‖ ^ (2 * m) := by
  have hre := Ublock_ofReal_re a hpos.invol_eq
  have hnn : ∀ k : ZMod n, (0 : ℝ) ≤ (Ublock a k).re := fun k =>
    le_trans (norm_nonneg _) (Ublock_ge_norm_Vblock k a hpos hpos.invol_eq)
  refine ZMod.sum_norm_pow_le _ _ (fun k => ?_) (fun k => ?_) hm
  · change Ublock a k = ((‖Ublock a k‖ : ℝ) : ℂ)
    rw [← hre k, Complex.norm_real, Real.norm_of_nonneg (hnn k)]
  · change ‖Vblock (sandwich a (sr 0) θ) k‖ ≤ ‖Ublock a k‖
    rw [← hre k, Complex.norm_real, Real.norm_of_nonneg (hnn k)]
    exact norm_Vblock_sandwich_le k a hpos hθ hθ'

end Transforms

end Lyons
