/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Dihedral.Rho
import Lyons.Fourier.EvenPart

/-!
# Rotation and reflection coefficients, and the block form of `ρ_k`

The coefficients of an element of the dihedral group algebra split into a rotation part and a
reflection part; their discrete Fourier transforms `U` and `V` assemble `ρ_k(a)` into a `2 × 2`
block.

Mathlib's `sr j` equals `r ^ (-j) * b`, its transform is `𝓕 Φ k = ∑ j, χ(-(j k)) Φ j`, and the
`(0,0)` and `(0,1)` entries of `ρ_k` carry *opposite* characters, so exactly one of the two
transforms picks up a sign flip. With the definitions below it lands on `U`: the `(0,1)` entry is
`V(k)` on the nose and the `(0,0)` entry is `U(-k)`. For self-adjoint `a` the rotation coefficients
are even, so `U(-k) = U(k)` and the flip disappears.

## Main definitions

* `Lyons.rotCoeff`, `Lyons.reflCoeff` : the coefficients of `a` along rotations
  and along reflections.
* `Lyons.Ublock`, `Lyons.Vblock` : their discrete Fourier transforms.

## Main results

* `Lyons.rhoAlg_apply` : `ρ_k` expanded over the group basis.
* `Lyons.rhoAlg_entry_00`, `Lyons.rhoAlg_entry_01`, `Lyons.rhoAlg_entry_10`,
  `Lyons.rhoAlg_entry_11` : the four entries of `ρ_k(a)`.
* `Lyons.rhoAlg_block` : `ρ_k(a) = !![U(-k), V(k); V(-k), U(k)]`.
* `Lyons.invol_eq_iff_rotCoeff_even` : self-adjointness of `a` is evenness of its
  rotation coefficients.
* `Lyons.rhoAlg_block_selfAdjoint` : the Hermitian block form, for self-adjoint `a`.
-/

open Matrix DihedralGroup Finset

namespace Lyons

variable {n : ℕ} [NeZero n]

/-- Coefficients of `a` along the rotations. -/
@[lyons_tag "def_rot_coeff"]
noncomputable def rotCoeff (a : MonoidAlgebra ℝ (DihedralGroup n)) : ZMod n → ℂ :=
  fun j => (co a (.r j) : ℂ)

/-- Coefficients of `a` along the reflections, that is, `a_{sr j}`. -/
@[lyons_tag "def_refl_coeff"]
noncomputable def reflCoeff (a : MonoidAlgebra ℝ (DihedralGroup n)) : ZMod n → ℂ :=
  fun j => (co a (.sr j) : ℂ)

omit [NeZero n] in
/-- The rotation coefficients are real: they are coefficients of an element of
the *real* group algebra. -/
@[simp] theorem conj_rotCoeff (a : MonoidAlgebra ℝ (DihedralGroup n)) (j : ZMod n) :
    (starRingEnd ℂ) (rotCoeff a j) = rotCoeff a j := Complex.conj_ofReal _

omit [NeZero n] in
/-- The reflection coefficients are real, for the same reason. -/
@[simp] theorem conj_reflCoeff (a : MonoidAlgebra ℝ (DihedralGroup n)) (j : ZMod n) :
    (starRingEnd ℂ) (reflCoeff a j) = reflCoeff a j := Complex.conj_ofReal _

/-- The transform of the rotation coefficients. -/
@[lyons_tag "def_block_transforms"]
noncomputable def Ublock (a : MonoidAlgebra ℝ (DihedralGroup n)) : ZMod n → ℂ :=
  ZMod.dft (rotCoeff a)

/-- The transform of the reflection coefficients. -/
@[lyons_tag "def_block_transforms"]
noncomputable def Vblock (a : MonoidAlgebra ℝ (DihedralGroup n)) : ZMod n → ℂ :=
  ZMod.dft (reflCoeff a)

/-- `ρ_k` expanded over the group basis. -/
theorem rhoAlg_apply (k : ZMod n) (a : MonoidAlgebra ℝ (DihedralGroup n)) :
    rhoAlg k a = ∑ g : DihedralGroup n, co a g • rho k g := by
  classical
  conv_lhs => rw [basis_expansion a]
  rw [map_sum]
  exact Finset.sum_congr rfl fun g _ ↦ rhoAlg_single k g (co a g)

/-- Splitting a sum over the dihedral group into rotations and reflections. -/
theorem sum_dihedral {M : Type*} [AddCommMonoid M] (F : DihedralGroup n → M) :
    ∑ g : DihedralGroup n, F g
      = (∑ j : ZMod n, F (.r j)) + ∑ j : ZMod n, F (.sr j) := by
  classical
  rw [Fintype.sum_equiv DihedralGroup.equivSum F
    (fun s => F (DihedralGroup.equivSum.symm s))
    (fun g => by rw [Equiv.symm_apply_apply])]
  rw [Fintype.sum_sum_type]
  rfl

/-! ### Entries of `ρ_k` on basis elements -/

@[simp] theorem rho_r_00 (k j : ZMod n) :
    rho k (.r j) 0 0 = (ZMod.stdAddChar (k * j) : ℂ) := by rw [rho_apply_r]; simp
@[simp] theorem rho_r_01 (k j : ZMod n) : rho k (.r j) 0 1 = 0 := by
  rw [rho_apply_r]; simp
@[simp] theorem rho_r_10 (k j : ZMod n) : rho k (.r j) 1 0 = 0 := by
  rw [rho_apply_r]; simp
@[simp] theorem rho_r_11 (k j : ZMod n) :
    rho k (.r j) 1 1 = (ZMod.stdAddChar (-(k * j)) : ℂ) := by rw [rho_apply_r]; simp
@[simp] theorem rho_sr_00 (k j : ZMod n) : rho k (.sr j) 0 0 = 0 := by
  rw [rho_apply_sr]; simp
@[simp] theorem rho_sr_01 (k j : ZMod n) :
    rho k (.sr j) 0 1 = (ZMod.stdAddChar (-(k * j)) : ℂ) := by rw [rho_apply_sr]; simp
@[simp] theorem rho_sr_10 (k j : ZMod n) :
    rho k (.sr j) 1 0 = (ZMod.stdAddChar (k * j) : ℂ) := by rw [rho_apply_sr]; simp
@[simp] theorem rho_sr_11 (k j : ZMod n) : rho k (.sr j) 1 1 = 0 := by
  rw [rho_apply_sr]; simp

/-- Entry `(1,1)` of `ρ_k(a)` is `U(k)`. -/
theorem rhoAlg_entry_11 (k : ZMod n) (a : MonoidAlgebra ℝ (DihedralGroup n)) :
    rhoAlg k a 1 1 = Ublock a k := by
  classical
  rw [rhoAlg_apply, Matrix.sum_apply, Ublock, ZMod.dft_apply,
    sum_dihedral (fun g => (co a g • rho k g) 1 1)]
  simp only [Matrix.smul_apply, rho_sr_11, smul_zero, Finset.sum_const_zero, add_zero,
    rho_r_11, rotCoeff, Complex.real_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_comm ((co a (DihedralGroup.r j) : ℂ))]
  congr 2
  ring

/-- Entry `(0,0)` of `ρ_k(a)` is `U(-k)`. -/
theorem rhoAlg_entry_00 (k : ZMod n) (a : MonoidAlgebra ℝ (DihedralGroup n)) :
    rhoAlg k a 0 0 = Ublock a (-k) := by
  classical
  rw [rhoAlg_apply, Matrix.sum_apply, Ublock, ZMod.dft_apply,
    sum_dihedral (fun g => (co a g • rho k g) 0 0)]
  simp only [Matrix.smul_apply, rho_sr_00, smul_zero, Finset.sum_const_zero, add_zero,
    rho_r_00, rotCoeff, Complex.real_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_comm ((co a (DihedralGroup.r j) : ℂ))]
  congr 2
  ring

/-- Entry `(0,1)` of `ρ_k(a)` is `V(k)`. -/
theorem rhoAlg_entry_01 (k : ZMod n) (a : MonoidAlgebra ℝ (DihedralGroup n)) :
    rhoAlg k a 0 1 = Vblock a k := by
  classical
  rw [rhoAlg_apply, Matrix.sum_apply, Vblock, ZMod.dft_apply,
    sum_dihedral (fun g => (co a g • rho k g) 0 1)]
  simp only [Matrix.smul_apply, rho_r_01, smul_zero, Finset.sum_const_zero, zero_add,
    rho_sr_01, reflCoeff, Complex.real_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_comm ((co a (DihedralGroup.sr j) : ℂ))]
  congr 2
  ring

/-- Entry `(1,0)` of `ρ_k(a)` is `V(-k)`. -/
theorem rhoAlg_entry_10 (k : ZMod n) (a : MonoidAlgebra ℝ (DihedralGroup n)) :
    rhoAlg k a 1 0 = Vblock a (-k) := by
  classical
  rw [rhoAlg_apply, Matrix.sum_apply, Vblock, ZMod.dft_apply,
    sum_dihedral (fun g => (co a g • rho k g) 1 0)]
  simp only [Matrix.smul_apply, rho_r_10, smul_zero, Finset.sum_const_zero, zero_add,
    rho_sr_10, reflCoeff, Complex.real_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_comm ((co a (DihedralGroup.sr j) : ℂ))]
  congr 2
  ring

/-- **The block form of `ρ_k`**, valid for every `a` (no self-adjointness needed):
the sign flip sits on `U`. -/
theorem rhoAlg_block (k : ZMod n) (a : MonoidAlgebra ℝ (DihedralGroup n)) :
    rhoAlg k a = !![Ublock a (-k), Vblock a k; Vblock a (-k), Ublock a k] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rhoAlg_entry_00, rhoAlg_entry_01, rhoAlg_entry_10, rhoAlg_entry_11]

/-! ### Self-adjointness in coordinates -/

omit [NeZero n] in
/-- **Self-adjointness is evenness of the rotation coefficients.** The reflection
coefficients carry no condition, because every reflection is its own inverse. -/
@[lyons_tag "lem_selfadjoint_coords"]
theorem invol_eq_iff_rotCoeff_even (a : MonoidAlgebra ℝ (DihedralGroup n)) :
    invol a = a ↔ ∀ j : ZMod n, rotCoeff a (-j) = rotCoeff a j := by
  constructor
  · intro h j
    have h2 := congrArg (fun x => co x (DihedralGroup.r j)) h
    simp only [co_invol,
      show (DihedralGroup.r j)⁻¹ = DihedralGroup.r (-j) from rfl] at h2
    rw [rotCoeff, rotCoeff]
    exact_mod_cast h2
  · intro h
    refine co_injective fun g ↦ ?_
    cases g with
    | r j =>
      rw [co_invol, show (DihedralGroup.r j)⁻¹ = DihedralGroup.r (-j) from rfl]
      have := h j
      rw [rotCoeff, rotCoeff] at this
      exact_mod_cast this
    | sr j =>
      rw [co_invol, show (DihedralGroup.sr j)⁻¹ = DihedralGroup.sr j from rfl]

/-! ### Behaviour of the transforms under negating the frequency -/

/-- The rotation transform is even when `a` is self-adjoint. -/
theorem Ublock_neg (a : MonoidAlgebra ℝ (DihedralGroup n)) (hsa : invol a = a)
    (k : ZMod n) : Ublock a (-k) = Ublock a k :=
  ZMod.dft_neg_of_even ((invol_eq_iff_rotCoeff_even a).mp hsa) k

/-- The reflection transform conjugates under negating the frequency, because
the reflection coefficients are real. -/
theorem Vblock_neg (a : MonoidAlgebra ℝ (DihedralGroup n)) (k : ZMod n) :
    Vblock a (-k) = (starRingEnd ℂ) (Vblock a k) := by
  refine ZMod.dft_neg_of_real (fun j => ?_) k
  rw [reflCoeff]
  exact Complex.conj_ofReal _

/-- The rotation transform of a self-adjoint element is fixed by conjugation:
the coefficients are real, which conjugates the transform, and even, which
negates the frequency, and for `U` the two effects coincide. -/
theorem Ublock_conj (a : MonoidAlgebra ℝ (DihedralGroup n)) (hsa : invol a = a)
    (k : ZMod n) : (starRingEnd ℂ) (Ublock a k) = Ublock a k := by
  have hreal : Ublock a (-k) = (starRingEnd ℂ) (Ublock a k) := by
    refine ZMod.dft_neg_of_real (fun j => ?_) k
    rw [rotCoeff]
    exact Complex.conj_ofReal _
  rw [← hreal, Ublock_neg a hsa]

/-- Hence it *is* its own real part. -/
theorem Ublock_ofReal_re (a : MonoidAlgebra ℝ (DihedralGroup n)) (hsa : invol a = a)
    (k : ZMod n) : (((Ublock a k).re : ℝ) : ℂ) = Ublock a k :=
  Complex.conj_eq_iff_re.mp (Ublock_conj a hsa k)

/-- **The Hermitian block form** for self-adjoint `a`: the sign flip on `U` is
absorbed by evenness, and the lower-left entry is the conjugate of the
upper-right. -/
@[lyons_tag "lem_rho_block"]
theorem rhoAlg_block_selfAdjoint (k : ZMod n)
    (a : MonoidAlgebra ℝ (DihedralGroup n)) (hsa : invol a = a) :
    rhoAlg k a
      = !![Ublock a k, Vblock a k; (starRingEnd ℂ) (Vblock a k), Ublock a k] := by
  rw [rhoAlg_block, Ublock_neg a hsa, Vblock_neg a]

end Lyons
