/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Contract
import Lyons.Dihedral.Relabel

/-!
# Rotation increments are central

For a rotation `s` the increment `ζ_s` is central in the real group algebra of `D_n`; reflections
have no such property. Conjugation in `D_n` sends `r k` to `r k` (by a rotation) or to `r (-k)`
(by a reflection), and `{r k, r (-k)}` is exactly the inverse orbit of `r k`, so conjugation
permutes the orbit and a sum over it is conjugation-invariant.

## Main definitions

* `Lyons.orbitSum`: the sum, in the group algebra, of the elements of an inverse orbit.

## Main results

* `Lyons.conj_r`: conjugation fixes an inverse orbit of rotations setwise.
* `Lyons.orbitElt_central_r`: `ζ_{r k}` commutes with everything.
-/

open Finset DihedralGroup

namespace Lyons

variable {n : ℕ}

theorem conj_r (g : DihedralGroup n) (k : ZMod n) :
    g * DihedralGroup.r k * g⁻¹ = DihedralGroup.r k ∨
      g * DihedralGroup.r k * g⁻¹ = DihedralGroup.r (-k) := by
  cases g with
  | r l =>
    left
    rw [show (DihedralGroup.r l)⁻¹ = DihedralGroup.r (-l) from rfl, r_mul_r, r_mul_r]
    congr 1; ring
  | sr l =>
    right
    rw [show (DihedralGroup.sr l)⁻¹ = DihedralGroup.sr l from rfl, sr_mul_r, sr_mul_sr]
    congr 1; ring

variable [NeZero n]

omit [NeZero n] in
theorem conj_mem_invOrbit_r {k : ZMod n} {a : DihedralGroup n}
    (ha : a ∈ invOrbit (DihedralGroup.r k)) (g : DihedralGroup n) :
    g * a * g⁻¹ ∈ invOrbit (DihedralGroup.r k) := by
  have hinv : (DihedralGroup.r k)⁻¹ = DihedralGroup.r (-k) := rfl
  rcases mem_invOrbit.mp ha with rfl | rfl
  · rcases conj_r g k with h | h
    · exact mem_invOrbit.mpr (Or.inl h)
    · exact mem_invOrbit.mpr (Or.inr (by rw [hinv]; exact h))
  · rw [hinv]
    rcases conj_r g (-k) with h | h
    · exact mem_invOrbit.mpr (Or.inr (by rw [hinv]; exact h))
    · exact mem_invOrbit.mpr (Or.inl (by rw [neg_neg] at h; exact h))

noncomputable def orbitSum (s : DihedralGroup n) : MonoidAlgebra ℝ (DihedralGroup n) :=
  ∑ a ∈ invOrbit s, MonoidAlgebra.single a (1 : ℝ)

omit [NeZero n] in
theorem co_orbitSum (s g : DihedralGroup n) :
    co (orbitSum s) g = if g ∈ invOrbit s then 1 else 0 := by
  classical
  rw [orbitSum, co_sum]
  by_cases hg : g ∈ invOrbit s
  · rw [if_pos hg, Finset.sum_eq_single g]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hcon; exact absurd hg hcon
  · rw [if_neg hg, Finset.sum_eq_zero]
    intro b hb
    have hne : g ≠ b := fun hcon => hg (by rw [hcon]; exact hb)
    simp [hne]

theorem orbitSum_central_r (k : ZMod n) (y : MonoidAlgebra ℝ (DihedralGroup n)) :
    orbitSum (DihedralGroup.r k) * y = y * orbitSum (DihedralGroup.r k) := by
  classical
  refine co_injective fun g ↦ ?_
  rw [co_mul', co_mul]
  have hL : ∀ u : DihedralGroup n,
      co (orbitSum (DihedralGroup.r k)) u * co y (u⁻¹ * g)
        = if u ∈ invOrbit (DihedralGroup.r k) then co y (u⁻¹ * g) else 0 := by
    intro u; rw [co_orbitSum]; by_cases h : u ∈ invOrbit (DihedralGroup.r k) <;> simp [h]
  have hR : ∀ h' : DihedralGroup n,
      co y (g * h'⁻¹) * co (orbitSum (DihedralGroup.r k)) h'
        = if h' ∈ invOrbit (DihedralGroup.r k) then co y (g * h'⁻¹) else 0 := by
    intro h'; rw [co_orbitSum]; by_cases h : h' ∈ invOrbit (DihedralGroup.r k) <;> simp [h]
  rw [Finset.sum_congr rfl fun u _ ↦ hL u, Finset.sum_congr rfl fun h' _ ↦ hR h',
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_ite_mem, Finset.univ_inter]
  refine Finset.sum_nbij' (fun u => g⁻¹ * u * g) (fun h' => g * h' * g⁻¹)
    (fun a ha => by simpa using conj_mem_invOrbit_r ha g⁻¹)
    (fun a ha => conj_mem_invOrbit_r ha g)
    (fun a _ => by group) (fun a _ => by group) (fun a _ => ?_)
  congr 1
  group

omit [NeZero n] in
/-- The orbit element is a multiple of `1` minus the orbit sum. -/
theorem orbitElt_eq (s : DihedralGroup n) :
    orbitElt s = (invOrbit s).card • (1 : MonoidAlgebra ℝ (DihedralGroup n))
      - orbitSum s := by
  rw [orbitElt, orbitSum, Finset.sum_sub_distrib, Finset.sum_const]

/-- **Rotation increments are central.** -/
@[lyons_tag "lem_rotation_central"]
theorem orbitElt_central_r (k : ZMod n) (y : MonoidAlgebra ℝ (DihedralGroup n)) :
    orbitElt (DihedralGroup.r k) * y = y * orbitElt (DihedralGroup.r k) := by
  rw [orbitElt_eq, sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
    orbitSum_central_r]

end Lyons
