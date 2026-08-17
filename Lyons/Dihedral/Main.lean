/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Dihedral.ReflectionStep
import Lyons.Dihedral.Rotation
import Lyons.Walk.Relabel

/-!
# Even-exponent monotonicity on dihedral groups

For rate functions `λ ≤ μ` off the identity on a dihedral group, the centred power sum
`∑_g |p_t^λ(g) - 1/(2n)|^{2m}` is at least as large for `λ` as for `μ`.

The rate is raised one inverse orbit at a time: a rotation increment is central, while a reflection
orbit is a singleton, so its increment is a `RateFn.setAt` and the reflection step applies — at the
distinguished reflection `sr 0` first, then at an arbitrary one by relabelling. The interpolation
between `λ` and `μ` runs by induction on the size of the disagreement set `{g | λ g ≠ μ g}`; one
increment removes a whole inverse orbit from that set, since both rate functions are constant on an
inverse orbit, so the increment lands exactly on `μ` there rather than merely below it.

## Main definitions

* `Lyons.disagree` : the set where two rate functions differ.

## Main results

* `Lyons.Phi_addOrbit_le` : raising the rate on one inverse orbit does not increase
  the power sum.
* `Lyons.Phi_le_of_le` : increasing every rate does not increase the power sum.
* `Lyons.sum_abs_centered_pow_le` : even-exponent monotonicity, in terms of the
  transition probabilities.
-/

open Finset DihedralGroup

namespace Lyons

/-! ### Rate-function bookkeeping -/

section Rate

variable {G : Type*} [Group G] [DecidableEq G]

/-- A rate function is constant on an inverse orbit — that is what symmetry says,
and it is what makes one orbit increment land exactly on the target. -/
theorem RateFn.apply_of_mem_invOrbit (lam : RateFn G) {s g : G}
    (h : g ∈ invOrbit s) : lam g = lam s := by
  rcases mem_invOrbit.mp h with rfl | rfl
  · rfl
  · exact lam.symm s

/-- An involution's inverse orbit is a singleton, so raising the rate on it is a
`RateFn.setAt`. -/
theorem mem_invOrbit_iff_of_inv {s : G} (hs : s⁻¹ = s) {g : G} :
    g ∈ invOrbit s ↔ g = s := by
  rw [mem_invOrbit, hs, or_self]

end Rate

/-! ### One orbit at a time -/

section SingleOrbit

variable {n : ℕ} [NeZero n]

set_option linter.unusedDecidableInType false in
/-- **Raising the rate on one inverse orbit does not increase the power sum.** -/
@[lyons_tag "lem_single_orbit_step"]
theorem Phi_addOrbit_le (lam : RateFn (DihedralGroup n)) {s : DihedralGroup n}
    (hs1 : s ≠ 1) {c : ℝ} (hc : 0 ≤ c) {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (hm : 1 ≤ m) :
    Phi (lam.addOrbit hs1 hc) t m ≤ Phi lam t m := by
  cases s with
  | r j =>
    -- A rotation increment is central; no Duhamel formula needed.
    exact Phi_addOrbit_r_le lam j hs1 hc ht m
  | sr j =>
    -- A reflection increment: relabel `sr 0` to `sr j` and use the reflection step.
    have hsinv : ((sr j : DihedralGroup n))⁻¹ = sr j := rfl
    set φ : DihedralGroup n ≃* DihedralGroup n := relabelAut j with hφ
    have hsb : φ (sr 0 : DihedralGroup n) = sr j := by simp [hφ]
    have hinj : ∀ g : DihedralGroup n, φ g = sr j ↔ g = sr 0 := fun g =>
      ⟨fun h => φ.injective (h.trans hsb.symm), fun h => by rw [h, hsb]⟩
    set lam0 : RateFn (DihedralGroup n) :=
      (lam.comp φ).setAt sr_zero_inv sr_zero_ne_one (le_refl (0 : ℝ)) with hlam0
    have hzero : lam0 (sr 0) = 0 := by
      rw [hlam0, RateFn.setAt_apply_self]
    have hα0 : (0 : ℝ) ≤ lam (sr j) := lam.nonneg _
    have h01 : lam (sr j) ≤ lam (sr j) + c := le_add_of_nonneg_right hc
    have hstep := Phi_setAt_le lam0 hzero ht hm hα0 h01
    -- identify the endpoints of the reflection step with the two rate functions
    have hbase : ∀ g : DihedralGroup n, g ≠ sr 0 → lam0 g = lam (φ g) := by
      intro g hg
      rw [hlam0, RateFn.setAt_apply_of_ne _ _ _ _ hg, RateFn.comp_apply]
    have e1 : lam0.setAt sr_zero_inv sr_zero_ne_one (hα0.trans h01)
        = (lam.addOrbit hs1 hc).comp φ := by
      refine DFunLike.ext _ _ fun g => ?_
      rw [RateFn.comp_apply, RateFn.addOrbit_apply]
      by_cases hg : g = sr 0
      · subst hg
        rw [RateFn.setAt_apply_self, hsb,
          if_pos ((mem_invOrbit_iff_of_inv hsinv).mpr rfl)]
      · rw [RateFn.setAt_apply_of_ne _ _ _ _ hg, hbase g hg,
          if_neg (fun hcon => hg ((hinj g).mp
            ((mem_invOrbit_iff_of_inv hsinv).mp hcon)))]
    have e0 : lam0.setAt sr_zero_inv sr_zero_ne_one hα0 = lam.comp φ := by
      refine DFunLike.ext _ _ fun g => ?_
      by_cases hg : g = sr 0
      · subst hg
        rw [RateFn.setAt_apply_self, RateFn.comp_apply, hsb]
      · rw [RateFn.setAt_apply_of_ne _ _ _ _ hg, hbase g hg, RateFn.comp_apply]
    rw [e1, e0, Phi_comp, Phi_comp] at hstep
    exact hstep

end SingleOrbit

/-! ### Interpolating between ordered rate functions -/

section Induction

variable {n : ℕ} [NeZero n]

set_option linter.unusedDecidableInType false in
/-- The disagreement set of two rate functions. -/
noncomputable def disagree (lam mu : RateFn (DihedralGroup n)) :
    Finset (DihedralGroup n) :=
  open Classical in Finset.univ.filter fun g => lam g ≠ mu g

set_option linter.unusedDecidableInType false in
theorem mem_disagree {lam mu : RateFn (DihedralGroup n)} {g : DihedralGroup n} :
    g ∈ disagree lam mu ↔ lam g ≠ mu g := by
  classical
  simp [disagree]

set_option linter.unusedDecidableInType false in
theorem eq_of_disagree_eq_empty {lam mu : RateFn (DihedralGroup n)}
    (h : disagree lam mu = ∅) : lam = mu := by
  refine DFunLike.ext _ _ fun g => ?_
  by_contra hg
  exact absurd (mem_disagree.mpr hg) (by rw [h]; exact Finset.notMem_empty g)

set_option linter.unusedDecidableInType false in
/-- The induction on the size of the disagreement set. -/
theorem Phi_le_of_le_aux {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (hm : 1 ≤ m) :
    ∀ N : ℕ, ∀ lam mu : RateFn (DihedralGroup n), (∀ g, lam g ≤ mu g) →
      (disagree lam mu).card ≤ N → Phi mu t m ≤ Phi lam t m := by
  intro N
  induction N with
  | zero =>
    intro lam mu _ hcard
    rw [eq_of_disagree_eq_empty (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))]
  | succ N ih =>
    intro lam mu hle hcard
    rcases Finset.eq_empty_or_nonempty (disagree lam mu) with hne | ⟨s, hs⟩
    · rw [eq_of_disagree_eq_empty hne]
    have hsne : lam s ≠ mu s := mem_disagree.mp hs
    have hs1 : s ≠ 1 := fun h => hsne (by rw [h, lam.apply_one, mu.apply_one])
    have hc : (0 : ℝ) ≤ mu s - lam s := by have := hle s; linarith
    set lam' : RateFn (DihedralGroup n) := lam.addOrbit hs1 hc with hlam'
    -- on the raised orbit the increment lands exactly on `mu`
    have horb : ∀ g : DihedralGroup n, g ∈ invOrbit s → lam' g = mu g := by
      intro g hg
      rw [hlam', RateFn.addOrbit_apply, if_pos hg,
        lam.apply_of_mem_invOrbit hg, mu.apply_of_mem_invOrbit hg]
      ring
    have hoff : ∀ g : DihedralGroup n, g ∉ invOrbit s → lam' g = lam g := by
      intro g hg
      rw [hlam', RateFn.addOrbit_apply, if_neg hg]
    have hle' : ∀ g, lam' g ≤ mu g := by
      intro g
      by_cases hg : g ∈ invOrbit s
      · exact le_of_eq (horb g hg)
      · rw [hoff g hg]; exact hle g
    -- the disagreement set has lost the whole orbit of `s`, in particular `s`
    have hsub : disagree lam' mu ⊆ (disagree lam mu).erase s := by
      intro g hg
      have hg' : lam' g ≠ mu g := mem_disagree.mp hg
      have hgo : g ∉ invOrbit s := fun h => hg' (horb g h)
      refine Finset.mem_erase.mpr ⟨fun hcon =>
        hgo (hcon ▸ mem_invOrbit.mpr (Or.inl rfl)), ?_⟩
      exact mem_disagree.mpr (by rw [← hoff g hgo]; exact hg')
    have hcard' : (disagree lam' mu).card ≤ N := by
      have h1 := Finset.card_le_card hsub
      have h2 : ((disagree lam mu).erase s).card = (disagree lam mu).card - 1 :=
        Finset.card_erase_of_mem hs
      have h3 : 1 ≤ (disagree lam mu).card := Finset.card_pos.mpr ⟨s, hs⟩
      omega
    exact (ih lam' mu hle' hcard').trans (Phi_addOrbit_le lam hs1 hc ht hm)

set_option linter.unusedDecidableInType false in
/-- **Increasing every rate does not increase the power sum.**

The hypothesis is `λ_s ≤ μ_s` off the identity; at the identity both are `0`, so the total
inequality the induction runs on follows. -/
@[lyons_tag "lem_orbit_induction"]
theorem Phi_le_of_le (lam mu : RateFn (DihedralGroup n))
    (hle : ∀ g : DihedralGroup n, g ≠ 1 → lam g ≤ mu g) {t : ℝ} (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) : Phi mu t m ≤ Phi lam t m := by
  refine Phi_le_of_le_aux ht hm (disagree lam mu).card lam mu (fun g => ?_) le_rfl
  by_cases hg : g = 1
  · rw [hg, lam.apply_one, mu.apply_one]
  · exact hle g hg

end Induction

/-! ### The theorem -/

section Main

variable {n : ℕ} [NeZero n]

set_option linter.unusedDecidableInType false in
/-- `Lyons.Phi` in the paper's shape: `|p_t^λ(g) - 1/(2n)|^{2m}`, summed. -/
theorem Phi_eq_sum_abs (lam : RateFn (DihedralGroup n)) (t : ℝ) (m : ℕ) :
    Phi lam t m
      = ∑ g : DihedralGroup n, |heatCoeffReal lam t g - (2 * n : ℝ)⁻¹| ^ (2 * m) := by
  rw [Phi_eq_sum_real]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hcard : (Fintype.card (DihedralGroup n) : ℝ) = 2 * n := by
    rw [DihedralGroup.card]; push_cast; ring
  rw [centeredHeatCoeffReal, hcard, pow_mul, ← sq_abs, ← pow_mul]

set_option linter.unusedDecidableInType false in
/-- **Even-exponent monotonicity on dihedral groups.**

`p_t^λ` is `Lyons.heatCoeffReal`, the first column of `exp (-t Δ_λ)`;
`Lyons.heatCoeffReal_nonneg`, `Lyons.sum_heatCoeffReal` and
`Lyons.hasDerivAt_heatCoeffReal_forward` are what license reading it as a transition
probability. -/
@[lyons_tag "thm_main"]
theorem sum_abs_centered_pow_le (lam mu : RateFn (DihedralGroup n))
    (hle : ∀ g : DihedralGroup n, g ≠ 1 → lam g ≤ mu g) {t : ℝ} (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) :
    ∑ g : DihedralGroup n, |heatCoeffReal mu t g - (2 * n : ℝ)⁻¹| ^ (2 * m)
      ≤ ∑ g : DihedralGroup n, |heatCoeffReal lam t g - (2 * n : ℝ)⁻¹| ^ (2 * m) := by
  rw [← Phi_eq_sum_abs, ← Phi_eq_sum_abs]
  exact Phi_le_of_le lam mu hle ht hm

end Main

end Lyons
