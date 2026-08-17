/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Dihedral.Reflection
import Lyons.Walk.ReflectionDeriv

/-!
# The reflection step

Raising the rate on a reflection does not increase the centred power sum. Differentiating the power
sum in the reflection rate `α` produces a Duhamel integral over `θ ∈ [0,1]` whose integrand is the
sandwich `a^θ · b · a^{1-θ}`, and the reflection inequality makes that integral nonpositive.

`RateFn.setAt` carries `0 ≤ α` as a proof argument, so `α ↦ Φ_m(λ[b↦α], t)` is not a function of
`α`; the differentiation runs instead on `Lyons.reflPhi`, which is total in `α` and agrees with
`Lyons.Phi` for `α ≥ 0`. The base rate is required to vanish at the reflection, since
`Lyons.reflLap` *adds* `α • ζ_b` where `RateFn.setAt` *overwrites*.

The sign statement is indexed by `p` with `m = p + 1`, which keeps truncated natural subtraction
out of the exponents; `Lyons.antitoneOn_reflPhi` converts back to `1 ≤ m`.

## Main definitions

* `Lyons.reflCentCo`, `Lyons.reflPhi` : the centred coefficient and the centred
  power sum, as total functions of the reflection rate.
* `Lyons.duhamelIntegrand` : the integrand of the Duhamel formula.

## Main results

* `Lyons.reflHeatMat_sandwich` : the Duhamel integrand is the sandwich, endpoints
  included.
* `Lyons.reflPhi_eq` : `reflPhi` agrees with `Lyons.Phi` for a nonnegative rate.
* `Lyons.hasDerivAt_reflPhi` : the derivative of the power sum in the rate.
* `Lyons.differentiableAt_reflPhi`, `Lyons.deriv_reflPhi_nonpos` : the power sum is
  differentiable in a reflection rate, with nonpositive derivative.
* `Lyons.Phi_setAt_le` : increasing a reflection rate does not increase the power
  sum.
-/

open Matrix Finset DihedralGroup
open scoped Norms.Operator MatrixOrder ComplexOrder

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### Absorption on the right -/

set_option linter.unusedDecidableInType false in
theorem single_mul_uniform (b : G) :
    MonoidAlgebra.single b (1 : ℝ) * uniform G = uniform G := by
  classical
  rw [uniform_absorb]
  have h : ∑ g : G, co (MonoidAlgebra.single b (1 : ℝ)) g = 1 := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc; simp [hc]
    · intro hcon; exact absurd (Finset.mem_univ b) hcon
  rw [h, one_smul]

set_option linter.unusedDecidableInType false in
theorem L_single_mul_L_uniform (b : G) :
    L (MonoidAlgebra.single b (1 : ℝ)) * L (uniform G) = L (uniform G) := by
  rw [← L_mul, single_mul_uniform]

set_option linter.unusedDecidableInType false in
theorem centeredElt_mul_uniform (lam : RateFn G) (t : ℝ) :
    centeredElt lam t * uniform G = 0 := by
  rw [centeredElt, sub_mul, heatElt_mul_uniform, uniform_idem, sub_self]

set_option linter.unusedDecidableInType false in
theorem uniform_mul_centeredElt (lam : RateFn G) (t : ℝ) :
    uniform G * centeredElt lam t = 0 := by
  rw [centeredElt, mul_sub, uniform_mul_heatElt, uniform_idem, sub_self]

/-! ### The functional calculus at the two endpoints -/

omit [Group G] in
theorem mpow_zero {M : Matrix G G ℂ} (hM : IsSelfAdjoint M) : mpow M 0 = 1 := by
  rw [mpow, show (fun t : ℝ => t ^ (0 : ℝ)) = (fun _ : ℝ => (1 : ℝ)) from
    funext fun t => Real.rpow_zero t, cfc_const (1 : ℝ) M hM, map_one]

omit [Group G] in
theorem mpow_one {M : Matrix G G ℂ} (hM : IsSelfAdjoint M) : mpow M 1 = M := by
  rw [mpow, show (fun t : ℝ => t ^ (1 : ℝ)) = (id : ℝ → ℝ) from
    funext fun t => Real.rpow_one t, cfc_id ℝ M hM]

/-! ### The Duhamel integrand is the sandwich, endpoints included -/

set_option linter.unusedDecidableInType false in
theorem L_uniform_mul_L_centeredElt (lam : RateFn G) (t : ℝ) :
    L (uniform G) * L (centeredElt lam t) = 0 := by
  rw [← L_mul, uniform_mul_centeredElt, L_zero]

set_option linter.unusedDecidableInType false in
theorem L_centeredElt_mul_L_uniform (lam : RateFn G) (t : ℝ) :
    L (centeredElt lam t) * L (uniform G) = 0 := by
  rw [← L_mul, centeredElt_mul_uniform, L_zero]

theorem reflHeatMat_zero (lam0 : RateFn G) (b : G) (α : ℝ) :
    reflHeatMat lam0 b 0 α = 1 := by
  rw [reflHeatMat, neg_zero, zero_smul, NormedSpace.exp_zero]

theorem isSelfAdjoint_L_centeredElt (lam : RateFn G) (t : ℝ) :
    IsSelfAdjoint (L (centeredElt lam t)) :=
  (Matrix.nonneg_iff_posSemidef.mp ((isPos_iff_le _).mp (centeredElt_isPos lam t))).isHermitian

/-- **The Duhamel integrand is the sandwich, for every `θ ∈ [0,1]`.**

At `θ = 0` and `θ = 1` the two sides' *factors* differ — `a_α^0 = 1`, not `1 - P` —
yet the products agree, because the discrepancy is a multiple of `P` and `P` is
annihilated by `L a_α` on either side. -/
theorem reflHeatMat_sandwich (lam0 : RateFn G) {b : G} (hb : b⁻¹ = b) (hb1 : b ≠ 1)
    (hzero : lam0 b = 0) {α : ℝ} (hα : 0 ≤ α) (t : ℝ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (reflHeatMat lam0 b (θ * t) α * (1 - L (uniform G)))
        * L (MonoidAlgebra.single b (1 : ℝ))
        * (reflHeatMat lam0 b ((1 - θ) * t) α * (1 - L (uniform G)))
      = L (sandwich (centeredElt (lam0.setAt hb hb1 hα) t) b θ) := by
  set a := centeredElt (lam0.setAt hb hb1 hα) t with ha
  have hpos : IsPos a := centeredElt_isPos _ _
  have hsa : IsSelfAdjoint (L a) := isSelfAdjoint_L_centeredElt _ _
  have hLa : reflHeatMat lam0 b t α * (1 - L (uniform G)) = L a := by
    rw [reflHeatMat_eq lam0 hb hb1 hzero hα, ← L_centeredElt_eq_mul]
  have hPa : L (uniform G) * L a = 0 := L_uniform_mul_L_centeredElt _ _
  have haP : L a * L (uniform G) = 0 := L_centeredElt_mul_L_uniform _ _
  rw [L_sandwich a hpos b hθ0 hθ1, sandwichMat]
  rcases eq_or_lt_of_le hθ0 with hθe | hθp
  · rw [← hθe]
    simp only [zero_mul, sub_zero, one_mul, reflHeatMat_zero, mpow_zero hsa,
      mpow_one hsa]
    rw [hLa, sub_mul, one_mul, sub_mul, L_uniform_mul_L_single, hPa, sub_zero]
  · rcases eq_or_lt_of_le hθ1 with hθe | hθp'
    · rw [hθe]
      simp only [sub_self, zero_mul, one_mul, mul_one, reflHeatMat_zero,
        mpow_zero hsa, mpow_one hsa]
      rw [hLa, mul_sub, mul_one, mul_assoc (L a) _ (L (uniform G)),
        L_single_mul_L_uniform, haP, sub_zero]
    · rw [reflHeatMat_mul_compl_eq_powElt lam0 hb hb1 hzero hα t hθp,
        reflHeatMat_mul_compl_eq_powElt lam0 hb hb1 hzero hα t
          (show (0 : ℝ) < 1 - θ by linarith),
        L_powElt a hpos hθ0, L_powElt a hpos (show (0 : ℝ) ≤ 1 - θ by linarith)]

/-! ### The power sum as a total function of the reflection rate -/

/-- The centred coefficient, as a total function of the reflection rate. -/
noncomputable def reflCentCo (lam0 : RateFn G) (b : G) (t α : ℝ) (g : G) : ℝ :=
  ((reflHeatMat lam0 b t α * (1 - L (uniform G))) g 1).re

set_option linter.unusedDecidableInType false in
theorem reflCentCo_eq (lam0 : RateFn G) {b : G} (hb : b⁻¹ = b) (hb1 : b ≠ 1)
    (hzero : lam0 b = 0) {α : ℝ} (hα : 0 ≤ α) (t : ℝ) (g : G) :
    reflCentCo lam0 b t α g = co (centeredElt (lam0.setAt hb hb1 hα) t) g := by
  rw [reflCentCo, reflHeatMat_eq lam0 hb hb1 hzero hα, ← L_centeredElt_eq_mul, L_apply]
  simp

/-- The centred power sum, as a total function of the reflection rate. -/
noncomputable def reflPhi (lam0 : RateFn G) (b : G) (t : ℝ) (m : ℕ) (α : ℝ) : ℝ :=
  ∑ g : G, reflCentCo lam0 b t α g ^ (2 * m)

set_option linter.unusedDecidableInType false in
theorem reflPhi_eq (lam0 : RateFn G) {b : G} (hb : b⁻¹ = b) (hb1 : b ≠ 1)
    (hzero : lam0 b = 0) {α : ℝ} (hα : 0 ≤ α) (t : ℝ) (m : ℕ) :
    reflPhi lam0 b t m α = Phi (lam0.setAt hb hb1 hα) t m := by
  rw [Phi_eq_sum_real, reflPhi]
  exact Finset.sum_congr rfl fun g _ => by
    rw [reflCentCo_eq lam0 hb hb1 hzero hα, co_centeredElt]

/-- The integrand of the Duhamel formula of
`Lyons.hasDerivAt_reflCentered_integral`. -/
noncomputable def duhamelIntegrand (lam0 : RateFn G) (b : G) (t α θ : ℝ) :
    Matrix G G ℂ :=
  (reflHeatMat lam0 b (θ * t) α * (1 - L (uniform G)))
      * L (MonoidAlgebra.single b (1 : ℝ))
      * (reflHeatMat lam0 b ((1 - θ) * t) α * (1 - L (uniform G)))
    - reflHeatMat lam0 b t α * (1 - L (uniform G))

theorem continuous_duhamelIntegrand (lam0 : RateFn G) (b : G) (t α : ℝ) :
    Continuous (duhamelIntegrand lam0 b t α) := by
  have h1 : Continuous fun θ : ℝ => reflHeatMat lam0 b (θ * t) α :=
    (continuous_reflExp lam0 b α (-t) 0).congr fun θ => by
      rw [reflHeatMat]; congr 2; ring
  have h2 : Continuous fun θ : ℝ => reflHeatMat lam0 b ((1 - θ) * t) α :=
    (continuous_reflExp lam0 b α t (-t)).congr fun θ => by
      rw [reflHeatMat]; congr 2; ring
  exact (((h1.mul continuous_const).mul continuous_const).mul
    (h2.mul continuous_const)).sub continuous_const

omit [Group G] in
/-- Reading one real entry off a matrix, as a continuous `ℝ`-linear map. -/
noncomputable def entryReCLM (g h : G) : Matrix G G ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (entryCLM g h)

omit [Group G] [Fintype G] [DecidableEq G] in
@[simp] theorem entryReCLM_apply (g h : G) (M : Matrix G G ℂ) :
    entryReCLM g h M = (M g h).re := rfl

/-! ### Differentiating the power sum -/

theorem hasDerivAt_reflCentCo (lam0 : RateFn G) {b : G} (hb : b⁻¹ = b) (t α : ℝ)
    (g : G) :
    HasDerivAt (fun a : ℝ => reflCentCo lam0 b t a g)
      (((t • ∫ θ in (0:ℝ)..1, duhamelIntegrand lam0 b t α θ) g 1).re) α :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt α
    ((entryCLM g 1).hasFDerivAt.comp_hasDerivAt α
      (hasDerivAt_reflCentered_integral lam0 hb t α))

theorem hasDerivAt_reflPhi (lam0 : RateFn G) {b : G} (hb : b⁻¹ = b) (t α : ℝ)
    (m : ℕ) :
    HasDerivAt (fun a : ℝ => reflPhi lam0 b t m a)
      (∑ g : G, ((2 * m : ℕ) : ℝ) * reflCentCo lam0 b t α g ^ (2 * m - 1)
        * ((t • ∫ θ in (0:ℝ)..1, duhamelIntegrand lam0 b t α θ) g 1).re) α := by
  have h : ∀ g ∈ (Finset.univ : Finset G),
      HasDerivAt (fun a : ℝ => reflCentCo lam0 b t a g ^ (2 * m))
        (((2 * m : ℕ) : ℝ) * reflCentCo lam0 b t α g ^ (2 * m - 1)
          * ((t • ∫ θ in (0:ℝ)..1, duhamelIntegrand lam0 b t α θ) g 1).re) α :=
    fun g _ => (hasDerivAt_reflCentCo lam0 hb t α g).pow (2 * m)
  have hsum := HasDerivAt.sum h
  have hfun : (∑ g : G, fun a : ℝ => reflCentCo lam0 b t a g ^ (2 * m))
      = fun a : ℝ => reflPhi lam0 b t m a := by
    funext a; simp [reflPhi, Finset.sum_apply]
  rwa [hfun] at hsum

/-! ### The sign of the derivative -/

set_option linter.unusedDecidableInType false in
/-- **The derivative is nonpositive**, given the pointwise reflection inequality
`key` on all of `Set.Icc 0 1`. -/
theorem sum_reflCentCo_pow_mul_deriv_nonpos (lam0 : RateFn G) {b : G} (hb : b⁻¹ = b)
    (hb1 : b ≠ 1) (hzero : lam0 b = 0) {α : ℝ} (hα : 0 ≤ α) {t : ℝ} (ht : 0 ≤ t)
    (p : ℕ)
    (key : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∑ g : G, co (centeredElt (lam0.setAt hb hb1 hα) t) g ^ (2 * p + 1)
          * co (sandwich (centeredElt (lam0.setAt hb hb1 hα) t) b θ) g
        ≤ ∑ g : G, co (centeredElt (lam0.setAt hb hb1 hα) t) g ^ (2 * p + 2)) :
    ∑ g : G, reflCentCo lam0 b t α g ^ (2 * p + 1)
        * ((t • ∫ θ in (0:ℝ)..1, duhamelIntegrand lam0 b t α θ) g 1).re ≤ 0 := by
  set a := centeredElt (lam0.setAt hb hb1 hα) t with ha
  set F := duhamelIntegrand lam0 b t α with hFdef
  have hFc : Continuous F := continuous_duhamelIntegrand lam0 b t α
  have hFre : ∀ g : G, Continuous fun θ : ℝ => (F θ g 1).re := fun g =>
    (entryReCLM g (1 : G)).continuous.comp hFc
  have hval : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ g : G,
      (F θ g 1).re = co (sandwich a b θ) g - co a g := by
    intro θ hθ0 hθ1 g
    have h2 : reflHeatMat lam0 b t α * (1 - L (uniform G)) = L a := by
      rw [ha, reflHeatMat_eq lam0 hb hb1 hzero hα, ← L_centeredElt_eq_mul]
    rw [hFdef, duhamelIntegrand,
      reflHeatMat_sandwich lam0 hb hb1 hzero hα t hθ0 hθ1, ← ha, h2]
    simp
  have hsmul : ∀ g : G, ((t • ∫ θ in (0:ℝ)..1, F θ) g 1).re
      = t * ∫ θ in (0:ℝ)..1, (F θ g 1).re := by
    intro g
    have hc : ((∫ θ in (0:ℝ)..1, F θ) g 1).re = ∫ θ in (0:ℝ)..1, (F θ g 1).re :=
      ((entryReCLM g (1 : G)).intervalIntegral_comp_comm (f := F)
        (μ := MeasureTheory.volume) (hFc.intervalIntegrable 0 1)).symm
    rw [Matrix.smul_apply, Complex.smul_re, hc, smul_eq_mul]
  have hint : ∀ g ∈ (Finset.univ : Finset G), IntervalIntegrable
      (fun θ : ℝ => co a g ^ (2 * p + 1) * (F θ g 1).re) MeasureTheory.volume 0 1 :=
    fun g _ => (continuous_const.mul (hFre g)).intervalIntegrable 0 1
  have hstep : ∑ g : G, reflCentCo lam0 b t α g ^ (2 * p + 1)
        * ((t • ∫ θ in (0:ℝ)..1, F θ) g 1).re
      = t * ∫ θ in (0:ℝ)..1, ∑ g : G, co a g ^ (2 * p + 1) * (F θ g 1).re := by
    rw [intervalIntegral.integral_finsetSum hint, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hsmul g, reflCentCo_eq lam0 hb hb1 hzero hα, ← ha,
      intervalIntegral.integral_const_mul]
    ring
  have hbig : Continuous fun θ : ℝ => ∑ g : G, co a g ^ (2 * p + 1) * (F θ g 1).re :=
    continuous_finsetSum _ fun g _ => continuous_const.mul (hFre g)
  have hptwise : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      (∑ g : G, co a g ^ (2 * p + 1) * (F θ g 1).re) ≤ (fun _ : ℝ => (0 : ℝ)) θ := by
    intro θ hθ
    have hbracket : ∑ g : G, co a g ^ (2 * p + 1) * (F θ g 1).re
        = (∑ g : G, co a g ^ (2 * p + 1) * co (sandwich a b θ) g)
          - ∑ g : G, co a g ^ (2 * p + 2) := by
      rw [Finset.sum_congr rfl fun g _ => by
            rw [hval θ hθ.1 hθ.2 g, mul_sub,
              show co a g ^ (2 * p + 1) * co a g = co a g ^ (2 * p + 2) by ring],
        Finset.sum_sub_distrib]
    rw [hbracket]
    have := key θ hθ.1 hθ.2
    simpa using by linarith
  have hle : (∫ θ in (0:ℝ)..1, ∑ g : G, co a g ^ (2 * p + 1) * (F θ g 1).re) ≤ 0 := by
    have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      zero_le_one (hbig.intervalIntegrable 0 1)
      ((continuous_const (y := (0:ℝ))).intervalIntegrable (0:ℝ) 1) hptwise
    simpa using hmono
  rw [hstep]
  exact mul_nonpos_of_nonneg_of_nonpos ht hle

/-! ### The reflection step on a dihedral group -/

section Dihedral

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem sr_zero_inv : ((sr 0 : DihedralGroup n))⁻¹ = sr 0 := rfl

omit [NeZero n] in
theorem sr_zero_ne_one : (sr 0 : DihedralGroup n) ≠ 1 := by
  intro h
  rw [DihedralGroup.one_def] at h
  cases h

/-- **The power sum is differentiable in the reflection rate.** -/
@[lyons_tag "lem_Phi_deriv_nonpos"]
theorem differentiableAt_reflPhi (lam0 : RateFn (DihedralGroup n)) (t α : ℝ) (m : ℕ) :
    DifferentiableAt ℝ (fun a : ℝ => reflPhi lam0 (sr 0) t m a) α :=
  (hasDerivAt_reflPhi lam0 sr_zero_inv t α m).differentiableAt

/-- **The derivative of the power sum in a reflection rate is nonpositive.** -/
@[lyons_tag "lem_Phi_deriv_nonpos"]
theorem deriv_reflPhi_nonpos (lam0 : RateFn (DihedralGroup n))
    (hzero : lam0 (sr 0) = 0) {α : ℝ} (hα : 0 ≤ α) {t : ℝ} (ht : 0 ≤ t) (p : ℕ) :
    deriv (fun a : ℝ => reflPhi lam0 (sr 0) t (p + 1) a) α ≤ 0 := by
  have hsum := sum_reflCentCo_pow_mul_deriv_nonpos lam0 sr_zero_inv sr_zero_ne_one
    hzero hα ht p (fun θ hθ0 hθ1 =>
      sum_co_pow_mul_sandwich_le _ (centeredElt_isPos _ _) hθ0 hθ1 p)
  rw [(hasDerivAt_reflPhi lam0 sr_zero_inv t α (p + 1)).deriv,
    show 2 * (p + 1) - 1 = 2 * p + 1 from by omega,
    show 2 * (p + 1) = 2 * p + 2 from by omega]
  have hfactor : ∑ g : DihedralGroup n, ((2 * p + 2 : ℕ) : ℝ)
        * reflCentCo lam0 (sr 0) t α g ^ (2 * p + 1)
        * ((t • ∫ θ in (0:ℝ)..1, duhamelIntegrand lam0 (sr 0) t α θ) g 1).re
      = ((2 * p + 2 : ℕ) : ℝ) * ∑ g : DihedralGroup n,
        reflCentCo lam0 (sr 0) t α g ^ (2 * p + 1)
        * ((t • ∫ θ in (0:ℝ)..1, duhamelIntegrand lam0 (sr 0) t α θ) g 1).re := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring
  rw [hfactor]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hsum

/-- **Increasing a reflection rate does not increase the power sum**, in the total
parametrisation. -/
theorem antitoneOn_reflPhi (lam0 : RateFn (DihedralGroup n))
    (hzero : lam0 (sr 0) = 0) {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (hm : 1 ≤ m) :
    AntitoneOn (fun a : ℝ => reflPhi lam0 (sr 0) t m a) (Set.Ici 0) := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun x _ => (differentiableAt_reflPhi lam0 t x (p + 1)).continuousAt.continuousWithinAt)
    (fun x _ => (differentiableAt_reflPhi lam0 t x (p + 1)).differentiableWithinAt)
    fun x hx => ?_
  rw [interior_Ici] at hx
  exact deriv_reflPhi_nonpos lam0 hzero (le_of_lt hx) ht p

/-- **Increasing a reflection rate does not increase the power sum.** -/
@[lyons_tag "lem_reflection_step"]
theorem Phi_setAt_le (lam0 : RateFn (DihedralGroup n)) (hzero : lam0 (sr 0) = 0)
    {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (hm : 1 ≤ m) {α₀ α₁ : ℝ} (h₀ : 0 ≤ α₀)
    (h₀₁ : α₀ ≤ α₁) :
    Phi (lam0.setAt sr_zero_inv sr_zero_ne_one (h₀.trans h₀₁)) t m
      ≤ Phi (lam0.setAt sr_zero_inv sr_zero_ne_one h₀) t m := by
  rw [← reflPhi_eq lam0 sr_zero_inv sr_zero_ne_one hzero (h₀.trans h₀₁) t m,
    ← reflPhi_eq lam0 sr_zero_inv sr_zero_ne_one hzero h₀ t m]
  exact antitoneOn_reflPhi lam0 hzero ht hm (Set.mem_Ici.mpr h₀)
    (Set.mem_Ici.mpr (h₀.trans h₀₁)) h₀₁

end Dihedral

end Lyons
