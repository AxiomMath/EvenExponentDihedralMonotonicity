/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lyons.Walk.Duhamel
import Lyons.Walk.CenteredRpow

/-!
# Differentiating the centred element in a reflection rate

The derivative of the centred element `a_α = h_t^{λ[b ↦ α]} - π_G` in the rate `α` at a single
involution `b`. Everything here is about a general finite group and a general involution; the
dihedral specifics enter only downstream.

`RateFn.setAt` takes `0 ≤ α` as a *proof argument*, so `α ↦ λ[b ↦ α]` is not a function of `α`
alone and cannot be differentiated as written. Instead `Lyons.reflLap` takes `Δ_0 + α(1 - b)` as
the primitive object, which is total in `α`, and `Lyons.reflLap_eq_laplacian_setAt` identifies it
with the rate-family Laplacian wherever `α ≥ 0`. That `1 - b` is the right increment is
`Lyons.orbitElt_of_invol`: for an involution the inverse orbit is a singleton.

The derivative is a Duhamel integral. Its integrand is written with `reflHeatMat` at the *scaled
times* `θt` and `(1-θ)t` rather than as a sandwich `x_{a_α,θ,b}` of fractional powers, because in
that form it holds for **every** `θ`, whereas the sandwich form fails at `θ = 0` and `θ = 1`
(there `a_α^0 = 1`, not `1 - P`). `Lyons.reflHeatMat_mul_compl_eq_powElt` supplies the
identification for `θ > 0`.

## Main definitions

* `Lyons.reflLap`: `Δ_0 + α(1 - b)`, total in `α`.
* `Lyons.reflHeatMat`: `exp (-t · L (reflLap))`, total in `α`.

## Main results

* `Lyons.orbitElt_of_invol`: for an involution, `ζ_b = 1 - b`.
* `Lyons.hasDerivAt_reflHeatMat`: Duhamel, specialised to the reflection rate.
* `Lyons.hasDerivAt_reflCentered`: the same, centred.
* `Lyons.insert_compl_uniform`, `Lyons.duhamel_integrand_split`: the algebra of the integrand.
* `Lyons.hasDerivAt_reflCentered_integral`: the derivative as `t ∫₀¹ (… − a_α)`.
* `Lyons.reflHeatMat_mul_compl_eq_powElt`: the integrand's factors are fractional powers of
  `a_α`.
-/

open Matrix
open scoped Norms.Operator

namespace Lyons

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] in
/-- For an involution the inverse orbit is a singleton, so the orbit element is `1 - b`. -/
theorem orbitElt_of_invol {b : G} (hb : b⁻¹ = b) :
    orbitElt b = 1 - MonoidAlgebra.single b (1 : ℝ) := by
  rw [orbitElt, invOrbit, hb]
  simp

/-- The Laplacian of the reflection family, as a total function of the rate. -/
noncomputable def reflLap (lam0 : RateFn G) (b : G) (α : ℝ) : MonoidAlgebra ℝ G :=
  laplacian lam0 + α • orbitElt b

theorem L_reflLap (lam0 : RateFn G) (b : G) (α : ℝ) :
    L (reflLap lam0 b α) = L (laplacian lam0) + α • L (orbitElt b) := by
  rw [reflLap, L_add, L_smul]

/-- It agrees with the Laplacian of the reflection family for a nonnegative rate. -/
theorem reflLap_eq_laplacian_setAt (lam0 : RateFn G) {b : G} (hb : b⁻¹ = b) (hb1 : b ≠ 1)
    (hzero : lam0 b = 0) {α : ℝ} (hα : 0 ≤ α) :
    reflLap lam0 b α = laplacian (lam0.setAt hb hb1 hα) := by
  refine co_injective fun g ↦ ?_
  rw [reflLap, co_add, co_smul, coe_laplacian, coe_laplacian, orbitElt_of_invol hb,
    co_sub, co_one, co_single]
  have hsum : ∑ s : G, (lam0.setAt hb hb1 hα) s = (∑ s : G, lam0 s) + α := by
    classical
    have hsplit : ∀ s : G, (lam0.setAt hb hb1 hα) s
        = lam0 s + (if s = b then α else 0) := by
      intro s
      by_cases h : s = b
      · subst h; simp [RateFn.setAt, hzero]
      · simp [RateFn.setAt_apply_of_ne _ hb hb1 hα h, h]
    rw [Finset.sum_congr rfl fun s _ ↦ hsplit s, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ b (fun _ => α)]
    simp
  rw [hsum]
  by_cases hg1 : g = 1
  · subst hg1
    have h1b : (1 : G) ≠ b := Ne.symm hb1
    rw [RateFn.setAt_apply_of_ne _ hb hb1 hα h1b]
    simp [h1b, lam0.apply_one]
  · by_cases hg : g = b
    · subst hg
      rw [RateFn.setAt_apply_self _ hb hb1 hα, hzero]
      simp [hg1]
    · rw [RateFn.setAt_apply_of_ne _ hb hb1 hα hg]
      simp [hg1, hg]


/-- The heat matrix of the reflection family, as a total function of the rate. -/
noncomputable def reflHeatMat (lam0 : RateFn G) (b : G) (t α : ℝ) : Matrix G G ℂ :=
  NormedSpace.exp ((-t) • L (reflLap lam0 b α))

theorem reflHeatMat_eq (lam0 : RateFn G) {b : G} (hb : b⁻¹ = b) (hb1 : b ≠ 1)
    (hzero : lam0 b = 0) {α : ℝ} (hα : 0 ≤ α) (t : ℝ) :
    reflHeatMat lam0 b t α = heatMat (lam0.setAt hb hb1 hα) t := by
  rw [reflHeatMat, reflLap_eq_laplacian_setAt lam0 hb hb1 hzero hα, heatMat]
  congr 1
  ext g h
  simp [Complex.real_smul]

/-- **Duhamel, specialised to the reflection rate.** -/
theorem hasDerivAt_reflHeatMat (lam0 : RateFn G) (b : G) (t α : ℝ) :
    HasDerivAt (fun a : ℝ => reflHeatMat lam0 b t a)
      (-∫ s in (0:ℝ)..t, NormedSpace.exp ((-s) • L (reflLap lam0 b α)) * L (orbitElt b)
          * NormedSpace.exp ((s - t) • L (reflLap lam0 b α))) α := by
  simp only [reflHeatMat, L_reflLap]
  exact duhamel_deriv _ _ t α

/-- **The derivative of the centred element in the reflection rate.** -/
theorem hasDerivAt_reflCentered (lam0 : RateFn G) (b : G) (t α : ℝ) :
    HasDerivAt (fun a : ℝ => reflHeatMat lam0 b t a * (1 - L (uniform G)))
      ((-∫ s in (0:ℝ)..t, NormedSpace.exp ((-s) • L (reflLap lam0 b α)) * L (orbitElt b)
          * NormedSpace.exp ((s - t) • L (reflLap lam0 b α))) * (1 - L (uniform G))) α :=
  (hasDerivAt_reflHeatMat lam0 b t α).mul_const _

/-! ### The algebra of the Duhamel integrand -/

theorem sum_co_orbitElt (s : G) : ∑ g : G, co (orbitElt s) g = 0 := by
  classical
  rw [Finset.sum_congr rfl fun g _ ↦ co_orbitElt s g, Finset.sum_sub_distrib,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const]
  simp

theorem reflLap_mul_uniform (lam0 : RateFn G) (b : G) (α : ℝ) :
    reflLap lam0 b α * uniform G = 0 := by
  rw [reflLap, add_mul, laplacian_mul_uniform, smul_mul_assoc, uniform_absorb,
    sum_co_orbitElt, zero_smul, smul_zero, add_zero]

theorem uniform_mul_reflLap (lam0 : RateFn G) (b : G) (α : ℝ) :
    uniform G * reflLap lam0 b α = 0 := by
  rw [reflLap, mul_add, uniform_mul_laplacian, mul_smul_comm, uniform_mul_absorb,
    sum_co_orbitElt, zero_smul, smul_zero, add_zero]

theorem exp_reflLap_mul_uniform (lam0 : RateFn G) (b : G) (α u : ℝ) :
    NormedSpace.exp (u • L (reflLap lam0 b α)) * L (uniform G) = L (uniform G) := by
  refine exp_mul_of_mul_eq_zero ?_
  rw [smul_mul_assoc, ← L_mul, reflLap_mul_uniform, L_zero, smul_zero]

theorem uniform_mul_exp_reflLap (lam0 : RateFn G) (b : G) (α u : ℝ) :
    L (uniform G) * NormedSpace.exp (u • L (reflLap lam0 b α)) = L (uniform G) := by
  refine mul_exp_of_mul_eq_zero ?_
  rw [mul_smul_comm, ← L_mul, uniform_mul_reflLap, L_zero, smul_zero]


set_option linter.unusedDecidableInType false in
theorem uniform_mul_single (b : G) :
    uniform G * MonoidAlgebra.single b (1 : ℝ) = uniform G := by
  classical
  rw [uniform_mul_absorb]
  have : ∑ h : G, co (MonoidAlgebra.single b (1:ℝ)) h = 1 := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc; simp [hc]
    · intro hcon; exact absurd (Finset.mem_univ b) hcon
  rw [this, one_smul]

set_option linter.unusedDecidableInType false in
theorem L_uniform_mul_L_single (b : G) :
    L (uniform G) * L (MonoidAlgebra.single b (1 : ℝ)) = L (uniform G) := by
  rw [← L_mul, uniform_mul_single]

/-- **Inserting `1 - P` to the left of `L_b` is free.** -/
theorem insert_compl_uniform (lam0 : RateFn G) (b : G) (α u v : ℝ) :
    NormedSpace.exp (u • L (reflLap lam0 b α)) * L (MonoidAlgebra.single b (1:ℝ))
        * NormedSpace.exp (v • L (reflLap lam0 b α)) * (1 - L (uniform G))
      = (NormedSpace.exp (u • L (reflLap lam0 b α)) * (1 - L (uniform G)))
        * L (MonoidAlgebra.single b (1:ℝ))
        * (NormedSpace.exp (v • L (reflLap lam0 b α)) * (1 - L (uniform G))) := by
  set X := NormedSpace.exp (u • L (reflLap lam0 b α)) with hX
  set Y := NormedSpace.exp (v • L (reflLap lam0 b α)) with hY
  set P := L (uniform G) with hP
  set Lb := L (MonoidAlgebra.single b (1:ℝ)) with hLb
  have hXQ : X * (1 - P) = X - P := by rw [mul_sub, mul_one, hX, hP,
    exp_reflLap_mul_uniform]
  have hPLb : P * Lb = P := L_uniform_mul_L_single b
  have hPY : P * (Y * (1 - P)) = 0 := by
    rw [← mul_assoc, hP, hY, uniform_mul_exp_reflLap, mul_sub, mul_one, ← hP,
      L_uniform_mul_self, sub_self]
  symm
  calc (X * (1 - P)) * Lb * (Y * (1 - P))
      = (X - P) * Lb * (Y * (1 - P)) := by rw [hXQ]
    _ = X * Lb * (Y * (1 - P)) - P * Lb * (Y * (1 - P)) := by rw [sub_mul, sub_mul]
    _ = X * Lb * (Y * (1 - P)) - P * (Y * (1 - P)) := by rw [hPLb]
    _ = X * Lb * (Y * (1 - P)) := by rw [hPY, sub_zero]
    _ = X * Lb * Y * (1 - P) := by noncomm_ring


/-- The Duhamel integrand splits into a constant part and a sandwich part. -/
theorem duhamel_integrand_split (lam0 : RateFn G) {b : G} (hb : b⁻¹ = b) (α t s : ℝ) :
    NormedSpace.exp ((-s) • L (reflLap lam0 b α)) * L (orbitElt b)
        * NormedSpace.exp ((s - t) • L (reflLap lam0 b α))
      = reflHeatMat lam0 b t α
        - NormedSpace.exp ((-s) • L (reflLap lam0 b α))
          * L (MonoidAlgebra.single b (1:ℝ))
          * NormedSpace.exp ((s - t) • L (reflLap lam0 b α)) := by
  have hcomm : Commute ((-s) • L (reflLap lam0 b α)) ((s - t) • L (reflLap lam0 b α)) :=
    ((Commute.refl _).smul_left _).smul_right _
  have hsum : (-s) • L (reflLap lam0 b α) + (s - t) • L (reflLap lam0 b α)
      = (-t) • L (reflLap lam0 b α) := by
    rw [← add_smul]
    congr 1
    ring
  have hexp : NormedSpace.exp ((-s) • L (reflLap lam0 b α))
      * NormedSpace.exp ((s - t) • L (reflLap lam0 b α)) = reflHeatMat lam0 b t α := by
    rw [reflHeatMat, ← hsum, Matrix.exp_add_of_commute _ _ hcomm]
  rw [orbitElt_of_invol hb, L_sub, L_one, mul_sub, sub_mul, mul_one]
  exact sub_left_inj.mpr hexp

/-! ### The integral calculus, and the node -/

omit [Group G] in
noncomputable def mulRightCLM (Q : Matrix G G ℂ) : Matrix G G ℂ →L[ℝ] Matrix G G ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => X * Q
      map_add' := fun X Y => add_mul X Y Q
      map_smul' := fun r X => smul_mul_assoc r X Q }

omit [Group G] in
set_option linter.unusedDecidableInType false in
theorem integral_mul_const_matrix (Q : Matrix G G ℂ) (f : ℝ → Matrix G G ℂ)
    (hf : Continuous f) (a b : ℝ) :
    (∫ s in a..b, f s) * Q = ∫ s in a..b, (f s * Q) :=
  ((mulRightCLM Q).intervalIntegral_comp_comm (f := f)
    (μ := MeasureTheory.volume) (hf.intervalIntegrable a b)).symm

/-- The exponential factors are continuous in the time parameter. -/
theorem continuous_reflExp (lam0 : RateFn G) (b : G) (α : ℝ) (c d : ℝ) :
    Continuous fun s : ℝ => NormedSpace.exp ((c * s + d) • L (reflLap lam0 b α)) :=
  NormedSpace.exp_continuous.comp (by fun_prop)



/-- The Duhamel integral, with the constant part peeled off. -/
theorem duhamel_integral_split (lam0 : RateFn G) {b : G} (hb : b⁻¹ = b) (α t : ℝ) :
    (∫ s in (0:ℝ)..t, NormedSpace.exp ((-s) • L (reflLap lam0 b α)) * L (orbitElt b)
        * NormedSpace.exp ((s - t) • L (reflLap lam0 b α)))
      = t • reflHeatMat lam0 b t α
        - ∫ s in (0:ℝ)..t, NormedSpace.exp ((-s) • L (reflLap lam0 b α))
            * L (MonoidAlgebra.single b (1:ℝ))
            * NormedSpace.exp ((s - t) • L (reflLap lam0 b α)) := by
  have hX : Continuous fun s : ℝ => NormedSpace.exp ((-s) • L (reflLap lam0 b α)) := by
    have := continuous_reflExp lam0 b α (-1) 0
    simpa using this
  have hY : Continuous fun s : ℝ => NormedSpace.exp ((s - t) • L (reflLap lam0 b α)) := by
    have := continuous_reflExp lam0 b α 1 (-t)
    simpa [sub_eq_add_neg] using this
  have hJ : Continuous fun s : ℝ => NormedSpace.exp ((-s) • L (reflLap lam0 b α))
      * L (MonoidAlgebra.single b (1:ℝ))
      * NormedSpace.exp ((s - t) • L (reflLap lam0 b α)) :=
    (hX.mul continuous_const).mul hY
  rw [intervalIntegral.integral_congr
      (g := fun s => reflHeatMat lam0 b t α
        - NormedSpace.exp ((-s) • L (reflLap lam0 b α))
          * L (MonoidAlgebra.single b (1:ℝ))
          * NormedSpace.exp ((s - t) • L (reflLap lam0 b α)))
      (fun s _ => duhamel_integrand_split lam0 hb α t s),
    intervalIntegral.integral_sub
      (continuous_const.intervalIntegrable 0 t) (hJ.intervalIntegrable 0 t),
    intervalIntegral.integral_const]
  simp


/-- **The derivative value, in the shape `t ∫₀¹ (… − a_α)`.** -/
theorem reflCentered_deriv_value (lam0 : RateFn G) {b : G} (hb : b⁻¹ = b) (α t : ℝ) :
    (-∫ s in (0:ℝ)..t, NormedSpace.exp ((-s) • L (reflLap lam0 b α)) * L (orbitElt b)
        * NormedSpace.exp ((s - t) • L (reflLap lam0 b α))) * (1 - L (uniform G))
      = t • ∫ θ in (0:ℝ)..1,
          ((reflHeatMat lam0 b (θ * t) α * (1 - L (uniform G)))
            * L (MonoidAlgebra.single b (1:ℝ))
            * (reflHeatMat lam0 b ((1 - θ) * t) α * (1 - L (uniform G)))
          - reflHeatMat lam0 b t α * (1 - L (uniform G))) := by
  have hX : Continuous fun s : ℝ => NormedSpace.exp ((-s) • L (reflLap lam0 b α)) := by
    have := continuous_reflExp lam0 b α (-1) 0; simpa using this
  have hY : Continuous fun s : ℝ => NormedSpace.exp ((s - t) • L (reflLap lam0 b α)) := by
    have := continuous_reflExp lam0 b α 1 (-t); simpa [sub_eq_add_neg] using this
  have hJ : Continuous fun s : ℝ => NormedSpace.exp ((-s) • L (reflLap lam0 b α))
      * L (MonoidAlgebra.single b (1:ℝ))
      * NormedSpace.exp ((s - t) • L (reflLap lam0 b α)) :=
    (hX.mul continuous_const).mul hY
  set Q := (1 : Matrix G G ℂ) - L (uniform G) with hQdef
  have hg : ∀ s : ℝ, (NormedSpace.exp ((-s) • L (reflLap lam0 b α))
        * L (MonoidAlgebra.single b (1:ℝ))
        * NormedSpace.exp ((s - t) • L (reflLap lam0 b α))) * Q
      = (NormedSpace.exp ((-s) • L (reflLap lam0 b α)) * Q)
        * L (MonoidAlgebra.single b (1:ℝ))
        * (NormedSpace.exp ((s - t) • L (reflLap lam0 b α)) * Q) :=
    fun s => insert_compl_uniform lam0 b α (-s) (s - t)
  rw [duhamel_integral_split lam0 hb α t, neg_sub, sub_mul,
    integral_mul_const_matrix Q _ hJ 0 t,
    intervalIntegral.integral_congr (fun s _ => hg s), smul_mul_assoc]
  have hcov := intervalIntegral.smul_integral_comp_mul_right (a := (0:ℝ)) (b := (1:ℝ))
    (fun s : ℝ => (NormedSpace.exp ((-s) • L (reflLap lam0 b α)) * Q)
      * L (MonoidAlgebra.single b (1:ℝ))
      * (NormedSpace.exp ((s - t) • L (reflLap lam0 b α)) * Q)) t
  simp only [zero_mul, one_mul] at hcov
  rw [← hcov]
  set A := L (reflLap lam0 b α) with hA
  set Lb := L (MonoidAlgebra.single b (1:ℝ)) with hLb
  have hggcont : Continuous fun θ : ℝ =>
      (reflHeatMat lam0 b (θ * t) α * Q) * Lb
        * (reflHeatMat lam0 b ((1 - θ) * t) α * Q) := by
    have h1 : Continuous fun θ : ℝ => reflHeatMat lam0 b (θ * t) α :=
      (continuous_reflExp lam0 b α (-t) 0).congr fun θ => by
        rw [reflHeatMat]; congr 2; ring
    have h2 : Continuous fun θ : ℝ => reflHeatMat lam0 b ((1 - θ) * t) α :=
      (continuous_reflExp lam0 b α t (-t)).congr fun θ => by
        rw [reflHeatMat]; congr 2; ring
    exact ((h1.mul continuous_const).mul continuous_const).mul (h2.mul continuous_const)
  rw [intervalIntegral.integral_sub (hggcont.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1), intervalIntegral.integral_const, smul_sub]
  simp only [sub_zero, one_smul]
  congr 1
  congr 1
  refine intervalIntegral.integral_congr fun x _ ↦ ?_
  rw [reflHeatMat, reflHeatMat, show x * t - t = -((1 - x) * t) by ring]


/-- **The derivative of the centred element in the reflection rate**, as an integral over
`θ ∈ [0, 1]`. -/
@[lyons_tag "lem_reflection_derivative"]
theorem hasDerivAt_reflCentered_integral (lam0 : RateFn G) {b : G} (hb : b⁻¹ = b)
    (t α : ℝ) :
    HasDerivAt (fun a : ℝ => reflHeatMat lam0 b t a * (1 - L (uniform G)))
      (t • ∫ θ in (0:ℝ)..1,
          ((reflHeatMat lam0 b (θ * t) α * (1 - L (uniform G)))
            * L (MonoidAlgebra.single b (1:ℝ))
            * (reflHeatMat lam0 b ((1 - θ) * t) α * (1 - L (uniform G)))
          - reflHeatMat lam0 b t α * (1 - L (uniform G)))) α := by
  rw [← reflCentered_deriv_value lam0 hb α t]
  exact hasDerivAt_reflCentered lam0 b t α

/-- Each exponential factor in the integrand is a fractional power of the centred element. -/
theorem reflHeatMat_mul_compl_eq_powElt (lam0 : RateFn G) {b : G} (hb : b⁻¹ = b)
    (hb1 : b ≠ 1) (hzero : lam0 b = 0) {α : ℝ} (hα : 0 ≤ α) (t : ℝ) {θ : ℝ}
    (hθ : 0 < θ) :
    reflHeatMat lam0 b (θ * t) α * (1 - L (uniform G))
      = L (powElt (centeredElt (lam0.setAt hb hb1 hα) t) θ) := by
  rw [reflHeatMat_eq lam0 hb hb1 hzero hα, ← L_centeredElt_eq_mul,
    powElt_centeredElt _ _ hθ]

end Lyons
