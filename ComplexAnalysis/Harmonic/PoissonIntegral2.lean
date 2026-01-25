/-
Copyright (c) 2025 [Your Name]. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name], [Collaborator Name if applicable]
-/
module
public import Mathlib.Analysis.Complex.Harmonic.Analytic

/-!
# The Poisson Integral Formula on the Unit Disc

## Main results

Theorem `poisson_integral_formula`: Every function `u : ℂ → ℝ`
harmonic on the unit disc and continuous on the closed unit disc can be represented as
```
u(z) = 1/(2π) ∫_0^{2π} (1 - |z|^2) / |e^{it} - z|^2 * u(e^{it}) dt,

```
for `z` in the unit disc.

## Implementation Notes

The proof follows from the
- Cauchy Integral Formula,
- the Cauchy-Goursat Theorem,
- the fact that every harmonic function is the real part of some analytic function on the unit disc,
- the Lebesgue Dominated Convergence Theorem.

## References

[Rudin, *Real and Complex Analysis* (Theorem 11.9)][rudin2006real]

## Tags

harmonic function, Poisson integral, analytic function, unit disc
-/

set_option Elab.async false

public section

open Complex Metric Real Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
         {z : ℂ} {r : ℝ} {f : ℂ → E} {u : ℂ → ℝ}

#count_heartbeats in
/-- Cauchy's integral formula for analytic functions on the unit disc,
    evaluated at scaled points `r * z` with `r ∈ (0,1)`. -/
theorem cauchy_integral_formula_unitDisc [CompleteSpace E]
    (hf : AnalyticOn ℂ f (ball 0 1)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    f (r * z) = (1 / (2 * π)) • ∫ t in 0..2*π,
                (exp (I * t) / (exp (I * t) - z)) • (f (r * exp (I * t))) := by
  have (x : ℂ) (hx : ‖x‖ ≤ 1) : ‖r * x‖ < 1 := by
      simp only [Complex.norm_mul, norm_real, norm_eq_abs, abs_of_pos hr.1]
      have := mul_le_of_le_one_left (LT.lt.le hr.1) hx
      rw [mul_comm] at this
      exact LE.le.trans_lt this hr.2
  have hfr_diff (x : ℂ) (hx : ‖x‖ ≤ 1) : DifferentiableAt ℂ (fun ζ => f (r * ζ)) x :=
     DifferentiableAt.comp x (hf.differentiableOn.differentiableAt (isOpen_ball.mem_nhds
                    (by simp only [mem_ball, Complex.dist_eq, sub_zero, this x hx])))
                             (differentiableAt_id.const_mul _)
  have hfr_cont : ContinuousOn (fun ζ => f (r* ζ)) (closedBall 0 1) := by
      intro x hx
      rw [mem_closedBall, dist_zero_right] at hx
      exact (DifferentiableAt.continuousAt (hfr_diff x hx)).continuousWithinAt
  have h_cauchy : -- We apply the Cauchy Integral Formula to the function `z ↦ f(rz)`.
    f (r * z) = (1 / (2 * π * I)) • ∮ (ζ : ℂ) in C(0, 1), (1 / (ζ - z)) • f (r * ζ)  := by
    have := @circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
               _ _ _ _ 1 0 z (fun ζ => f (r * ζ)) ∅ countable_empty hz hfr_cont
    simp only [div_eq_inv_mul, mul_one]
    rw [this]
    · simp only [smul_smul,inv_mul_cancel₀ two_pi_I_ne_zero]
      exact Eq.symm (MulAction.one_smul (f (r * z)))
    · intro x hx
      simp only [diff_empty,mem_ball,Complex.dist_eq, sub_zero] at hx
      exact hfr_diff x (LT.lt.le hx)
  have h_cauchy :
    f (r * z) =  ∮ (ζ : ℂ) in C(0, 1), (1 / (2 * π * I)) • (1 / (ζ - z)) • f (r * ζ)  := by
    rw [h_cauchy]
    exact Eq.symm (circleIntegral.integral_smul
              (1 / (2 * π * I)) (fun ζ ↦ (1 / (ζ - z)) • f (r * ζ)) 0 1)
  have : (1 / (2 * π)) • ∫ (t : ℝ) in 0..2 * π,
      (cexp (I * t) / (cexp (I * t) - z)) • f (r * cexp (I * t)) =
     ∫ (t : ℝ) in 0..2 * π, (1 / (2 * π)) •
      (cexp (I * t) / (cexp (I * t) - z)) • f (r * cexp (I * t)) :=
        Eq.symm (intervalIntegral.integral_smul (1 / (2 * π)) fun t ↦
                (cexp (I * t) / (cexp (I * t) - z)) • f (r * cexp (I * t)))
  rw [this,h_cauchy]
  simp only [circleIntegral]
  congr 1
  ext t
  have : f (r * circleMap 0 1 t) = f (r * cexp (I * t)) := by simp [circleMap, mul_comm]
  rw [this]
  simp only [← smul_assoc]
  have : (deriv (circleMap 0 1) t • (1 / (2 * π * I))) • (1 / (circleMap 0 1 t - z)) =
         ((1 / (2 * π)) • (cexp (I * t) / (cexp (I * t) - z))) := by
    simp [circleMap, deriv_circleMap]
    ring_nf
    rw [I_sq]
    ring_nf
  rw [this]

lemma goursat_vanishing_integral
    (hf : AnalyticOn ℂ f (ball 0 1)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    ∫ t in 0..2*Real.pi,  (star z / (star (exp (I * t)) - star z)) • f (r * exp (I * t)) = 0 := by
       sorry

#count_heartbeats in
/-- For a sequence `r_n → 1` with `r_n ∈ (0,1)`,
the integral of `t ↦ k(e^{it}) f(r_n * e^{it})` on [0 , 2π] converges to
the integral of `t ↦ k(e^{it}) f(e^{it})` on [0 , 2π],
when `f` is continuous on the closed unit disc and `k` is continuous on the unit circle. -/
theorem tendsto_integral_boundary_unitDisc_of_continuousOn
    (hf : ContinuousOn f (closedBall (0 : ℂ) 1))
    (k : ℂ → ℂ) (hk : ContinuousOn k (sphere (0 : ℂ) 1))
    (r : ℕ → ℝ) (hr : ∀ n, r n ∈ Ioo 0 1) (hr_lim : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => ∫ t in 0..2 * π, (k (exp (I * t))) • f (r n * exp (I * t)))
           atTop (𝓝 (∫ t in 0..2 * π, (k (exp (I * t))) • f (exp (I * t)))) := by
  -- -- We apply the Lebesgue Dominated Convergence Theorem.
  have hrn (n : ℕ) (t : ℝ) : (r n) * cexp (t * I) ∈ closedBall 0 1  := by
      rw [mem_closedBall, dist_zero_right, norm_mul, norm_real,
            norm_eq_abs, norm_exp_ofReal_mul_I, mul_one, abs_of_pos (hr n).1]
      exact LT.lt.le (hr n).2
  apply_rules [Tendsto.const_mul,
                intervalIntegral.tendsto_integral_filter_of_dominated_convergence]
  rotate_right
  -- We define the bound to be the supremum of the integrand.
  · exact fun x => (SupSet.sSup (image (fun ζ => ‖k ζ‖) (sphere 0 1))) *
                   (SupSet.sSup (image (fun w => ‖f w‖) (closedBall 0 1)))
  -- We verify the measurability of the integrand.
  · apply Eventually.of_forall
    intro n
    apply Continuous.aestronglyMeasurable
    refine Continuous.smul ?_ ?_
    · refine ContinuousOn.comp_continuous (s:= sphere 0 1) hk (by fun_prop) ?_
      · intro x
        rw [mem_sphere, dist_zero_right, mul_comm, norm_exp_ofReal_mul_I]
    · refine ContinuousOn.comp_continuous (s:= closedBall 0 1) hf (by fun_prop) ?_
      simpa [mul_comm] using hrn n
  -- We verify that the integrand is eventually bounded by the bound.
  · refine Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun t ht => ?_
    -- We bound each factor of the integrand separately.
    have h_bound :
        ‖f (r n * exp (t * I))‖ ≤ sSup (image (fun w => ‖f w‖) (closedBall (0 : ℂ) 1)) ∧
        ‖k (exp (t * I))‖ ≤ sSup (image (fun w => ‖k w‖) (sphere 0 1)) := by
      refine ⟨le_csSup ?_ ?_, le_csSup ?_ ?_⟩
      · exact IsCompact.bddAbove (isCompact_closedBall (0 : ℂ) 1 |>.image_of_continuousOn hf.norm)
      · exact ⟨_, hrn n t, rfl⟩
      · exact IsCompact.bddAbove (IsCompact.image_of_continuousOn (isCompact_sphere 0 1) hk.norm)
      · use (exp (t * I))
        constructor
        · simp [Metric.sphere, dist_eq_norm]
        · rfl
    rw [mul_comm]
    have hmul_bds: ‖(k (exp (t * I)))‖  * ‖f (r n * exp (t * I))‖ ≤
      (sSup (image (fun ζ => ‖k ζ‖) (sphere 0 1))) *
      (sSup (image (fun w => ‖f w‖) (closedBall (0 : ℂ) 1))):= by
         apply mul_le_mul h_bound.2 h_bound.1 (norm_nonneg (f ((r n) * cexp (t * I))))
         apply sSup_nonneg
         rintro _ ⟨_,⟨_,hx⟩⟩
         simp_rw [← hx, norm_nonneg]
    have hmul_norm : ‖k (cexp (t * I)) • f ((r n) * cexp (t * I))‖ ≤
      ‖k (cexp (t * I))‖ * ‖f ((r n) * cexp (t * I))‖ := by rw [norm_smul]
    exact le_trans hmul_norm hmul_bds
  · simp only [ne_eq, enorm_ne_top, not_false_eq_true, intervalIntegrable_const]
  -- We verify the pointwise convergence of the integrand.
  · refine Eventually.of_forall fun x hx => Tendsto.smul tendsto_const_nhds ?_
    apply_rules [Filter.Tendsto.comp (hf.continuousWithinAt _), tendsto_const_nhds]
    · rw [tendsto_nhdsWithin_iff]
      constructor
      · simpa using Tendsto.mul
          (Complex.continuous_ofReal.continuousAt.tendsto.comp hr_lim) tendsto_const_nhds
      · apply Eventually.of_forall
        intro n
        simpa [mul_comm] using hrn n x
    · rw [mem_closedBall,dist_zero_right,mul_comm,norm_exp_ofReal_mul_I]

#count_heartbeats in
/-- For an analytic function `f` on the unit disc, `f(rz)` equals the integral
of `f(re^{it})` against the real part of the Herglotz kernel, where `r ∈ (0,1)`
and `z` is in the unit disc. -/
theorem poisson_formula_analytic_unitDisc [CompleteSpace E]
    (hf : AnalyticOn ℂ f (ball 0 1))
    (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    f (r * z) = (1 / (2 * π)) • ∫ t in 0..2*π,
       (((exp (I * t) + z) / (exp (I * t) - z)).re) • f (r * exp (I * t)) := by
  have h_add : f (r * z) = (1 / (2 * π)) • ∫ t in 0..2*π,
                           (exp (I * t) / (exp (I * t) - z)) • f (r * exp (I * t))  +
                           (star z / (star (exp (I * t)) - star z)) • f (r * exp (I * t)) := by
    have hr_exp (t : ℝ) : r * cexp (I * t) ∈ ball 0 1 := by
        simp only [mem_ball,Complex.dist_eq,sub_zero, norm_mul,
                   norm_real,norm_eq_abs, abs_of_pos hr.1]
        simpa [mul_comm,norm_exp_ofReal_mul_I] using hr.2
    have h_exp_ball (t : ℝ)  : ¬(cexp (I * t) ∈ ball 0 1) := by
      by_contra hzx
      rw [mem_ball,dist_zero_right,mul_comm, norm_exp_ofReal_mul_I] at hzx
      exact (lt_self_iff_false 1).mp hzx
    /- We add the integrals from `cauchy_integral_formula_unitDisc`
      and `goursat_vanishing_integral` to obtain the desired formula. -/
    rw [intervalIntegral.integral_add]
    · rw [cauchy_integral_formula_unitDisc hf hr hz, goursat_vanishing_integral hf hr hz, add_zero]
    · apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.smul ?_ ?_
      · refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
                                (Continuous.continuousOn (by fun_prop)) ?_
        intro t _
        by_contra hzx
        rw [sub_eq_zero] at hzx
        rw [← hzx] at hz
        exact h_exp_ball t hz
      · refine hf.continuousOn.comp (Continuous.continuousOn (by fun_prop)) ?_
        intro t _
        exact hr_exp t
    · apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.smul ?_ ?_
      · refine ContinuousOn.div (Continuous.continuousOn continuous_const)
                                (Continuous.continuousOn (by fun_prop)) ?_
        intro t _
        by_contra hzx
        rw [sub_eq_zero] at hzx
        simp only [star_inj] at hzx
        rw [← hzx] at hz
        exact h_exp_ball t hz
      · refine hf.continuousOn.comp (by fun_prop) ?_
        intro t _
        exact hr_exp t
  convert h_add using 3
  ext t
  rw [← add_smul]
  have : (exp (I * t) / (exp (I * t) - z)) + (star z / (star (exp (I * t)) - star z)) =
         ((exp (I * t) + z) / (exp (I * t) - z)).re := by
    simp [Complex.ext_iff, div_eq_mul_inv, normSq]
    grind
  rw [this]
  rfl

open InnerProductSpace

#count_heartbeats in
/-- For a harmonic function `u` on the unit disc, `u(rz)` equals the integral
of `u(r e^{it})` times the real part of the Herglotz kernel, where `r ∈ (0,1)`
and `z` is in the unit disc. -/
theorem harmonic_representation_scaled_radius
    (hu : HarmonicOnNhd u (ball 0 1))
    (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    u (r * z) = (1 / (2 * Real.pi)) * ∫ t in (0)..(2 * Real.pi),
      (((exp (I * t) + z) / (exp (I * t) - z))).re * (u (r * exp (I * t))) := by
  -- We express `u` as the real part of an analytic function `f`. -/
  have hfu : ∃ (f : ℂ → ℂ), AnalyticOn ℂ f (ball 0 1) ∧
    EqOn (fun (z : ℂ) => (f z).re) u (ball 0 1) := by
    obtain ⟨f,hf⟩ := @harmonic_is_realOfHolomorphic u (0 : ℂ) 1 hu
    use f
    exact ⟨hf.1.analyticOn, hf.2⟩
  obtain ⟨f, hf, hf_eq⟩ := hfu
  have hrz : r * z ∈ ball 0 1 := by
    simp only [mem_ball, dist_zero_right, norm_mul, norm_real, norm_eq_abs, abs_of_pos hr.1]
    rw [mem_ball, dist_zero_right] at hz
    nlinarith [hr.1, hr.2, hz]
  -- We replace `u(rz)` by `Re(f(rz))`.
  rw [← hf_eq hrz]
  have hrt (t : ℝ) : r * exp (I * t) ∈ ball 0 1 := by
    simp only [mem_ball, dist_zero_right, norm_mul, norm_real, norm_eq_abs, abs_of_pos hr.1,
               norm_exp_I_mul_ofReal, mul_one, hr.2]
  have hrt : EqOn
    (fun t : ℝ => ((exp (I * t) + z) / (exp (I * t) - z)).re *(f (r * exp (I * t))).re)
    (fun t : ℝ => ((exp (I * t) + z) / (exp (I * t) - z)).re * u (r * exp (I * t)))
    (uIcc 0 (2 * Real.pi)) := by
    intro t _
    simp only [← hf_eq (hrt t)]
  rw [← intervalIntegral.integral_congr hrt]
  dsimp
  rw [congr_arg Complex.re (poisson_formula_analytic_unitDisc hf hr hz)]
  rw [smul_re,smul_eq_mul]
  apply congrArg (fun x => 1 / (2 * π) * x)
  simp only [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  symm
  convert integral_re _ using 1
  any_goals tauto
  · simp only [real_smul, RCLike.mul_re, RCLike.re_to_complex, ofReal_re, RCLike.im_to_complex,
               ofReal_im, zero_mul, sub_zero]
  · refine ContinuousOn.integrableOn_Icc ?_ |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self
    refine ContinuousOn.smul ?_ ?_
    · refine Continuous.continuousOn ?_
      refine Complex.continuous_re.comp ?_
      refine Continuous.div (by fun_prop) (by fun_prop) ?_
      intro t hexpz
      rw [sub_eq_zero] at hexpz
      rw [← hexpz] at hz
      rw [mem_ball,dist_zero_right,mul_comm, norm_exp_ofReal_mul_I] at hz
      exact (lt_self_iff_false 1).mp hz
    · refine hf.continuousOn.comp (Continuous.continuousOn (by fun_prop)) ?_
      intro t _
      simp only [mem_ball,Complex.dist_eq,sub_zero, norm_mul,
                   norm_real,norm_eq_abs, abs_of_pos hr.1]
      simpa [mul_comm,norm_exp_ofReal_mul_I] using hr.2

#count_heartbeats in
/-- The real part of the Herglotz–Riesz kernel is equal to the Poisson kernel. -/
theorem real_part_herglotz_kernel (x w : ℂ) (hx : ‖x‖ = 1) :
    ((x + w) / (x - w)).re = (1 - ‖w‖^2) / ‖x - w‖^2 := by
  rw [Complex.div_re, normSq_eq_norm_sq (x - w)]
  calc (x + w).re * (x - w).re / ‖x - w‖ ^ 2 + (x + w).im * (x - w).im / ‖x - w‖ ^ 2
   _ = ((x.re + w.re) * (x.re - w.re) + (x.im + w.im) * (x.im - w.im)) / ‖x - w‖ ^ 2 := by
        simp only [add_re, sub_re, add_im, sub_im, add_div]
   _ = ((x.re * x.re + x.im * x.im) - (w.re * w.re + w.im * w.im)) / ‖x - w‖ ^ 2 := by ring_nf
   _ = ((normSq x) - (normSq w)) / ‖x - w‖ ^ 2 := by simp only [normSq_apply]
   _ = (‖x‖ ^ 2 - ‖w‖ ^ 2) / ‖x - w‖ ^ 2 := by simp only [normSq_eq_norm_sq]
   _ = (1 - ‖w‖ ^ 2) / ‖x - w‖ ^ 2 := by rw [hx, one_pow 2]
