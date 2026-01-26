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

-- #count_heartbeats in
/-- Cauchy's integral formula for analytic functions on the unit disc,
    evaluated at scaled points `r * z` with `r ∈ (0,1)`. -/
theorem cauchy_integral_formula_unitDisc [CompleteSpace E]
    (hf : AnalyticOn ℂ f (ball 0 1)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    f (r * z) = (1 / (2 * π)) • ∫ t in 0..2*π,
                (exp (t * I) / (exp (t * I) - z)) • (f (r * exp (t * I))) := by
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
         (cexp (t * I) / (cexp (t * I) - z)) • f (r * cexp (t * I)) =
         ∫ (t : ℝ) in 0..2 * π, (1 / (2 * π)) •
         (cexp (t * I) / (cexp (t * I) - z)) • f (r * cexp (t * I)) :=
    Eq.symm (intervalIntegral.integral_smul (1 / (2 * π)) fun t ↦
            (cexp (t * I) / (cexp (t * I) - z)) • f (r * cexp (t * I)))
  rw [this,h_cauchy]
  simp only [circleIntegral]
  congr 1
  ext t
  have : f (r * circleMap 0 1 t) = f (r * cexp (t * I)) := by simp [circleMap]
  rw [this]
  simp only [← smul_assoc]
  have : (deriv (circleMap 0 1) t • (1 / (2 * π * I))) • (1 / (circleMap 0 1 t - z)) =
         ((1 / (2 * π)) • (cexp (t * I) / (cexp (t * I) - z))) := by
    simp only [deriv_circleMap, circleMap, ofReal_one, one_mul, zero_add, mul_inv_rev,
              div_eq_inv_mul, smul_eq_mul, real_smul, ofReal_mul,
              ofReal_inv, ofReal_ofNat,mul_one,mul_assoc]
    rw [← mul_assoc I I⁻¹, mul_inv_cancel₀ I_ne_zero, one_mul]
    ring_nf
  rw [this]

-- #count_heartbeats in
/-- Cauchy-Goursat theorem for the unit disc implies the integral of an analytic function
against the conjugate Cauchy kernel vanishes. -/
lemma goursat_vanishing_integral
    (hf : AnalyticOn ℂ f (ball 0 1)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    ∫ t in 0..2*Real.pi,  (star z / (star (exp (t * I)) - star z)) • f (r * exp (t * I)) = 0 := by
  -- Algebraic identity for the Goursat integrand.
  have goursat_integrand_eq (z : ℂ) (t : ℝ) :
      star z / (star (exp (t * I)) - star z) =  (I * exp (t * I)) *
     (star z / (I * (1 - star z * exp (t * I)))) := by
    have : star (exp (t * I)) = (exp (t * I))⁻¹ := by
      rw [star_def, ← exp_conj, ← exp_neg (t * I)]
      apply congrArg cexp
      simp only [map_mul, conj_ofReal, conj_I, mul_neg]
    simp only [this]
    rw [mul_comm I,mul_assoc, ← mul_div_assoc, mul_div_mul_left (hc:=I_ne_zero), ← mul_div_assoc,
        mul_comm (cexp (t * I)), mul_div_assoc,div_eq_mul_inv (star z)]
    apply congrArg (fun x => (star z) * x)
    rw [inv_eq_one_div]
    nth_rewrite 2 [← inv_inv (cexp (t * I)), inv_eq_one_div]
    rw [div_div,mul_sub,mul_one,mul_comm (star z),← mul_assoc,
        inv_mul_cancel₀ (Complex.exp_ne_zero (t * I)),one_mul]
  -- Use `goursat_integrand_eq` to rewrite the integrand.
  have h_integrand : ∀ t : ℝ, (star z / (star (exp (t * I)) - star z)) • (f (r * exp (t * I))) =
    (I * exp (t * I)) • ((star z / (I * (1 - star z * exp (t * I)))) • (f (r * exp (t * I)))) := by
    intro t
    rw [goursat_integrand_eq]
    simp only [mul_assoc, mul_smul]
  -- Let $g(w) = (star z / (I * (1 - star z * w))) • f (r * w)$.
  set g : ℂ → E := fun w => (star z / (I * (1 - star z * w))) • (f (r * w))
  have aux_denom_ne_zero {w : ℂ} (hw : w ∈ closedBall 0 1) : I * (1 - star z * w) ≠ 0 := by
    apply mul_ne_zero I_ne_zero
    intro h
    have hz_norm : ‖z‖ < 1 := by rw [mem_ball_zero_iff] at hz ; exact hz
    have hw_norm : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
    have : ‖star z * w‖ < 1 := by
      calc ‖star z * w‖ ≤ ‖star z‖ * ‖w‖ := norm_mul_le _ _
        _ = ‖z‖ * ‖w‖ := by rw [norm_star]
        _ < 1 := by nlinarith [norm_nonneg z, norm_nonneg w]
    rw [sub_eq_zero] at h
    rw [<-h] at this
    rw [norm_one] at this
    exact absurd this (lt_irrefl 1)
  /- By Cauchy's integral theorem, the integral of an
   analytic function over a closed contour is zero. -/
  have h_cauchy : (∮ w in C(0, 1), g w) = 0 := by
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable
    · exact zero_le_one
    · exact Set.countable_empty
    · refine ContinuousOn.smul ?_ ?_
      · refine continuousOn_of_forall_continuousAt fun w hw =>
          ContinuousAt.div continuousAt_const ?_ ?_
        · exact ContinuousAt.mul continuousAt_const (ContinuousAt.sub continuousAt_const (
            ContinuousAt.mul continuousAt_const continuousAt_id))
        · exact aux_denom_ne_zero hw
      · refine ContinuousOn.comp hf.continuousOn ?_ ?_;
        · exact continuousOn_const.mul continuousOn_id;
        · exact fun x hx => by simpa [abs_of_nonneg hr.1.le] using lt_of_le_of_lt (
          mul_le_of_le_one_right hr.1.le (mem_closedBall_zero_iff.mp hx)) hr.2;
    · intro w hw
      refine DifferentiableAt.smul ?_ ?_
      · refine DifferentiableAt.div ?_ ?_ ?_
        · exact differentiableAt_const _
        · apply DifferentiableAt.const_mul
          refine DifferentiableAt.sub (differentiableAt_const (1 : ℂ)) ?_
          exact DifferentiableAt.mul (differentiableAt_const (star z)) differentiableAt_id
        · exact aux_denom_ne_zero (ball_subset_closedBall hw.1)
      · refine DifferentiableAt.comp w ?_ ?_
        · refine hf.differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds ?_)
          rw [mem_ball_zero_iff]
          have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw.1
          calc ‖↑r * w‖  = ‖(r:ℂ)‖ * ‖w‖ := norm_mul _ _
            _ = r * ‖w‖                := by rw [norm_real, norm_eq_abs, abs_of_pos hr.1]
            _ < r * 1                    := mul_lt_mul_of_pos_left hw1 hr.1
            _ = r                        := mul_one r
            _ < 1                        := hr.2
        · exact differentiableAt_id.const_mul _
 -- #count_heartbeats! in simp_all [circleIntegral, mul_assoc, mul_comm, mul_left_comm]
  convert h_cauchy using 3
  rw [circleIntegral_def_Icc]
  rw [intervalIntegral.integral_of_le]
  · congr 1
    · apply MeasureTheory.Measure.restrict_congr_set
      exact MeasureTheory.Ioc_ae_eq_Icc
    · funext θ
      simp only [circleMap_zero, deriv_circleMap]
      rw [smul_smul, h_integrand θ,  ofReal_one, one_mul,smul_smul]
      apply congrArg (fun x => x • f (r * cexp (θ * I)))
      rw [mul_comm I]
  · exact mul_nonneg zero_le_two Real.pi_pos.le

-- #count_heartbeats in
/-- For a sequence `r_n → 1` with `r_n ∈ (0,1)`,
the integral of `t ↦ k(e^{it}) f(r_n * e^{it})` on [0 , 2π] converges to
the integral of `t ↦ k(e^{it}) f(e^{it})` on [0 , 2π],
when `f` is continuous on the closed unit disc and `k` is continuous on the unit circle. -/
theorem tendsto_integral_boundary_unitDisc_of_continuousOn
    (hf : ContinuousOn f (closedBall (0 : ℂ) 1))
    (k : ℂ → ℂ) (hk : ContinuousOn k (sphere (0 : ℂ) 1))
    (r : ℕ → ℝ) (hr : ∀ n, r n ∈ Ioo 0 1) (hr_lim : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => ∫ t in 0..2 * π, (k (exp (t * I))) • f (r n * exp (t * I)))
           atTop (𝓝 (∫ t in 0..2 * π, (k (exp (t * I))) • f (exp (t * I)))) := by
  -- -- We apply the Lebesgue Dominated Convergence Theorem.
  have hrn (n : ℕ) (t : ℝ) : (r n) * cexp (t * I) ∈ closedBall 0 1  := by
      rw [mem_closedBall, dist_zero_right, norm_mul, norm_real,
            norm_eq_abs, norm_exp_ofReal_mul_I, mul_one, abs_of_pos (hr n).1]
      exact LT.lt.le (hr n).2
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
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
        rw [mem_sphere, dist_zero_right, norm_exp_ofReal_mul_I]
    · exact ContinuousOn.comp_continuous (s:= closedBall 0 1) hf (by fun_prop) (hrn n)
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
    apply Filter.Tendsto.comp (hf.continuousWithinAt _)
    · rw [tendsto_nhdsWithin_iff]
      constructor
      · simpa using Tendsto.mul
          (Complex.continuous_ofReal.continuousAt.tendsto.comp hr_lim) tendsto_const_nhds
      · apply Eventually.of_forall
        exact fun n => hrn n x
    · rw [mem_closedBall,dist_zero_right,norm_exp_ofReal_mul_I]

-- #count_heartbeats in
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

-- #count_heartbeats in
/-- For an analytic function `f` on the unit disc, `f(rz)` equals the integral
of `f(re^{it})` against the real part of the Herglotz kernel, where `r ∈ (0,1)`
and `z` is in the unit disc. -/
theorem poisson_formula_analytic_unitDisc [CompleteSpace E]
    (hf : AnalyticOn ℂ f (ball 0 1))
    (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    f (r * z) = (1 / (2 * π)) • ∫ t in 0..2*π,
       (((exp (t * I) + z) / (exp (t * I) - z)).re) • f (r * exp (t * I)) := by
  have h_exp_z (t : ℝ) : cexp (t * I) - z ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [← h,mem_ball,dist_zero_right, norm_exp_ofReal_mul_I] at hz
    exact (lt_self_iff_false 1).mp hz
  have h_add : f (r * z) = (1 / (2 * π)) • ∫ t in 0..2*π,
               (exp (t * I) / (exp (t * I) - z)) • f (r * exp (t * I))  +
               (star z / (star (exp (t * I)) - star z)) • f (r * exp (t * I)) := by
    have hr_exp (t : ℝ) : r * cexp (t * I) ∈ ball 0 1 := by
      simp only [mem_ball,Complex.dist_eq,sub_zero, norm_mul,norm_real,norm_eq_abs, abs_of_pos hr.1]
      simpa [mul_comm,norm_exp_ofReal_mul_I] using hr.2
    /- We add the integrals from `cauchy_integral_formula_unitDisc`
      and `goursat_vanishing_integral` to obtain the desired formula. -/
    rw [intervalIntegral.integral_add]
    · rw [cauchy_integral_formula_unitDisc hf hr hz, goursat_vanishing_integral hf hr hz, add_zero]
    · apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.smul ?_ ?_
      · exact ContinuousOn.div (Continuous.continuousOn (by fun_prop))
                               (Continuous.continuousOn (by fun_prop)) (fun t _ => h_exp_z t)
      · exact hf.continuousOn.comp (Continuous.continuousOn (by fun_prop)) (fun t _ => hr_exp t)
    · apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.smul ?_ ?_
      · exact ContinuousOn.div (Continuous.continuousOn continuous_const)
                               (Continuous.continuousOn (by fun_prop))
                               (fun t _ => by rw [← star_sub]; exact star_ne_zero.mpr (h_exp_z t))
      · exact hf.continuousOn.comp (by fun_prop) (fun t _ => hr_exp t)
  convert h_add using 3
  ext t
  rw [← add_smul]
  apply congrArg (fun (x : ℂ) => x • f (r * cexp (t * I)))
  rw [real_part_herglotz_kernel (exp (t * I)) z (by rw [norm_exp_ofReal_mul_I])]
  dsimp
  simp only [← star_def, ← star_sub]
  rw [div_add_div _ _ (h_exp_z t) (star_ne_zero.mpr (h_exp_z t))]
  simp only [star_def, mul_conj,normSq_eq_norm_sq]
  simp only [ofReal_div, ofReal_sub, ofReal_one, ofReal_pow, map_sub]
  apply congrArg (fun (x : ℂ) => x / ‖(exp (t * I) - z)‖^2)
  have : star (exp (t * I)) = (exp (t * I))⁻¹ := by
    rw [star_def, ← exp_conj, ← exp_neg (t * I)]
    apply congrArg cexp
    simp only [map_mul, conj_ofReal, conj_I, mul_neg]
  simp only [← star_def, this,mul_sub,sub_mul]
  simp only [ne_eq, Complex.exp_ne_zero, not_false_eq_true, mul_inv_cancel₀, star_def,
             mul_conj, normSq_eq_norm_sq z, ofReal_pow, sub_add_sub_cancel]

open InnerProductSpace

-- #count_heartbeats in
/-- For a harmonic function `u` on the unit disc, `u(rz)` equals the integral
of `u(r e^{it})` times the real part of the Herglotz kernel, where `r ∈ (0,1)`
and `z` is in the unit disc. -/
theorem harmonic_representation_scaled_radius
    (hu : HarmonicOnNhd u (ball 0 1))
    (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    u (r * z) = (1 / (2 * Real.pi)) * ∫ t in (0)..(2 * Real.pi),
      (((exp (t * I) + z) / (exp (t * I) - z))).re * (u (r * exp (t * I))) := by
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
  rw [← hf_eq hrz]
  have hrt (t : ℝ) : r * exp (t * I) ∈ ball 0 1 := by
    simp only [mem_ball, dist_zero_right, norm_mul, norm_real, norm_eq_abs, abs_of_pos hr.1,
               norm_exp_ofReal_mul_I, mul_one, hr.2]
  -- We replace `u(rz)` by `Re(f(rz))`.
  have hrt_eq : EqOn
    (fun t : ℝ => ((exp (t * I) + z) / (exp (t * I) - z)).re *(f (r * exp (t * I))).re)
    (fun t : ℝ => ((exp (t * I) + z) / (exp (t * I) - z)).re * u (r * exp (t * I)))
    (uIcc 0 (2 * Real.pi)) := by
    intro t _
    simp only [← hf_eq (hrt t)]
  rw [← intervalIntegral.integral_congr hrt_eq]
  dsimp
  rw [congr_arg Complex.re (poisson_formula_analytic_unitDisc hf hr hz), smul_re, smul_eq_mul]
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
      rw [← hexpz,mem_ball,dist_zero_right, norm_exp_ofReal_mul_I] at hz
      exact (lt_self_iff_false 1).mp hz
    · exact hf.continuousOn.comp (Continuous.continuousOn (by fun_prop)) (fun t _ => hrt t)
