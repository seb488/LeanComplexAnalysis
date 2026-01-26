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

open Set Complex Metric

variable {z : ℂ} {r : ℝ} {f : ℂ → ℂ} {u : ℂ → ℝ}

#count_heartbeats in
/-- Cauchy's integral formula for analytic functions on the unit disc,
    evaluated at scaled points `r * z` with `r ∈ (0,1)`. -/
private lemma cauchy_integral_formula_unitDisc
    (hf : AnalyticOn ℂ f (ball 0 1)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    f (r * z) = (1 / (2 * Real.pi)) * ∫ t in 0..2*Real.pi,
      f (r * exp (I * t)) * (exp (I * t) / (exp (I * t) - z)) := by
  norm_num at *
  have h_cauchy :
    f (r * z) = (1 / (2 * Real.pi * I)) * ∮ (ζ : ℂ) in C(0, 1), (f (r * ζ)) / (ζ - z) := by
    have := @Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    -- We apply the Cauchy Integral Formula to the function `z ↦ f(rz)`.
    specialize @this ℂ _ _ _ 1 0 z (fun ζ => f (r * ζ)) {0}
    norm_num at this
    simp_all [div_eq_inv_mul]
    rw [this]
    · ring_nf; norm_num [Real.pi_ne_zero]
    · refine ContinuousOn.comp hf.continuousOn ?_ ?_
      · exact continuousOn_const.mul continuousOn_id
      · intro w hw
        simp only [Metric.mem_ball, Complex.dist_eq]
        simp only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hw
        simp [abs_of_pos hr.1]
        calc r * ‖w‖ ≤ r := by nlinarith [hr.1, hw]
        _ < 1 := hr.2
    · intro x hx hx'
      exact DifferentiableAt.comp x (hf.differentiableOn.differentiableAt
        (Metric.isOpen_ball.mem_nhds (show ↑r * x ∈ ball 0 1 by
          simp only [Metric.mem_ball, Complex.dist_eq, sub_zero]
          simp [abs_of_pos hr.1]
          calc r * ‖x‖ < r := by nlinarith [hr.1, hx]
          _ < 1 := hr.2))) (differentiableAt_id.const_mul _)
  -- We convert the circle integral to the desired integral.
  convert h_cauchy using 1
  norm_num [circleIntegral, circleMap, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv]
  norm_num [← mul_assoc]

-- #count_heartbeats in
/-- Cauchy-Goursat theorem for the unit disc implies the integral of an analytic function
against the conjugate Cauchy kernel vanishes. -/
private lemma goursat_vanishing_integral
    (hf : AnalyticOn ℂ f (ball 0 1)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    ∫ t in 0..2*Real.pi, f (r * exp (I * t)) *
      (star z / (star (exp (I * t)) - star z)) = 0 := by
  -- We show that an equivalent integral vanishes, using the Cauchy-Goursat Theorem.
  have h_goursat : ∫ t in (0 : ℝ)..2 * Real.pi, f (r * exp (I * t)) *
    (exp (I * t)) / (1 - star z * exp (I * t)) = 0 := by
    -- We prove that for any analytic function `g` on the closed unit disc,
    -- the integral of `g(e^{it}) e^{it}` vanishes.
    have h_goursat_g (g : ℂ → ℂ) (hg_analytic : AnalyticOn ℂ g (closedBall 0 1)) :
      ∫ t in (0 : ℝ)..2 * Real.pi, g (exp (I * t)) * exp (I * t) = 0 := by
      -- The above integral equals a circle integral.
      have : ∫ t in (0 : ℝ)..2 * Real.pi, g (exp (I * t)) *
        exp (I * t) = (1 / I) * ∮ t in C(0, 1), g t := by
        norm_num [circleIntegral, circleMap, mul_comm]
        norm_num [mul_assoc, mul_comm, mul_left_comm]
        norm_num [← mul_assoc]
      rw [this]
      -- We apply the Cauchy-Goursat Theorem for a disc.
      simpa using @Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
                     ℂ _ _ 1 zero_le_one g 0 ∅ (by norm_num) (hg_analytic.continuousOn)
                    (by intro z hz
                        exact hg_analytic.differentiableOn.differentiableAt
                                              (Metric.closedBall_mem_nhds_of_mem hz.1))
    -- We apply h_goursat_g to the function `w ↦ f(rw) / (1 - star z * w)`.
    convert h_goursat_g (fun w => f (r * w) / (1 - star z * w)) _ using 3
    · ring
    · refine AnalyticOn.div ?_ ?_ ?_
      · refine hf.comp ?_ ?_
        · apply_rules [AnalyticOn.mul, analyticOn_const, analyticOn_id]
        · simp_all [Set.MapsTo]
          exact fun x hx => by rw [abs_of_pos hr.1] ; nlinarith [norm_nonneg x]
      · apply_rules [AnalyticOn.sub, AnalyticOn.mul, analyticOn_const, analyticOn_id]
      · intro x hx hxz
        simp [Complex.ext_iff] at hxz
        norm_num [Complex.normSq, Complex.norm_def] at hz hx
        rw [Real.sqrt_lt'] at hz <;> nlinarith [sq_nonneg (z.re * x.im - z.im * x.re)]
  -- We finish the proof by converting the integral in h_goursat back to the original integral.
  convert congr_arg (fun x : ℂ => x * star z) h_goursat using 1 <;> norm_num
  ring_nf
  rw [← intervalIntegral.integral_const_mul]
  congr
  ext t
  norm_num [exp_neg, exp_re, exp_im, mul_comm]
  ring_nf
  rw [show (-(starRingEnd ℂ z) + starRingEnd ℂ (exp (I * t))) =
           (1 - exp (I * t) * starRingEnd ℂ z) / exp (I * t) from ?_]
  · norm_num
    ring
  · rw [eq_div_iff (exp_ne_zero _)]
    norm_num [Complex.ext_iff, exp_re, exp_im]
    ring_nf
    rw [Real.sin_sq, Real.cos_sq]
    ring_nf
    trivial

#count_heartbeats in
/-- As `r → 1`, the Poisson integral of a continuous function `g` on the closed unit disc
converges to the boundary integral. More precisely, for a sequence `r_n → 1` with
`r_n ∈ (0,1)`, the integral against the real part of the Herglotz kernel converges. -/
private lemma poisson_integral_limit_to_boundary (g : ℂ → ℝ) (hz : z ∈ ball 0 1)
    (hc : ContinuousOn g (closedBall (0 : ℂ) 1)) (r : ℕ → ℝ)
    (hr : ∀ n, r n ∈ Ioo 0 1)
    (hr_lim : Filter.Tendsto r Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun n => (1 / (2 * Real.pi)) * ∫ t in 0..2 * Real.pi,
      (((exp (I * t) + z) / (exp (I * t) - z)).re)*g (r n * exp (I * t)))
        Filter.atTop (nhds ((1 / (2 * Real.pi)) * ∫ t in 0..2 * Real.pi,
          (((exp (I * t) + z) / (exp (I * t) - z)).re) * g (exp (I * t)))) := by
  field_simp
  -- We apply the Lebesgue Dominated Convergence Theorem.
  apply_rules [Filter.Tendsto.div_const,
                intervalIntegral.tendsto_integral_filter_of_dominated_convergence]
  rotate_right
  -- We define the bound to be the supremum of the integrand.
  · exact fun x => (SupSet.sSup (Set.image (fun w => |((w + z) / (w - z)).re|)
     (sphere 0 1))) * (SupSet.sSup (Set.image (fun w => |g w|) (closedBall (0 : ℂ) 1)))
  -- We verify the measurability of the integrand.
  · filter_upwards with n
    refine Measurable.aestronglyMeasurable ?_
    refine Measurable.mul ?_ ?_
    · fun_prop
    · refine Continuous.measurable ?_
      refine hc.comp_continuous ?_ ?_
      · continuity
      · simp_all
        linarith [hr n, abs_of_pos (hr n |>.1)]
  -- We verify that the integrand is eventually bounded by the bound.
  · refine Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun x hx => ?_
    -- We bound each factor of the integrand separately.
    have h_bound : |g (r n * exp (x * I))| ≤
      sSup (Set.image (fun w => |g w|) (closedBall (0 : ℂ) 1)) ∧
        |((exp (x * I) + z) / (exp (x * I) - z)).re| ≤
          sSup (Set.image (fun w => |((w + z) / (w - z)).re|) (sphere 0 1)) := by
      refine ⟨le_csSup ?_ ?_, le_csSup ?_ ?_⟩
      · have h_compact : IsCompact (closedBall (0 : ℂ) 1) :=  isCompact_closedBall (0 : ℂ) 1
        exact IsCompact.bddAbove (h_compact.image_of_continuousOn hc.abs)
      · refine ⟨_, ?_, rfl⟩
        simp_all
        linarith [hr n, abs_of_pos (hr n |>.1)]
      · have h_cont : ContinuousOn (fun w : ℂ => |((w + z) / (w - z)).re|) (sphere 0 1) := by
          refine ContinuousOn.abs (Complex.continuous_re.comp_continuousOn ?_)
          exact continuousOn_of_forall_continuousAt
            fun w hw => ContinuousAt.div (continuousAt_id.add continuousAt_const)
              (continuousAt_id.sub continuousAt_const) (sub_ne_zero_of_ne (by
                intro h_eq
                rw [h_eq] at hw
                simp only [Metric.mem_sphere, Complex.dist_eq, sub_zero] at hw
                have : ‖z‖ < 1 := by simpa using hz
                linarith))
        exact IsCompact.bddAbove (isCompact_sphere 0 1 |> IsCompact.image_of_continuousOn <| h_cont)
      · use (exp (x * I))
        constructor
        · simp [Metric.sphere, dist_eq_norm]
        · simp
    rw [norm_mul]
    -- We put the bounds together to obtain the desired bound.
    refine mul_le_mul ?_ ?_ ?_ ?_
    · rw [Real.norm_eq_abs]
      rw [mul_comm I (↑x : ℂ)]
      exact h_bound.2
    · rw [Real.norm_eq_abs]
      rw [mul_comm (cexp (I * ↑x)), mul_comm I (↑x : ℂ)]
      exact h_bound.1
    · norm_num
    · apply Real.sSup_nonneg
      intro b hb
      simp only [Set.mem_image] at hb
      obtain ⟨w, _, rfl⟩ := hb
      exact abs_nonneg _
  · norm_num -- The bound is integrable.
  -- We verify the pointwise convergence of the integrand.
  · refine Filter.Eventually.of_forall fun x hx => Filter.Tendsto.mul ?_ ?_
    · exact tendsto_const_nhds
    · apply_rules [Filter.Tendsto.comp (hc.continuousWithinAt _), tendsto_const_nhds]
      · rw [tendsto_nhdsWithin_iff]
        have h_tendsto : Filter.Tendsto (fun n => (r n : ℂ) * exp (I * x))
          Filter.atTop (nhds (exp (I * x))) := by
          simpa using Filter.Tendsto.mul
            (Complex.continuous_ofReal.continuousAt.tendsto.comp hr_lim) tendsto_const_nhds
        simp_all
        refine ⟨?_, 0, fun b _ => ?_⟩
        · convert h_tendsto using 1; ext n; ring
        · rw [abs_of_pos (hr b).1]; linarith [(hr b).2]
      · simp

-- #count_heartbeats in
/-- For an analytic function `f` on the unit disc, `f(rz)` equals the integral
of `f(re^{it})` against the real part of the Herglotz kernel, where `r ∈ (0,1)`
and `z` is in the unit disc. -/
private lemma poisson_formula_analytic_unitDisc
    (hf : AnalyticOn ℂ f (ball 0 1))
    (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    f (r * z) = (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..2 * Real.pi,
      f (r * exp (I * t)) * (((exp (I * t) + z) / (exp (I * t) - z)).re) := by
  have h_add : f (r * z) = (1 / (2 * Real.pi)) * (∫ t in (0 : ℝ)..2 * Real.pi,
    f (r * exp (I * t)) * (exp (I * t) / (exp (I * t) - z)) +
      f (r * exp (I * t)) * (star z / (star (exp (I * t)) - star z))) := by
    /- We add the integrals from `cauchy_integral_formula_unitDisc`
      and `goursat_vanishing_integral` to obtain the desired formula. -/
    rw [intervalIntegral.integral_add]
    · rw [cauchy_integral_formula_unitDisc hf hr hz, goursat_vanishing_integral hf hr hz]
      ring
    · apply_rules [ContinuousOn.intervalIntegrable]
      refine ContinuousOn.mul ?_ ?_
      · refine hf.continuousOn.comp ?_ ?_
        · exact Continuous.continuousOn (by continuity)
        · intro t ht
          simp_all [abs_of_pos hr.1]
      · refine ContinuousOn.div ?_ ?_ ?_
        · exact Continuous.continuousOn (by continuity)
        · exact Continuous.continuousOn (by continuity)
        · intro x hx
          rw [Ne.eq_def, sub_eq_zero]
          intro H
          simp_all [Complex.ext_iff]
          have : cexp (I * ↑x) = z := Complex.ext H.1 H.2
          rw [← this] at hz
          simp at hz
    · apply_rules [ContinuousOn.intervalIntegrable]
      refine ContinuousOn.mul ?_ ?_
      · refine hf.continuousOn.comp ?_ ?_
        · fun_prop
        · simp_all [Set.MapsTo, abs_of_pos hr.1]
      · refine continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div ?_ ?_ ?_
        · exact continuousAt_const
        · fun_prop (disch := norm_num)
        · simp_all [sub_eq_iff_eq_add, Complex.ext_iff]
          intro h₁ h₂; have := Complex.normSq_apply z
          simp_all +decide [Complex.normSq]
          have : cexp (I * ↑t) = z := Complex.ext h₁ h₂
          rw [← this] at hz
          simp at hz
  convert h_add using 3
  ext t
  rw [← mul_add]
  have : let eit := exp (I * t)
    (eit / (eit - z)) + (star z / (star eit - star z)) = (((eit + z) / (eit - z)).re : ℂ) := by
      norm_num [Complex.ext_iff, div_eq_mul_inv]
      simp [Complex.normSq]
      grind
  rw [← this]

open InnerProductSpace

-- #count_heartbeats in
/-- For a harmonic function `u` on the unit disc, `u(rz)` equals the integral
of `u(r e^{it})` times the real part of the Herglotz kernel, where `r ∈ (0,1)`
and `z` is in the unit disc. -/
lemma harmonic_representation_scaled_radius
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
    simp [abs_of_pos hr.1]
    have := mul_lt_mul_of_le_of_lt_of_pos_of_nonneg (hr.2.le) hz.out (hr.1) (by norm_num)
    simp_all
  -- We replace `u(rz)` by `Re(f(rz))`.
  rw [← hf_eq hrz]
  have hrt (t : ℝ) : r * exp (I * t) ∈ ball 0 1 := by
    simp [abs_of_pos hr.1]
    exact hr.2
  have hrt : EqOn
    (fun t : ℝ => ((exp (I * t) + z) / (exp (I * t) - z)).re *(f (r * exp (I * t))).re)
      (fun t : ℝ => ((exp (I * t) + z) / (exp (I * t) - z)).re * u (r * exp (I * t)))
        (uIcc 0 (2 * Real.pi)) := by
    intro t _
    dsimp
    rw [← hf_eq (hrt t)]
  dsimp
  have := intervalIntegral.integral_congr (μ := MeasureTheory.volume) hrt
  rw [← this]
  -- We apply the Poisson integral formula for analytic functions on the unit disc.
  have h_real : (f (r * z)).re = (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..2 * Real.pi,
    ((f (r * exp (I * t)) * (((exp (I * t) + z) / (exp (I * t) - z)).re : ℂ)).re) := by
    convert congr_arg Complex.re (poisson_formula_analytic_unitDisc hf hr hz) using 1
    norm_num [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    convert integral_re _
    any_goals tauto
    · norm_num [Complex.ext_iff]
    · refine ContinuousOn.integrableOn_Icc ?_ |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self
      refine ContinuousOn.mul ?_ ?_
      · refine hf.continuousOn.comp ?_ ?_
        · exact Continuous.continuousOn (by continuity)
        · intro t ht; simp_all
      · refine Continuous.continuousOn ?_
        refine Complex.continuous_ofReal.comp ?_
        refine Complex.continuous_re.comp ?_
        refine Continuous.div ?_ ?_ ?_
        · continuity
        · continuity
        · intro t
          rw [Ne.eq_def, sub_eq_zero]
          intro H
          simp_all [Complex.ext_iff]
          have : cexp (I * ↑t) = z := Complex.ext H.1 H.2
          rw [← this] at hz
          simp at hz
  convert h_real using 3
  norm_num [circleMap]
  ring_nf
  ac_rfl

#count_heartbeats in
/-- The real part of the Herglotz–Riesz kernel is equal to the Poisson kernel. -/
lemma real_part_herglotz_kernel {x w : ℂ} (hx : ‖x‖ = 1) :
    ((x + w) / (x - w)).re = (1 - ‖w‖^2) / ‖x - w‖^2 := by
  rw [Complex.div_re]
  norm_num [Complex.normSq, Complex.norm_def] at *
  rw [← add_div, Real.sq_sqrt, Real.sq_sqrt,← hx]
  · ring
  · nlinarith
  · nlinarith

-- #count_heartbeats in
/-- **Poisson integral formula for harmonic functions on the unit disc**:
A function `u` harmonic on the unit disc and continuous on the closed unit disc
satisfies `u(z) = (1/2π) ∫_0^{2π} (1 - |z|²) / |e^{it} - z|² u(e^{it}) dt`
for `z` in the unit disc. -/
theorem poisson_integral_formula
    (hu : HarmonicOnNhd u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (z : ℂ) (hz : z ∈ ball 0 1) :
    u z = (1 / (2 * Real.pi)) * ∫ t in 0..(2 * Real.pi),
      (1 - ‖z‖^2) / ‖(exp (I * t)) - z‖^2 * (u (exp (I * t))) := by
  -- We approximate `1` by a sequence `r_n` in `(0,1)`.
  let r : ℕ → ℝ := fun n => 1 - 1 / (n + 2)
  have hr (n : ℕ): r n ∈ Ioo 0 1 := by
    simp [r]
    constructor
    · have : (1 : ℝ) < (↑n+2 : ℝ) := by linarith
      exact inv_lt_one_of_one_lt₀ this
    · linarith
  have hr_lim : Filter.Tendsto r Filter.atTop (nhds 1) := by
    exact le_trans (tendsto_const_nhds.sub
                    <| tendsto_const_nhds.div_atTop
                    <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
          <| by norm_num
  -- We express `u(r_n z)` as the Poisson integral and then take the limit.
  have hu_lim := poisson_integral_limit_to_boundary u hz hc r hr hr_lim
  have h_poisson (n : ℕ) := harmonic_representation_scaled_radius hu (hr n) hz
  have hu_lim : Filter.Tendsto (fun n => u (r n * z))
    Filter.atTop (nhds ((1 / (2 * Real.pi)) * ∫ t in 0..2 * Real.pi,
      (((exp (I * t) + z) / (exp (I * t) - z)).re) * u (exp (I * t)))) := by
    simp_rw [h_poisson]
    exact hu_lim
  -- We show that `u (r_n z)` tends to `u z` as `n → ∞`.
  have hu_lim' : Filter.Tendsto (fun n => u (r n * z)) Filter.atTop (nhds (u z)) := by
    have h_cont : Filter.Tendsto (fun n => r n  * z) Filter.atTop (nhds z) := by
      simpa using Filter.Tendsto.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hr_lim)
        tendsto_const_nhds
    apply_rules [Filter.Tendsto.comp, hc]
    · simp
      exact le_of_lt (by simpa [Metric.mem_ball] using hz)
    · rw [tendsto_nhdsWithin_iff]
      simp_all
      use 0
      intro n _
      nlinarith [abs_of_pos (hr n).1,hr n]
  -- We conclude by uniqueness of limits and by revealing the Poisson kernel.
  rw [← tendsto_nhds_unique hu_lim hu_lim']
  field_simp
  apply_rules [intervalIntegral.integral_congr_ae]
  filter_upwards with t
  intro ht
  simp [real_part_herglotz_kernel]
  rw [mul_comm I ↑t]
  ring
