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

Theorems `poisson_integral_formula_harmonic` and
`poisson_integral_formula_harmonic_realPart_kernel`:
Every function `u : ℂ → ℝ`
harmonic on the unit disc and continuous on the closed unit disc can be represented as
```
u(z) = 1/(2π) ∫_0^{2π} (1 - |z|^2) / |e^{it} - z|^2 * u(e^{it}) dt
     = 1/(2π) ∫_0^{2π} Re((e^{it} + z) / (e^{it} - z)) * u(e^{it}) dt,
```
for `z` in the unit disc.

Theorem `poisson_integral_formula_analytic` and
`poisson_integral_formula_analytic_realPart_kernel`:
Every function `f : ℂ → E` analytic on the unit disc, continuous on the closed unit disc,
with values in a complex Banach space `E`, can be represented as
```
f(z) = 1/(2π) ∫_0^{2π} (1 - |z|^2) / |e^{it} - z|^2 • f(e^{it}) dt
     = 1/(2π) ∫_0^{2π} Re((e^{it} + z) / (e^{it} - z)) • f(e^{it}) dt,
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

-- set_option linter.all true

public section

open Complex Metric Real Set

-- #count_heartbeats in-- 600 hb
/- Scaling a point in the closed unit ball by r in (0,1) remains in the unit ball. -/
lemma norm_le_one_scaled_mem_ball {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ 1) (hr : r ∈ Ioo 0 1) :
    r * z ∈ ball 0 1 := by
  rw [mem_ball, dist_zero_right, norm_mul, norm_real, norm_eq_abs, abs_of_pos hr.1]
  have := mul_le_of_le_one_left (LT.lt.le hr.1) hz
  rw [mul_comm] at this
  exact LE.le.trans_lt this hr.2

-- #count_heartbeats in -- 650 hb
/- r* exp (t * I) is in the unit disc for r ∈ (0,1). -/
lemma exp_ofReal_mul_I_in_unitDisc {r : ℝ} (hr : r ∈ Ioo 0 1) (t : ℝ) :
  r * exp (t * I) ∈ ball 0 1 := by
  refine norm_le_one_scaled_mem_ball ?_ hr
  rw [norm_exp_ofReal_mul_I]

-- #count_heartbeats in -- 600 hb
/- exp (t * I) is not equal to any z in the unit disc. -/
lemma exp_ofReal_mul_I_not_in_ball {z : ℂ} (hz : z ∈ ball 0 1) (t : ℝ) : exp (t * I) - z ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  rw [← h, mem_ball, dist_zero_right, norm_exp_ofReal_mul_I] at hz
  exact (lt_self_iff_false 1).mp hz

-- #count_heartbeats in -- 2000 hb
/- 1 - star z * w ≠ 0, for z in unit disc and w in closed unit disc -/
lemma one_sub_star_mul_neq_zero {z : ℂ} {w : ℂ} (hz : z ∈ ball 0 1) (hw : w ∈ closedBall 0 1) :
    1 - star z * w ≠ 0 := by
  intro h
  have hz_norm : ‖z‖ < 1 := by rw [mem_ball_zero_iff] at hz; exact hz
  have hw_norm : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
  have : ‖star z * w‖ < 1 := by
    calc ‖star z * w‖ ≤ ‖star z‖ * ‖w‖ := norm_mul_le _ _
      _ = ‖z‖ * ‖w‖ := by rw [norm_star]
      _ < 1 := by nlinarith [norm_nonneg z, norm_nonneg w]
  rw [sub_eq_zero] at h
  rw [← h] at this
  rw [norm_one] at this
  exact absurd this (lt_irrefl 1)

-- #count_heartbeats in -- 1200 hb
/- If f is analytic on the unit disc, then ζ ↦ f (r * ζ) is differentiable at z
  for r in (0,1) and z in the closed unit ball. -/
lemma analyticOn_unitDisc_differentiableAt_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {z : ℂ} {r : ℝ}
    (hf : AnalyticOn ℂ f (ball 0 1)) (hz : z ∈ closedBall 0 1) (hr : r ∈ Ioo 0 1) :
    DifferentiableAt ℂ (fun ζ => f (r * ζ)) z := by
  rw [mem_closedBall, dist_zero_right] at hz
  exact DifferentiableAt.comp z (hf.differentiableOn.differentiableAt
        (isOpen_ball.mem_nhds (norm_le_one_scaled_mem_ball hz hr)))
        (differentiableAt_id.const_mul _)

-- #count_heartbeats in -- 2200 hb
/- Cauchy integral formula applied to f analytic on the unit disc at the point r*z,
for r in (0,1) and z in the ball 0 1. -/
lemma cauchy_circleIntegral_formula_unitDisc_scaled {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {z : ℂ} {r : ℝ}
    (hf : AnalyticOn ℂ f (ball 0 1)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    f (r * z) = (1 / (2 * π * I)) • ∮ (ζ : ℂ) in C(0, 1), (1 / (ζ - z)) • f (r * ζ) := by
    have hfr_cont : ContinuousOn (fun ζ => f (r * ζ)) (closedBall 0 1) :=
      fun x hx => (DifferentiableAt.continuousAt
                   (analyticOn_unitDisc_differentiableAt_mul hf hx hr)).continuousWithinAt
    have := @circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      _ _ _ _ 1 0 z (fun ζ => f (r * ζ)) ∅ countable_empty hz hfr_cont
    simp only [div_eq_inv_mul, mul_one]
    rw [this]
    · simp only [smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero]
      exact Eq.symm (MulAction.one_smul (f (r * z)))
    · intro x hx
      simp only [diff_empty] at hx
      exact analyticOn_unitDisc_differentiableAt_mul hf (ball_subset_closedBall hx) hr

-- #count_heartbeats in -- 7200 hb
/-- Cauchy's integral formula for analytic functions on the unit disc,
    evaluated at scaled points `r * z` with `r ∈ (0,1)`. -/
lemma cauchy_integral_formula_unitDisc_scaled {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {z : ℂ} {r : ℝ}
    (hf : AnalyticOn ℂ f (ball 0 1)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    f (r * z) = (1 / (2 * π)) • ∫ t in 0..2 * π,
                (exp (t * I) / (exp (t * I) - z)) • (f (r * exp (t * I))) := by
  have h_cauchy := cauchy_circleIntegral_formula_unitDisc_scaled hf hr hz
  rw [← circleIntegral.integral_smul] at h_cauchy
  rw [← intervalIntegral.integral_smul, h_cauchy]
  simp only [circleIntegral]
  congr 1
  ext t
  have : f (r * circleMap 0 1 t) = f (r * exp (t * I)) := by simp [circleMap]
  rw [this]
  simp only [← smul_assoc]
  have : (deriv (circleMap 0 1) t • (1 / (2 * π * I))) • (1 / (circleMap 0 1 t - z)) =
         ((1 / (2 * π)) • (exp (t * I) / (exp (t * I) - z))) := by
    simp only [deriv_circleMap, circleMap, ofReal_one, one_mul, zero_add, mul_inv_rev,
              div_eq_inv_mul, smul_eq_mul, real_smul, ofReal_mul,
              ofReal_inv, ofReal_ofNat, mul_one, mul_assoc]
    rw [← mul_assoc I I⁻¹, mul_inv_cancel₀ I_ne_zero, one_mul]
    ring_nf
  rw [this]

-- #count_heartbeats in --2200 hb
/- If f is analytic on the unit disc, then ζ ↦ (star z / (I * (1 - star z * ζ))) • (f (r * ζ)))
 is differentiable at w in the closed unit disc, for r in (0,1). -/
lemma goursat_integrand_diffferentiableAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {z w : ℂ} {r : ℝ} (hf : AnalyticOn ℂ f (ball 0 1))
    (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) (hw : w ∈ closedBall 0 1) :
    DifferentiableAt ℂ (fun ζ => (star z / (I * (1 - star z * ζ))) • (f (r * ζ))) w := by
    refine DifferentiableAt.smul ?_ ?_
    · refine DifferentiableAt.div (differentiableAt_const _) ?_ ?_
      · apply DifferentiableAt.const_mul
        refine DifferentiableAt.sub (differentiableAt_const (1 : ℂ)) ?_
        exact DifferentiableAt.mul (differentiableAt_const (star z)) differentiableAt_id
      · exact mul_ne_zero I_ne_zero (one_sub_star_mul_neq_zero hz hw)
    · exact analyticOn_unitDisc_differentiableAt_mul hf hw hr

-- #count_heartbeats in  -- 1200 hb
/- We apply the Cauchy-Goursat theorem to the function
(fun ζ => (star z / (I * (1 - star z * ζ))) • (f (r * ζ))) on the unit circle. -/
lemma goursat_vanishing_integral_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {z : ℂ} {r : ℝ}
    (hf : AnalyticOn ℂ f (ball 0 1)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    (∮ w in C(0, 1), (star z / (I * (1 - star z * w))) • (f (r * w))) = 0 := by
  apply circleIntegral_eq_zero_of_differentiable_on_off_countable (zero_le_one) countable_empty
  · exact fun ζ hζ => (DifferentiableAt.continuousAt
                      (goursat_integrand_diffferentiableAt hf hr hz hζ)).continuousWithinAt
  · rw [diff_empty]
    exact fun ζ hζ => goursat_integrand_diffferentiableAt hf hr hz (ball_subset_closedBall hζ)

-- #count_heartbeats in -- 3500 hb
/- Algebraic identity that will be used in integrand of the Cauchy-Goursat theorem. -/
lemma goursat_integrand_eq (z : ℂ) (t : ℝ) : star z / (star (exp (t * I)) - star z) =
                    (I * exp (t * I)) * (star z / (I * (1 - star z * exp (t * I)))) := by
  have : star (exp (t * I)) = (exp (t * I))⁻¹ := by
    rw [star_def, ← exp_conj, ← exp_neg (t * I)]
    congr 1
    simp only [map_mul, conj_ofReal, conj_I, mul_neg]
  simp only [this]
  rw [mul_comm I, mul_assoc, ← mul_div_assoc, mul_div_mul_left (hc := I_ne_zero), ← mul_div_assoc,
      mul_comm (exp (t * I)), mul_div_assoc, div_eq_mul_inv (star z)]
  congr 1
  rw [inv_eq_one_div]
  nth_rewrite 2 [← inv_inv (exp (t * I)), inv_eq_one_div]
  rw [div_div, mul_sub, mul_one, mul_comm (star z), ← mul_assoc,
      inv_mul_cancel₀ (Complex.exp_ne_zero (t * I)), one_mul]

-- #count_heartbeats in -- 2800 hb
/-- Cauchy-Goursat theorem for the unit disc implies the integral of an analytic function
against the conjugate Cauchy kernel vanishes. -/
lemma goursat_vanishing_integral_unitDisc_scaled {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {z : ℂ} {r : ℝ}
    (hf : AnalyticOn ℂ f (ball 0 1)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    ∫ t in 0..2 * π, (star z / (star (exp (t * I)) - star z)) • f (r * exp (t * I)) = 0 := by
  convert (goursat_vanishing_integral_aux hf hr hz) using 3
  rw [circleIntegral_def_Icc]
  rw [intervalIntegral.integral_of_le (mul_nonneg zero_le_two pi_pos.le)]
  congr 1
  · exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc
  · funext θ
    simp only [circleMap_zero, deriv_circleMap]
    rw [goursat_integrand_eq z θ, smul_smul, ofReal_one, one_mul]
    congr 1
    rw [mul_comm I]

-- #count_heartbeats in -- 6500 hb
/- We put together `goursat_vanishing_integral_unitDisc_scaled` and
  `cauchy_integral_formula_unitDisc_scaled` -/
lemma cauchy_goursat_integral_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {z : ℂ} {r : ℝ}
    (hf : AnalyticOn ℂ f (ball 0 1)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    f (r * z) = (1 / (2 * π)) • ∫ t in 0..2 * π,
              (exp (t * I) / (exp (t * I) - z)) • f (r * exp (t * I)) +
              (star z / (star (exp (t * I)) - star z)) • f (r * exp (t * I)) := by
  rw [intervalIntegral.integral_add]
  · rw [cauchy_integral_formula_unitDisc_scaled hf hr hz,
        goursat_vanishing_integral_unitDisc_scaled hf hr hz, add_zero]
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.smul ?_ ?_
    · exact ContinuousOn.div (Continuous.continuousOn (by fun_prop))
                               (Continuous.continuousOn (by fun_prop))
                               (fun t _ => exp_ofReal_mul_I_not_in_ball hz t)
    · exact hf.continuousOn.comp (Continuous.continuousOn (by fun_prop))
              (fun t _ => exp_ofReal_mul_I_in_unitDisc hr t)
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.smul ?_ ?_
    · exact ContinuousOn.div (Continuous.continuousOn continuous_const)
              (Continuous.continuousOn (by fun_prop))
              (fun t _ => by rw [← star_sub];
                             exact star_ne_zero.mpr (exp_ofReal_mul_I_not_in_ball hz t))
    · exact hf.continuousOn.comp (by fun_prop)
                (fun t _ => exp_ofReal_mul_I_in_unitDisc hr t)

-- #count_heartbeats in --5200 hb
/-- For an analytic function `f : ℂ → E` on the unit disc, `f(rz)` equals the integral
of `f(re^{it})` against the real part of the Herglotz kernel, where `r ∈ (0,1)`
and `z` is in the unit disc. -/
theorem poisson_formula_analytic_scaled_radius {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {z : ℂ} {r : ℝ}
    (hf : AnalyticOn ℂ f (ball 0 1))
    (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    f (r * z) = (1 / (2 * π)) • ∫ t in 0..2 * π,
      ((1 - ‖z‖ ^ 2) / ‖exp (t * I) - z‖ ^ 2) • f (r * exp (t * I)) := by
  convert cauchy_goursat_integral_aux hf hr hz using 3
  ext t
  rw [← add_smul]
  apply congrArg (fun (x : ℂ) => x • f (r * exp (t * I)))
  dsimp
  simp only [← star_def, ← star_sub]
  rw [div_add_div _ _ (exp_ofReal_mul_I_not_in_ball hz t)
                      (star_ne_zero.mpr (exp_ofReal_mul_I_not_in_ball hz t))]
  simp only [star_def, mul_conj, normSq_eq_norm_sq]
  simp only [ofReal_div, ofReal_sub, ofReal_one, ofReal_pow, map_sub]
  congr 1
  have : star (exp (t * I)) = (exp (t * I))⁻¹ := by
    rw [star_def, ← exp_conj, ← exp_neg (t * I)]
    congr 1
    simp only [map_mul, conj_ofReal, conj_I, mul_neg]
  simp only [← star_def, this, mul_sub, sub_mul]
  simp only [ne_eq, Complex.exp_ne_zero, not_false_eq_true, mul_inv_cancel₀, star_def,
             mul_conj, normSq_eq_norm_sq z, ofReal_pow, sub_add_sub_cancel]

open InnerProductSpace

-- #count_heartbeats in -- 7800 hb
/-- For a harmonic function `u` on the unit disc, `u(rz)` equals the integral
of `u(r e^{it})` times the real part of the Herglotz kernel, where `r ∈ (0,1)`
and `z` is in the unit disc. -/
theorem poisson_formula_harmonic_scaled_radius {u : ℂ → ℝ} {z : ℂ} {r : ℝ}
    (hu : HarmonicOnNhd u (ball 0 1))
    (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    u (r * z) = (1 / (2 * π)) * ∫ t in (0)..(2 * π),
      ((1 - ‖z‖ ^ 2) / ‖exp (t * I) - z‖ ^ 2) * (u (r * exp (t * I))) := by
  have hfu : ∃ (f : ℂ → ℂ), AnalyticOn ℂ f (ball 0 1) ∧
    EqOn (fun (z : ℂ) => (f z).re) u (ball 0 1) := by
    obtain ⟨f, hf⟩ := @harmonic_is_realOfHolomorphic u 0 1 hu
    use f
    exact ⟨hf.1.analyticOn, hf.2⟩
  obtain ⟨f, hf, hf_eq⟩ := hfu
  rw [← hf_eq (norm_le_one_scaled_mem_ball (LT.lt.le (mem_ball_zero_iff.mp hz)) hr)]
  -- We replace `u(rz)` by `Re(f(rz))`.
  have hrt_eq : EqOn
    (fun t : ℝ => ((1 - ‖z‖^2) / ‖exp (t * I) - z‖^2) * (f (r * exp (t * I))).re)
    (fun t : ℝ => ((1 - ‖z‖^2) / ‖exp (t * I) - z‖^2) * u (r * exp (t * I))) (uIcc 0 (2 * π)) :=
       fun t _ => by simp only [← hf_eq (exp_ofReal_mul_I_in_unitDisc hr t)]
  rw [← intervalIntegral.integral_congr hrt_eq]
  dsimp
  rw [congr_arg re (poisson_formula_analytic_scaled_radius hf hr hz), smul_re, smul_eq_mul]
  congr 1
  simp only [intervalIntegral.integral_of_le two_pi_pos.le]
  symm
  rw [← RCLike.re_eq_complex_re]
  convert integral_re _ using 1
  · simp only [real_smul, RCLike.mul_re, RCLike.re_to_complex, ofReal_re, RCLike.im_to_complex,
               ofReal_im, zero_mul, sub_zero]
  · refine ContinuousOn.integrableOn_Icc ?_ |> fun h => h.mono_set <| Ioc_subset_Icc_self
    refine ContinuousOn.smul ?_ ?_
    · exact Continuous.continuousOn (Continuous.div (by fun_prop) (by fun_prop)
              (fun t => by positivity [exp_ofReal_mul_I_not_in_ball hz t]))
    · exact hf.continuousOn.comp (Continuous.continuousOn (by fun_prop))
                                 (fun t _ => exp_ofReal_mul_I_in_unitDisc hr t)

open Filter Topology

-- #count_heartbeats in -- 5100 hb
/- We bound  t ↦ ‖k (exp (t * I)) • f (r * exp (t * I))‖, for
k continuous on the unit circle and f continuous on the closed unit disc. -/
lemma bounds_continuousOn_unitDisc_unitCircle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} {k : ℂ → ℝ} {r : ℝ} {t : ℝ} (hr : r ∈ Ioo 0 1)
    (hf : ContinuousOn f (closedBall 0 1)) (hk : ContinuousOn k (sphere 0 1)) :
    ‖k (exp (t * I)) • f (r * exp (t * I))‖ ≤
    sSup ((fun ζ ↦ |k ζ|) '' sphere 0 1) * sSup ((fun w ↦ ‖f w‖) '' closedBall 0 1) := by
    have h_bds :
        ‖f (r * exp (t * I))‖ ≤ sSup (image (fun w => ‖f w‖) (closedBall 0 1)) ∧
        ‖k (exp (t * I))‖ ≤ sSup (image (fun w => ‖k w‖) (sphere 0 1)) := by
      refine ⟨le_csSup ?_ ?_, le_csSup ?_ ?_⟩
      · exact IsCompact.bddAbove (isCompact_closedBall 0 1 |>.image_of_continuousOn hf.norm)
      · exact ⟨_, ball_subset_closedBall (exp_ofReal_mul_I_in_unitDisc hr t), rfl⟩
      · exact IsCompact.bddAbove (IsCompact.image_of_continuousOn (isCompact_sphere 0 1) hk.norm)
      · exact ⟨exp (t * I), ⟨by simp only [mem_sphere_zero_iff_norm, norm_exp_ofReal_mul_I], rfl⟩⟩
    have hmul_bds : |k (exp (t * I))| * ‖f (r * exp (t * I))‖ ≤
      (sSup (image (fun ζ => |k ζ|) (sphere 0 1))) *
      (sSup (image (fun w => ‖f w‖) (closedBall 0 1))) := by
         apply mul_le_mul h_bds.2 h_bds.1 (norm_nonneg (f (r * exp (t * I))))
         apply sSup_nonneg
         rintro _ ⟨_, ⟨_, hx⟩⟩
         simp_rw [← hx, norm_nonneg]
    have hmul_norm : ‖k (exp (t * I)) • f (r * exp (t * I))‖ ≤
      ‖k (exp (t * I))‖ * ‖f (r * exp (t * I))‖ := by rw [norm_smul]
    exact le_trans hmul_norm hmul_bds

-- #count_heartbeats in -- 6700 hb
/-- For a sequence `r_n → 1` with `r_n ∈ (0,1)`,
the integral of `t ↦ k(e^{it}) f(r_n * e^{it})` on [0 , 2π] converges to
the integral of `t ↦ k(e^{it}) f(e^{it})` on [0 , 2π],
when `f` is continuous on the closed unit disc and `k` is continuous on the unit circle,
by the Lebesgue Dominated Convergence Theorem. -/
lemma tendsto_integral_prod_of_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} {k : ℂ → ℝ} {r : ℕ → ℝ}
    (hf : ContinuousOn f (closedBall 0 1)) (hk : ContinuousOn k (sphere 0 1))
    (hr : ∀ n, r n ∈ Ioo 0 1) (hr_lim : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => ∫ t in 0..2 * π, (k (exp (t * I))) • f (r n * exp (t * I)))
      atTop (𝓝 (∫ t in 0..2 * π, (k (exp (t * I))) • f (exp (t * I)))) := by
  have hrn (n : ℕ) (t : ℝ) : (r n) * exp (t * I) ∈ closedBall 0 1 :=
      ball_subset_closedBall (exp_ofReal_mul_I_in_unitDisc (hr n) t)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
  rotate_right
  -- We define the bound to be the supremum of the integrand.
  · exact fun x => sSup ((fun ζ ↦ |k ζ|) '' sphere 0 1) * sSup ((fun w ↦ ‖f w‖) '' closedBall 0 1)
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
  · exact Eventually.of_forall fun n => Eventually.of_forall fun t ht =>
             bounds_continuousOn_unitDisc_unitCircle (hr n) hf hk
  · simp only [ne_eq, enorm_ne_top, not_false_eq_true, intervalIntegrable_const]
  -- We verify the pointwise convergence of the integrand.
  · refine Eventually.of_forall fun x hx => Tendsto.smul tendsto_const_nhds ?_
    apply Tendsto.comp (hf.continuousWithinAt _)
    · rw [tendsto_nhdsWithin_iff]
      constructor
      · simpa using Tendsto.mul
          (continuous_ofReal.continuousAt.tendsto.comp hr_lim) tendsto_const_nhds
      · exact Eventually.of_forall (fun n => hrn n x)
    · rw [mem_closedBall,dist_zero_right,norm_exp_ofReal_mul_I]

-- #count_heartbeats in -- 2100 hb
/-- The Poisson kernel is continuous on the unit circle. -/
theorem poisson_kernel_continousOn_circle {z : ℂ} (hz : z ∈ ball 0 1) :
     ContinuousOn (fun ζ => (1 - ‖z‖ ^ 2) / ‖ζ - z‖ ^ 2) (sphere 0 1) := by
  refine continuousOn_of_forall_continuousAt ?_
  intro ζ hζ
  refine ContinuousAt.div (continuousAt_const) (by fun_prop) ?_
  intro h
  rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h
  rw [h, mem_sphere, dist_zero_right] at hζ
  rw [mem_ball, dist_zero_right, hζ] at hz
  exact (lt_self_iff_false 1).mp hz

-- #count_heartbeats in -- 2200 hb
/-- The sequence `r_n = 1 - 1 / (n + 2)` is in (0,1) and tends to `1` as `n → ∞`. -/
lemma seq_conv_to_one_in_unit_interval :
  let r : ℕ → ℝ := fun n => 1 - 1 / (n + 2)
  (∀ n, r n ∈ Ioo 0 1) ∧ Tendsto r atTop (𝓝 1) := by
  let r : ℕ → ℝ := fun n => 1 - 1 / (n + 2)
  have hr (n : ℕ) : r n ∈ Ioo 0 1 := by
    simp only [one_div, mem_Ioo, sub_pos, sub_lt_self_iff, inv_pos, r]
    have : (1 : ℝ) < (↑n + 2 : ℝ) := by linarith
    exact ⟨inv_lt_one_of_one_lt₀ this, by linarith⟩
  have hr_lim : Tendsto r atTop (𝓝 1) :=
    le_trans (tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop
      <| tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop) (by rw [sub_zero])
  exact ⟨hr, hr_lim⟩

-- #count_heartbeats in -- 800 hb
/- If r n tends to 1, then f (r n * z) tends to f z, for z in the unit disc,
when f is continuous on the closed unit disc. -/
lemma radii_tendsto_one_continuousOn_closedUnitDisc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℂ → E} {z : ℂ} {r : ℕ → ℝ}
    (hc : ContinuousOn f (closedBall 0 1)) (hr_lim : Tendsto r atTop (𝓝 1))
    (hz : z ∈ ball 0 1) : Tendsto (fun n => f (r n * z)) atTop (𝓝 (f z)) := by
    have h_seq : Tendsto (fun n => r n * z) atTop (𝓝 z) := by
      simpa using Tendsto.mul (continuous_ofReal.continuousAt.tendsto.comp hr_lim)
        (tendsto_const_nhds (x := z))
    specialize hc z (ball_subset_closedBall hz)
    have hc : ContinuousAt f z := ContinuousWithinAt.continuousAt hc (closedBall_mem_nhds_of_mem hz)
    exact (ContinuousAt.tendsto hc).comp h_seq

-- #count_heartbeats in -- 3100 hb
/- **Poisson integral formula for harmonic functions on the unit disc**:
A function `u` harmonic on the unit disc and continuous on the closed unit disc
satisfies `u(z) = (1/2π) ∫_0^{2π} (1 - |z|²) / |e^{it} - z|² u(e^{it}) dt`
for `z` in the unit disc. -/
theorem poisson_integral_formula_harmonic {u : ℂ → ℝ} {z : ℂ}
    (hu : HarmonicOnNhd u (ball 0 1)) (hc : ContinuousOn u (closedBall 0 1))
    (hz : z ∈ ball 0 1) :
    u z = (1 / (2 * π)) * ∫ t in 0..(2 * π),
      (1 - ‖z‖ ^ 2) / ‖(exp (t * I)) - z‖ ^ 2 * (u (exp (t * I))) := by
  let r : ℕ → ℝ := fun n => 1 - 1 / (n + 2)
  -- We approximate `1` by a sequence `r_n` in `(0,1)`.
  obtain ⟨hr, hr_lim⟩ := seq_conv_to_one_in_unit_interval
  have h_poisson (n : ℕ) := poisson_formula_harmonic_scaled_radius hu (hr n) hz
  have hu_lim := tendsto_integral_prod_of_continuousOn hc
                 (poisson_kernel_continousOn_circle hz) hr hr_lim
  have hu_lim : Tendsto (fun n => (u (r n * z))) atTop (𝓝 ((1 / (2 * π)) * ∫ t in 0..2 * π,
      ((1 - ‖z‖^2) / ‖(exp (t * I)) - z‖^2 * u (exp (t * I))))) := by
    simp only [r,h_poisson]
    dsimp only [smul_eq_mul] at hu_lim
    exact (Tendsto.const_mul (1 / (2 * π)) hu_lim)
  -- We conclude by uniqueness of limits and by revealing the Poisson kernel.
  rw [← tendsto_nhds_unique hu_lim (radii_tendsto_one_continuousOn_closedUnitDisc hc hr_lim hz)]

-- #count_heartbeats in -- 4200 hb
/-- **Poisson integral formula for analytic functions on the unit disc**:
A function `f : ℂ → E` analytic on the unit disc and continuous on the closed unit disc
satisfies `f(z) = (1/2π) ∫_0^{2π} (1 - |z|²) / |e^{it} - z|² f(e^{it}) dt`
for `z` in the unit disc. -/
theorem poisson_integral_formula_analytic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {z : ℂ}
    (hf : AnalyticOn ℂ f (ball 0 1)) (hc : ContinuousOn f (closedBall 0 1))
    (hz : z ∈ ball 0 1) :
    f z = (1 / (2 * π)) • ∫ t in 0..(2 * π),
      ((1 - ‖z‖ ^ 2) / ‖exp (t * I) - z‖ ^ 2) • f (exp (t * I)) := by
  let r : ℕ → ℝ := fun n => 1 - 1 / (n + 2)
  obtain ⟨hr, hr_lim⟩ := seq_conv_to_one_in_unit_interval
  -- We express `f(r_n z)` as the Poisson integral and then take the limit.
  have h_poisson (n : ℕ) := poisson_formula_analytic_scaled_radius hf (hr n) hz
  have hu_lim : Tendsto (fun n => (f (r n * z))) atTop (𝓝 ((1 / (2 * π)) • ∫ t in 0..2 * π,
      ((1 - ‖z‖ ^ 2) / ‖(exp (t * I)) - z‖ ^ 2) • f (exp (t * I)))) := by
    simp only [r,h_poisson]
    exact (Tendsto.const_smul (tendsto_integral_prod_of_continuousOn hc
            (poisson_kernel_continousOn_circle hz) hr hr_lim) (1 / (2 * π)))
  -- We conclude by uniqueness of limits and by revealing the Poisson kernel.
  rw [← tendsto_nhds_unique (hu_lim) (radii_tendsto_one_continuousOn_closedUnitDisc hc hr_lim hz)]

-- #count_heartbeats in -- 2300 hb
/-- The real part of the Herglotz–Riesz kernel is equal to the Poisson kernel. -/
theorem real_part_herglotz_kernel (x w : ℂ) (hx : ‖x‖ = 1) :
    ((x + w) / (x - w)).re = (1 - ‖w‖ ^ 2) / ‖x - w‖ ^ 2 := by
  rw [div_re, normSq_eq_norm_sq (x - w)]
  calc (x + w).re * (x - w).re / ‖x - w‖ ^ 2 + (x + w).im * (x - w).im / ‖x - w‖ ^ 2
   _ = ((x.re + w.re) * (x.re - w.re) + (x.im + w.im) * (x.im - w.im)) / ‖x - w‖ ^ 2 := by
        simp only [add_re, sub_re, add_im, sub_im, add_div]
   _ = ((x.re * x.re + x.im * x.im) - (w.re * w.re + w.im * w.im)) / ‖x - w‖ ^ 2 := by ring_nf
   _ = ((normSq x) - (normSq w)) / ‖x - w‖ ^ 2 := by simp only [normSq_apply]
   _ = (‖x‖ ^ 2 - ‖w‖ ^ 2) / ‖x - w‖ ^ 2 := by simp only [normSq_eq_norm_sq]
   _ = (1 - ‖w‖ ^ 2) / ‖x - w‖ ^ 2 := by rw [hx, one_pow 2]

-- #count_heartbeats in -- 2000 hb
/- **Poisson integral formula for harmonic functions on the unit disc**:
A function `u : ℂ → ℝ` harmonic on the unit disc and continuous on the closed unit disc
satisfies `u(z) = (1/2π) ∫_0^{2π} Re((e^{it} + z) / (e^{it} - z)) * u(e^{it}) dt`
for `z` in the unit disc. -/
theorem poisson_integral_formula_harmonic_realPart_kernel {u : ℂ → ℝ} {z : ℂ}
    (hu : HarmonicOnNhd u (ball 0 1)) (hc : ContinuousOn u (closedBall 0 1))
    (hz : z ∈ ball 0 1) :
    u z = (1 / (2 * π)) * ∫ t in 0..(2 * π),
      ((exp (t * I) + z) / (exp (t * I) - z)).re * (u (exp (t * I))) := by
  rw [poisson_integral_formula_harmonic hu hc hz]
  congr 3
  ext t
  congr 1
  exact (real_part_herglotz_kernel (exp (t * I)) z (by rw [norm_exp_ofReal_mul_I])).symm

-- #count_heartbeats in -- 2200 hb
/-- **Poisson integral formula for analytic functions on the unit disc**:
A function `f : ℂ → E` analytic on the unit disc and continuous on the closed unit disc
satisfies `f(z) = (1/2π) ∫_0^{2π} Re((e^{it} + z) / (e^{it} - z)) • f(e^{it}) dt`
for `z` in the unit disc. -/
theorem poisson_integral_formula_analytic_realPart_kernel {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {z : ℂ}
    (hf : AnalyticOn ℂ f (ball 0 1)) (hc : ContinuousOn f (closedBall 0 1))
    (hz : z ∈ ball 0 1) :
    f z = (1 / (2 * π)) • ∫ t in 0..(2 * π),
      (((exp (t * I) + z) / (exp (t * I) - z)).re) • (f (exp (t * I))) := by
  rw [poisson_integral_formula_analytic hf hc hz]
  congr 3
  ext t
  congr 1
  exact (real_part_herglotz_kernel (exp (t * I)) z (by rw [norm_exp_ofReal_mul_I])).symm
