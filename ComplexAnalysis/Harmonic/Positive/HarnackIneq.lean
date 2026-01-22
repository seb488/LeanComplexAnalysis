module

public import ComplexAnalysis.PoissonIntegral
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Harnack's inequality

## Main Results

Theorem `harnack_ineq`:

A positive harmonic function `u` on the unit disc satisfies the inequalities
    `(1 - ‖z‖) / (1 + ‖z‖) * u 0 ≤ u z ∧ u z ≤ u 0 * (1 + ‖z‖) / (1 - ‖z‖)`
for all `z` in the unit disc.
-/

public section

open  Complex InnerProductSpace Metric Set

/-- Harnack's inequality for a positive harmonic functions u on the unit disc
with u(0) = 1 and assuming continuous extension to the closed unit disc.
-/
private lemma harnack_ineq_cont_normalized
    (u : ℂ → ℝ)
    (h_pos : ∀ z ∈ ball (0 : ℂ) 1, 0 < u z)
    (h_f_zero : u 0 = 1)
    (h_harmonic : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (z : ℂ) (hz : z ∈ ball 0 1) :
    (1 - ‖z‖) / (1 + ‖z‖) ≤ u z ∧ u z ≤ (1 + ‖z‖) / (1 - ‖z‖) := by
  have h_boundary : ∀ t : ℝ, 0 ≤ t → t ≤ 2 * Real.pi → u (exp (I * t)) ≥ 0 := by
    intros t ht_nonneg ht_le_two_pi
    have h_boundary : Filter.Tendsto (fun r : ℝ => u (r * exp (I * t)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (u (exp (I * t)))) := by
      have h_boundary : Filter.Tendsto (fun r : ℝ => u (r * exp (I * t)))
        (nhdsWithin 1 (Set.Iio 1)) (nhds (u (exp (I * t)))) := by
        have h_cont : ContinuousOn (fun r : ℝ => u (r * exp (I * t))) (Set.Icc 0 1) := by
          refine hc.comp ?_ ?_
          · fun_prop
          · norm_num [Set.MapsTo, norm_exp]
            exact fun x hx₁ hx₂ => abs_le.mpr ⟨by linarith, by linarith⟩
        have := h_cont 1 (by norm_num)
        simpa using this.tendsto.mono_left <| nhdsWithin_mono _ <| Set.Ioo_subset_Icc_self;
      convert h_boundary using 1;
    have h_boundary : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1), 0 < u (r * exp (I * t)) := by
      filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr using h_pos _ <| by
        simpa [abs_of_nonneg hr.1.le, norm_exp] using hr.2
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ‹_› (
      Filter.eventually_of_mem h_boundary fun x hx => le_of_lt hx)
  have h_cont_exp : Continuous fun t : ℝ => cexp (I * t) := by
    continuity
  -- Apply the Poisson integral formula to u.
  have h_poisson : u z = (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..2 * Real.pi,
    (1 - ‖z‖^2) / ‖(exp (I * t)) - z‖^2 * u (exp (I * t)) := by
    exact poisson_integral_formula h_harmonic hc z hz
  -- Using the Poisson integral formula, we can bound u(z) from below and above.
  have h_integral_bounds : (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..2 * Real.pi,
    (1 - ‖z‖^2) / (1 + ‖z‖)^2 * u (exp (I * t)) ≤ u z ∧
      u z ≤ (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..2 * Real.pi,
        (1 - ‖z‖^2) / (1 - ‖z‖)^2 * u (exp (I * t)) := by
    -- Using the bounds on the Poisson kernel, we can bound the integral.
    have h_bound_integral : ∀ t : ℝ, 0 ≤ t → t ≤ 2 * Real.pi →
        (1 - ‖z‖^2) / (1 + ‖z‖)^2 * u (exp (I * t)) ≤
      (1 - ‖z‖^2) / ‖(exp (I * t)) - z‖^2 * u (exp (I * t)) ∧
      (1 - ‖z‖^2) / ‖(exp (I * t)) - z‖^2 * u (exp (I * t)) ≤
      (1 - ‖z‖^2) / (1 - ‖z‖)^2 * u (exp (I * t)) := by
      intros t ht_nonneg ht_le_two_pi
      have h_norm_bound : ‖(exp (I * t)) - z‖^2 ≥ (1 - ‖z‖)^2 ∧
        ‖(exp (I * t)) - z‖^2 ≤ (1 + ‖z‖)^2 := by
        have h_norm_bound : ‖(exp (I * t)) - z‖ ≥ 1 - ‖z‖ ∧ ‖(exp (I * t)) - z‖ ≤ 1 + ‖z‖ := by
          exact ⟨by have := norm_sub_norm_le (exp (I * t)) z; norm_num [norm_exp] at *; linarith,
           by have := norm_sub_le (exp (I * t)) z; norm_num [norm_exp] at *; linarith⟩
        exact ⟨pow_le_pow_left₀ (sub_nonneg.2 <| le_of_lt <| by simpa using hz) h_norm_bound.1 2,
          pow_le_pow_left₀ (norm_nonneg _) h_norm_bound.2 2⟩
      constructor <;> gcongr
      any_goals nlinarith [norm_nonneg z, show ‖z‖ < 1 from by simpa using hz]
      · exact h_boundary t ht_nonneg ht_le_two_pi
      · exact h_boundary t ht_nonneg ht_le_two_pi
      · nlinarith [norm_nonneg (exp (I * t) - z)]
    rw [h_poisson]
    constructor <;> apply_rules [mul_le_mul_of_nonneg_left,
      intervalIntegral.integral_mono_on] <;> norm_num
    any_goals linarith [Real.pi_pos]
    any_goals intro t ht₁ ht₂; linarith [h_bound_integral t ht₁ ht₂]
    · apply_rules [ContinuousOn.intervalIntegrable]
      exact ContinuousOn.mul continuousOn_const <| hc.comp (Continuous.continuousOn <| by
        continuity) fun x hx => by simp [norm_exp]
    · apply_rules [ContinuousOn.intervalIntegrable]
      refine ContinuousOn.mul ?_ ?_
      · refine ContinuousOn.div continuousOn_const ?_ ?_
        · fun_prop
        · norm_num [exp_ne_zero, sub_eq_zero]
          intro t ht H; rw [← H] at hz; norm_num [norm_exp] at hz
      · exact hc.comp (Continuous.continuousOn <| by continuity) fun x hx => by simp [norm_exp]
    · apply_rules [ContinuousOn.intervalIntegrable]
      refine ContinuousOn.mul ?_ ?_
      · refine ContinuousOn.div continuousOn_const ?_ ?_
        · fun_prop;
        · norm_num [exp_ne_zero, sub_eq_zero]
          intro t ht H; rw [← H] at hz; norm_num [norm_exp] at hz
      · exact hc.comp (Continuous.continuousOn <| by continuity) fun x hx => by simp [norm_exp]
    · apply_rules [ContinuousOn.intervalIntegrable]
      refine ContinuousOn.mul continuousOn_const ?_
      exact hc.comp (Continuous.continuousOn <| by continuity) fun x hx => by simp [norm_exp]
  -- Using the fact that u(0) = 1, we can simplify the integrals.
  have h_integral_simplified : ∫ t in (0 : ℝ)..2 * Real.pi, u (exp (I * t)) = 2 * Real.pi := by
    -- Apply the Poisson integral formula at the center of the disc (= mean value property).
    have := poisson_integral_formula  h_harmonic hc (z:=0)
    norm_num at this ⊢
    nlinarith [Real.pi_pos, mul_inv_cancel₀ Real.pi_ne_zero]
  convert h_integral_bounds using 2 <;> norm_num [h_integral_simplified] <;> ring;
  · field_simp
    ring
  · grind

/--
Removing the normalization at `0` from Lemma `harnack_ineq_normalized_cont`.
-/
private lemma harnack_ineq_cont
    (u : ℂ → ℝ)
    (h_pos : ∀ z ∈ ball (0 : ℂ) 1, 0 < u z)
    (h_harmonic : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (z : ℂ) (hz : z ∈ ball 0 1) :
    (1 - ‖z‖) / (1 + ‖z‖) * u 0 ≤ u z ∧ u z ≤ u 0 * (1 + ‖z‖) / (1 - ‖z‖) := by
  -- Normalize u
  set v := fun w => u w / u 0 with hv
  -- v satisfies the conditions of `harnack_ineq_normalized`
  have hv_pos : ∀ w ∈ ball (0 : ℂ) 1, 0 < v w := by
    intro w hw
    simp [hv]
    exact div_pos (h_pos w hw) (h_pos 0 (mem_ball_self zero_lt_one))
  have hv_zero : v 0 = 1 := by
    simp [hv]
    exact div_self (ne_of_gt (h_pos 0 (mem_ball_self zero_lt_one)))
  have hv_harmonic : HarmonicOnNhd v (ball 0 1) := by
    intro w hw
    change HarmonicAt (fun z => u z / u 0) w
    have : (fun z => u z / u 0) = (1 / u 0) • u := by
      ext; simp [smul_eq_mul]; ring
    rw [this]
    apply (h_harmonic w hw).const_smul
  have hv_cont : ContinuousOn v (closedBall 0 1) := by
    apply ContinuousOn.div hc continuousOn_const
    intro w _
    exact ne_of_gt (h_pos 0 (mem_ball_self zero_lt_one))
  -- Apply `harnack_ineq_cont_normalized` to v
  have := harnack_ineq_cont_normalized v hv_pos hv_zero hv_harmonic hv_cont z hz
  -- Scale back
  simp [hv] at this
  have h0_ne : u 0 ≠ 0 := ne_of_gt (h_pos 0 (mem_ball_self zero_lt_one))
  have h0_ge : u 0 > 0 := h_pos 0 (mem_ball_self zero_lt_one)
  constructor
  · calc (1 - ‖z‖) / (1 + ‖z‖) * u 0
      _ ≤ (u z / u 0) * u 0 := by nlinarith [this.1]
      _ = u z := by field_simp
  · calc u z
      = (u z / u 0) * u 0 := by field_simp [h0_ne]
    _ ≤ ((1 + ‖z‖) / (1 - ‖z‖)) * u 0 := by nlinarith [this.2, h0_ge]
    _ = u 0 * (1 + ‖z‖) / (1 - ‖z‖) := by ring

/-- The scaled version of a harmonic function. -/
private lemma harmonic_scaling
    (u : ℂ → ℝ)
    (hu : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (r : ℝ) (hr : r ∈ Set.Ioo 0 1) :
    let v : ℂ → ℝ := fun w => u (r * w)
    HarmonicOnNhd v (ball (0 : ℂ) 1):= by
      intro v
      simp_all only [Set.mem_Ioo]
      have hfu : ∃ (f : ℂ → ℂ), AnalyticOn ℂ f (ball 0 1) ∧
        EqOn (fun (z : ℂ) => (f z).re) u (ball 0 1) := by
        obtain ⟨f,hf⟩ := @harmonic_is_realOfHolomorphic u (0 : ℂ) 1 hu
        use f
        exact ⟨hf.1.analyticOn, hf.2⟩
      obtain ⟨f, hf, hf_eq⟩ := hfu
      have hv_analytic : AnalyticOn ℂ (fun w => f (r * w)) (ball 0 1) := by
        apply_rules [DifferentiableOn.analyticOn]
        · exact DifferentiableOn.comp (hf.differentiableOn)
                  (DifferentiableOn.mul (differentiableOn_const _) differentiableOn_id)
                  fun x hx => by simpa [abs_of_pos hr.1]
                              using by nlinarith [abs_le.mp (Complex.abs_re_le_norm x),
                                                  abs_le.mp (Complex.abs_im_le_norm x),
                                                  mem_ball_zero_iff.mp hx]
        · exact isOpen_ball
      have hv_harmonic : ∀ w ∈ ball 0 1, HarmonicAt (fun w => (f (r * w)).re) w := by
        intro w hw
        have hv_analytic_at_w : AnalyticAt ℂ (fun w => f (r * w)) w := by
          apply_rules [DifferentiableOn.analyticAt, hv_analytic.differentiableOn]
          exact isOpen_ball.mem_nhds hw
        exact AnalyticAt.harmonicAt_re hv_analytic_at_w
      have hv_eq : ∀ w ∈ ball 0 1, v w = (f (r * w)).re := by
        intro w hw
        specialize hf_eq (show (r : ℂ) * w ∈ ball 0 1 from
                          by simpa [abs_of_pos hr.1]
                          using by nlinarith [norm_nonneg w,
                                              show (‖w‖ : ℝ) < 1 from by simpa using hw])
        aesop
      intro w hw;
      have hv_harmonic_at_w : ∀ᶠ w in nhds w, v w = (f (r * w)).re := by
        exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_ball hw) hv_eq
      exact (harmonicAt_congr_nhds hv_harmonic_at_w).mpr (hv_harmonic w hw)


/-- Scaled version of Harnack's inequality for a smaller radius r < 1. -/
private lemma harnack_ineq_aux
    (u : ℂ → ℝ)
    (h_pos : ∀ z ∈ ball (0 : ℂ) 1, 0 < u z)
    (h_harmonic : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (r : ℝ) (hr : r ∈ Set.Ioo 0 1)
    (z : ℂ) (hz : ‖z‖ < r) :
    (r - ‖z‖) / (r + ‖z‖) * u 0 ≤ u z ∧ u z ≤ u 0 * (r + ‖z‖) / (r - ‖z‖) := by
      -- Define the function v as v(w) = u(rw) and show that it is harmonic on the unit disk.
      set v : ℂ → ℝ := fun w => u (r * w)
      have hv_harmonic : HarmonicOnNhd v (ball (0 : ℂ) 1) := harmonic_scaling u h_harmonic r hr
      -- Apply the normalized Harnack's inequality to v at w = z/r.
      have hv_ineq : (1 - ‖z / r‖) / (1 + ‖z / r‖) * v 0 ≤ v (z / r) ∧
        v (z / r) ≤ v 0 * (1 + ‖z / r‖) / (1 - ‖z / r‖) := by
        /- Since v is harmonic on the unit disk and continuous on its closure,
        we can apply Harnack's inequality. -/
        have hv_cont : ContinuousOn v (closedBall 0 1) := by
          refine ContinuousOn.comp (t:= ball 0 1) ?_ ?_ ?_
          · intro z hz
            have := h_harmonic z hz
            exact this.1.continuousAt.continuousWithinAt
          · exact continuousOn_const.mul continuousOn_id
          · exact fun x hx =>
              by simpa [abs_of_pos hr.1] using
                by nlinarith [hr.1, hr.2, show ‖x‖ ≤ 1 from by simpa using hx.out]
        apply harnack_ineq_cont v (fun w hw => by
          apply h_pos
          simpa [abs_of_pos hr.1] using
            by nlinarith [hr.1, hr.2, norm_nonneg w, show ‖w‖ < 1 from by simpa using hw])
          hv_harmonic hv_cont (z / r) (by simp_all [div_lt_iff₀, abs_of_pos hr.1])
      simp at *;
      convert hv_ineq using 2 <;> norm_num [abs_of_pos hr.1, mul_div_cancel₀, hr.1.ne']
      · have hr_pos : 0 < r := hr.1
        field_simp [hr_pos.ne']
        ring_nf
        simp [v]
      · have : v (z / r) = u (r * (z / r)) := rfl
        simp [this] ; congr 1 ; field_simp [hr.1.ne']
      · have : v (z / r) = u (r * (z / r)) := rfl
        simp [this] ; congr 1 ; field_simp [hr.1.ne']
      · have : v 0 = u 0 := by simp [v, mul_zero]
        rw [this]
        have hr_pos : 0 < r := hr.1
        field_simp [hr_pos.ne']

/-- **Harnack's inequality for positive harmonic functions.**
A positive harmonic function on the unit disc satisfies
two-sided estimates in terms of the distance to the boundary.
-/
theorem harnack_ineq
    (u : ℂ → ℝ)
    (h_pos : ∀ z ∈ ball (0 : ℂ) 1, 0 < u z)
    (h_harmonic : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (z : ℂ) (hz : z ∈ ball 0 1) :
    (1 - ‖z‖) / (1 + ‖z‖) * u 0 ≤ u z ∧ u z ≤ u 0 * (1 + ‖z‖) / (1 - ‖z‖) := by
  refine ⟨?_, ?_⟩
  · -- For any r ∈  (‖z‖, 1), we can apply `harnack_ineq_aux` to get the inequality.
    have h_ineq : ∀ r ∈ Set.Ioo ‖z‖ 1, (r - ‖z‖) / (r + ‖z‖) * u 0 ≤ u z := by
      exact fun r hr => harnack_ineq_aux u h_pos h_harmonic r ⟨
        by linarith [hr.1, norm_nonneg z], by linarith [hr.2]⟩ z (by simpa using hr.1) |>.1
    -- Taking the limit as r → 1^-, we get:
    have h_limit : Filter.Tendsto (fun r => (r - ‖z‖) / (r + ‖z‖) * u 0) (
      nhdsWithin 1 (Set.Iio 1)) (nhds ((1 - ‖z‖) / (1 + ‖z‖) * u 0)) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.mul (
        ContinuousAt.div (continuousAt_id.sub continuousAt_const) (
          continuousAt_id.add continuousAt_const) (by linarith [norm_nonneg z]))
            continuousAt_const)
    exact le_of_tendsto h_limit (
      Filter.eventually_of_mem (Ioo_mem_nhdsLT <| show ‖z‖ < 1 from by simpa using hz) h_ineq)
  · -- For any r ∈  (‖z‖, 1), we can apply `harnack_ineq_aux` to get the inequalities:
    have h_aux : ∀ r ∈ Set.Ioo (‖z‖) 1, u z ≤ u 0 * (r + ‖z‖) / (r - ‖z‖) := by
      exact fun r hr => harnack_ineq_aux u h_pos h_harmonic r ⟨
          by linarith [hr.1, norm_nonneg z], hr.2⟩ z (by simpa using hr.1) |>.2
    -- Taking the limit as r → 1^- (or just r → 1 within the interval),
    -- we get the desired inequality.
    have h_lim : Filter.Tendsto (fun r : ℝ => u 0 * (r + ‖z‖) / (r - ‖z‖)) (
      nhdsWithin 1 (Set.Iio 1)) (nhds (u 0 * (1 + ‖z‖) / (1 - ‖z‖))) := by
      exact Filter.Tendsto.div (tendsto_const_nhds.mul (
        continuousWithinAt_id.add continuousWithinAt_const)) (
          continuousWithinAt_id.sub continuousWithinAt_const) (sub_ne_zero_of_ne <| by aesop)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_lim (
      Filter.eventually_of_mem (Ioo_mem_nhdsLT <| show ‖z‖ < 1 from by simpa using hz) h_aux)
