import ComplexAnalysis.PoissonIntegral

open  Complex InnerProductSpace Metric

/-- **Harnack's inequality for positive harmonic functions.**
A positive harmonic function on the unit disc with `u(0) = 1` satisfies
two-sided estimates in terms of the distance to the boundary.

TODO: remove the hypothesis h_f_zero : u 0 = 1
      remove the hypothesis hc : ContinuousOn u (closedBall 0 1)
-/
theorem harnack_inequality_closed_disc
    (u : ℂ → ℝ)
    (h_pos : ∀ z ∈ (ball (0 : ℂ) 1), 0 < u z)
    (h_f_zero : u 0 = 1)
    (h_harmonic : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
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

  -- Apply the Poisson integral formula.
  have h_poisson : u z = (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..2 * Real.pi,
    (1 - ‖z‖^2) / ‖(exp (I * t)) - z‖^2 * u (exp (I * t)) := by
    exact poisson_integral_formula h_harmonic hc z hz
  -- Using the Poisson integral formula, we can bound $u(z)$ from below and above.
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
