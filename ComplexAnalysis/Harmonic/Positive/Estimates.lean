module

public import ComplexAnalysis.Harmonic.Positive.HerglotzRieszUnique
public import ComplexAnalysis.Harmonic.Positive.HerglotzRieszRepresentations

open MeasureTheory Metric Set

variable {z : ℂ} {p : ℂ → ℂ}

/-- TO DO: Prove the bound on the Taylor coefficients of a holomorphic function
    with positive real part on the unit disk. -/
theorem Taylor_coef_bound
    (hp_analytic : AnalyticOn ℂ p (ball (0 : ℂ) 1))
    (h_real_pos : MapsTo p (ball (0 : ℂ) 1) {w : ℂ | 0 < w.re})
    (c : ℕ → ℂ) (hc : ∀ z : ℂ, ‖z‖ < 1 → p z = 1 + ∑' n, z ^ (n + 1) * c n) :
    ∀ n : ℕ, ‖c n‖ ≤ 2 := by
      have hp0 : p 0 = 1 := by
        specialize hc 0 (by simp)
        aesop
      obtain ⟨μ, hμ, _⟩ := HerglotzRiesz_representation_analytic p hp_analytic hp0 h_real_pos
      sorry

/-- TO D0: Prove the growth estimates for holomorphic functions
   with positive real part on the unit disk. -/
theorem growth_estimates
  (hp_analytic : AnalyticOn ℂ p (ball (0 : ℂ) 1)) (hp0 : p 0 = 1)
  (h_real_pos : MapsTo p (ball (0 : ℂ) 1) {w : ℂ | 0 < w.re}) :
  (1-‖z‖) / (1+‖z‖) ≤ ‖p z‖ ∧ ‖p z‖ ≤ (1+‖z‖) / (1-‖z‖) := by
     sorry
