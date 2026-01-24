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

public section

open Complex Metric Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
         {z : ℂ} {r : ℝ} {f : ℂ → E} {u : ℂ → ℝ}

#count_heartbeats in
/-- Cauchy's integral formula for analytic functions on the unit disc,
    evaluated at scaled points `r * z` with `r ∈ (0,1)`. -/
theorem cauchy_integral_formula_unitDisc
    (hf : AnalyticOn ℂ f (ball 0 1)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 1) :
    f (r * z) = (1 / (2 * π)) • ∫ t in 0..2*π,
                (exp (I * t) / (exp (I * t) - z)) • (f (r * exp (I * t))) := by
  have (x : ℂ) (hx : ‖x‖ ≤ 1) : ‖r * x‖ < 1 := by
      #count_heartbeats! in simp only [Complex.norm_mul, norm_real, norm_eq_abs, abs_of_pos hr.1]
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
               _ _ _ _ 1 0 z (fun ζ => f (r * ζ)) ∅ (by norm_num) hz hfr_cont
    simp only [div_eq_inv_mul, mul_one]
    rw [this]
    · simp only [smul_smul,inv_mul_cancel₀ two_pi_I_ne_zero]
      exact Eq.symm (MulAction.one_smul (f (↑r * z)))
    · intro x hx
      simp only [diff_empty,mem_ball,Complex.dist_eq, sub_zero] at hx
      exact hfr_diff x (LT.lt.le hx)
  have h_cauchy :
    f (r * z) =  ∮ (ζ : ℂ) in C(0, 1), (1 / (2 * π * I)) • (1 / (ζ - z)) • f (r * ζ)  := by
    rw [h_cauchy]
    exact Eq.symm (circleIntegral.integral_smul
              (1 / (2 * ↑π * I)) (fun ζ ↦ (1 / (ζ - z)) • f (↑r * ζ)) 0 1)
  have : (1 / (2 * π)) • ∫ (t : ℝ) in 0..2 * π,
      (cexp (I * ↑t) / (cexp (I * ↑t) - z)) • f (↑r * cexp (I * ↑t)) =
     ∫ (t : ℝ) in 0..2 * π, (1 / (2 * π)) •
      (cexp (I * ↑t) / (cexp (I * ↑t) - z)) • f (↑r * cexp (I * ↑t)) :=
        Eq.symm (intervalIntegral.integral_smul (1 / (2 * π)) fun t ↦
                (cexp (I * ↑t) / (cexp (I * ↑t) - z)) • f (↑r * cexp (I * ↑t)))
  rw [this,h_cauchy]
  simp only [circleIntegral]
  congr 1
  ext t
  have : f (↑r * circleMap 0 1 t) = f (↑r * cexp (I * ↑t)) := by norm_num [circleMap, mul_comm]
  rw [this]
  simp only [← smul_assoc]
  have : (deriv (circleMap 0 1) t • (1 / (2 * ↑π * I))) • (1 / (circleMap 0 1 t - z)) =
         ((1 / (2 * π)) • (cexp (I * ↑t) / (cexp (I * ↑t) - z))) := by
          norm_num [circleMap, deriv_circleMap]
          ring_nf
          simp only [I_sq]
          ring_nf
  rw [this]
