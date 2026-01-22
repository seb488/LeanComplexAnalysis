/-
Provided we know Grönwall's area theorem, we prove that:

* If f is in S, f(z) = z + a₂ * z^2 + a₃ * z^2, ..., then |a₂^2 - a₃| ≤ 1; `coeff_bound_of_S_two_three`.

* Bieberbach's theorem: If f is in S, f(z) = z + a₂ * z^2 + ..., then |a₂| ≤ 2; `bieberbach_second_coeff`.
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Tactic.LinearCombination'
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import ComplexAnalysis.UnivalentFunctions.ClassS

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

open Metric


noncomputable section

/- # Assumption -/

/-
The property that for any function g in class Σ with expansion g(z) = z + h(1/z)
we have |h'(0)| <= 1 is treated as an axiom. (A consequence of Grönwall's area theorem.)
-/
axiom SigmaCoeffBound :
  ∀ (g : ℂ → ℂ), g ∈ classSigma →
  ∀ (h : ℂ → ℂ), AnalyticOn ℂ h (ball 0 1) →
  (∀ z, 1 < ‖z‖ → g z = z + h (1 / z)) → ‖deriv h 0‖ ≤ 1


/- # Theorems -/

/- Using the Taylor expansion of $f(z)$, we can write $f(z) = z + \frac{f''(0)}{2} z^2 +
\frac{f'''(0)}{6} z^3 + o(z^3)$. -/
theorem taylor_classS (f : ℂ → ℂ) (hf : f ∈ classS) :
    Filter.Tendsto (fun z => (f z - z - (deriv^[2] f 0 / 2) * z^2 -
    (deriv^[3] f 0 / 6) * z^3) / z^3) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  -- Since $f$ is analytic on the unit disk, we can apply the Taylor series expansion.
  have h_taylor : ∀ z ∈ ball 0 1, f z = z + (deriv^[2] f 0 / 2) * z^2 +
    (deriv^[3] f 0 / 6) * z^3 + ∑' n : ℕ, (deriv^[n + 4] f 0 / (n + 4)!) * z^(n + 4) := by
    have h_taylor : ∀ z ∈ ball 0 1, f z = ∑' n : ℕ, (deriv^[n] f 0 / (n ! : ℂ)) * z^n := by
      intro z hz
      have h_analytic : AnalyticOn ℂ f (ball 0 1) := by
        exact hf.1
      have := @Complex.taylorSeries_eq_on_ball
      simpa [div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm, iteratedDeriv_eq_iterate]
        using Eq.symm (this (
          show DifferentiableOn ℂ f (ball 0 1) from h_analytic.differentiableOn) hz)
    intro z hz; rw [h_taylor z hz] ; rw [← Summable.sum_add_tsum_nat_add 4]
    focus norm_num [Finset.sum_range_succ]
    · have := hf.2.2; aesop
    · contrapose! h_taylor
      use z; simp_all  [tsum_eq_zero_of_not_summable]
      have := hf.2.1
      intro H; have := @this z (by simpa using hz) 0 (by simp) ; simp_all  [hf.2.2]
      exact h_taylor ⟨_, hasSum_single 0 fun n hn => by aesop⟩
  -- Substitute the Taylor series expansion into the expression.
  suffices h_subst : Filter.Tendsto (fun z => (∑' n : ℕ, (deriv^[n + 4] f 0 / (n + 4)!) *
    z^(n + 1)) / 1) (nhdsWithin 0 {0}ᶜ) (nhds 0) by
    refine Filter.Tendsto.congr' ?_ h_subst
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [ball_mem_nhds _ zero_lt_one] with z hz hz' ; rw [h_taylor z hz]
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_succ, tsum_mul_left]
    grind
  /- The series $\sum_{n=0}^{\infty} \frac{f^{(n+4)}(0)}{(n+4)!} z^{n+1}$ converges uniformly
  to an analytic function on the unit disk. -/
  have h_uniform : ContinuousOn (fun z => ∑' n : ℕ, (
    deriv^[n + 4] f 0 / (n + 4)!) * z^(n + 1)) (closedBall 0 (1 / 2)) := by
    refine continuousOn_tsum (u := fun n => ‖deriv^[n + 4] f 0 / (n + 4)!‖ *
      (1 / 2) ^ (n + 1)) ?_ ?_ ?_
    · exact fun n => Continuous.continuousOn (by continuity)
    · have h_uniform : Summable (fun n : ℕ => ‖deriv^[n + 4] f 0 / (n + 4)!‖ *
        (1 / 2) ^ n) := by
        have h_uniform : Summable (fun n : ℕ => ‖deriv^[n + 4] f 0 / (n + 4)!‖ *
          (1 / 2) ^ (n + 4)) := by
          have h_analytic : AnalyticOn ℂ f (ball 0 1) := by
            exact hf.1
          have := @Complex.taylorSeries_eq_on_ball
          specialize this (
            show DifferentiableOn ℂ f (ball 0 1) from h_analytic.differentiableOn) (
              show (1 / 2 : ℂ) ∈ ball 0 1 from by norm_num [Complex.dist_eq])
          norm_num [div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm,
            iteratedDeriv_eq_iterate] at this ⊢
          contrapose! this
          rw [tsum_eq_zero_of_not_summable]
          · have := hf.2.1 (show (1 / 2 : ℂ) ∈ ball 0 1 from by norm_num [Complex.dist_eq]) (
              show (0 : ℂ) ∈ ball 0 1 from by norm_num [Complex.dist_eq])
            norm_num at this ; aesop
          · exact fun h => this <| by simpa using summable_nat_add_iff 4 |>.2 h.norm
        convert h_uniform.mul_left 16 using 2 ; ring
      convert h_uniform.mul_left (1 / 2) using 2 ; ring
    · norm_num
      exact fun n x hx => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (
        norm_nonneg x) hx _) (by positivity)
  have := h_uniform.continuousAt (closedBall_mem_nhds _ <| by norm_num)
  simpa using this.tendsto.mono_left inf_le_left


/-
If f is in class S and h is analytic on the unit ball such that h(z) = 1/f(z) - 1/z
 for non-zero z, then h'(0) = (f''(0)/2)^2 - f'''(0)/6.
-/
lemma deriv_h_eq (f : ℂ → ℂ) (hf : f ∈ classS) (h : ℂ → ℂ) (hh : AnalyticOn ℂ h (ball 0 1))
    (heq : ∀ z ∈ ball 0 1, z ≠ 0 → h z = 1 / f z - 1 / z) :
    deriv h 0 = (deriv^[2] f 0 / 2) ^ 2 - (deriv^[3] f 0 / 6) := by
  /- Using the fact that $f(z) = z + \frac{f''(0)}{2} z^2 + \frac{f'''(0)}{6} z^3 + o(z^3)$,
  we can write $h(z)$ as $-\frac{f''(0)}{2} + \left(\frac{f''(0)^2}{4} -
  \frac{f'''(0)}{6}\right) z + o(z)$. -/
  have h_h_expansion : Filter.Tendsto (fun z => (h z - h 0) / z) (nhdsWithin 0 {0}ᶜ) (
    nhds ((deriv^[2] f 0 / 2) ^ 2 - deriv^[3] f 0 / 6)) := by
    have h_approx : Filter.Tendsto (fun z => (1 / (f z) - 1 / z + deriv^[2] f 0 / 2) / z) (
      nhdsWithin 0 {0}ᶜ) (nhds ((deriv^[2] f 0 / 2) ^ 2 - deriv^[3] f 0 / 6)) := by
      /- Using the fact that $f(z) = z + \frac{f''(0)}{2} z^2 + \frac{f'''(0)}{6} z^3 + o(z^3)$,
      we can write $1/f(z) - 1/z$ as $-\frac{f''(0)}{2} + (\frac{f''(0)^2}{4} -
      \frac{f'''(0)}{6}) z + o(z)$ and simplify the expression. -/
      have h_simplify : Filter.Tendsto (fun z => ((z - f z) / (z * f z) + deriv^[2] f 0 / 2) / z) (
        nhdsWithin 0 {0}ᶜ) (nhds ((deriv^[2] f 0 / 2) ^ 2 - deriv^[3] f 0 / 6)) := by
        have h_simplify2 : Filter.Tendsto (fun z => ((z - f z) + (deriv^[2] f 0 / 2) * z * f z) /
          (z^2 * f z)) (nhdsWithin 0 {0}ᶜ) (nhds ((deriv^[2] f 0 / 2) ^ 2 -
            deriv^[3] f 0 / 6)) := by
          have h_simplify3 : Filter.Tendsto (fun z =>
            ((z - f z) + (deriv^[2] f 0 / 2) * z * f z) / z^3) (
              nhdsWithin 0 {0}ᶜ) (nhds ((deriv^[2] f 0 / 2) ^ 2 - deriv^[3] f 0 / 6)) := by
            have h_simplify4 : Filter.Tendsto (fun z =>
              ((z - f z) + (deriv^[2] f 0 / 2) * z * (z + (deriv^[2] f 0 / 2) * z^2)) / z^3) (
                nhdsWithin 0 {0}ᶜ) (nhds ((deriv^[2] f 0 / 2) ^ 2 - deriv^[3] f 0 / 6)) := by
              have := (taylor_classS f hf).const_mul (-1)
              convert this.add (show Filter.Tendsto (fun z : ℂ =>
                (deriv^[2] f 0 / 2) ^ 2 * z ^ 3 / z ^ 3) (nhdsWithin 0 {0} ᶜ) (
                  nhds ((deriv^[2] f 0 / 2) ^ 2)) from tendsto_const_nhds.congr' (
                    by filter_upwards [self_mem_nhdsWithin] with x hx using by rw [
                      mul_div_cancel_right₀ _ (pow_ne_zero _ hx)])) |>
                    Filter.Tendsto.sub <| show Filter.Tendsto (fun z : ℂ =>
                    deriv^[3] f 0 / 6 * z ^ 3 / z ^ 3) (
                    nhdsWithin 0 {0} ᶜ) (nhds (deriv^[3] f 0 / 6)) from tendsto_const_nhds.congr' (
                            by filter_upwards [self_mem_nhdsWithin] with x hx using
                              by rw [mul_div_cancel_right₀ _ (pow_ne_zero _ hx)]) using 2 <;> ring
            have h_simplify5 : Filter.Tendsto (fun z => ((deriv^[2] f 0 / 2) * z *
              (f z - (z + (deriv^[2] f 0 / 2) * z^2))) / z^3) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
              have h_simplify6 : Filter.Tendsto (fun z =>
                (f z - (z + (deriv^[2] f 0 / 2) * z^2)) / z^2) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
                have := (taylor_classS f hf).mul (Filter.tendsto_id.mono_left inf_le_left)
                simp_all  [div_mul, pow_succ, mul_assoc]
                convert this.add (show Filter.Tendsto (fun z : ℂ =>
                  deriv (deriv (deriv f)) 0 / (6 / (z * (z * z))) / (z * z)) (
                    nhdsWithin 0 {0} ᶜ) (nhds 0) from ?_) using 2 <;> ring_nf
                · by_cases h : ‹ℂ› = 0 <;> simp  [h, pow_three, sq, mul_assoc] ; ring_nf
                  grind
                · field_simp
                  exact tendsto_nhdsWithin_of_tendsto_nhds (
                    Continuous.tendsto' (by continuity) _ _ <| by norm_num)
              field_simp
              convert h_simplify6.const_mul (deriv^[2] f 0 / 2) using 2 <;> ring
            convert ‹Filter.Tendsto (fun z => (z - f z + deriv^[2] f 0 / 2 * z *
              (z + deriv^[2] f 0 / 2 * z ^ 2)) / z ^ 3) (
              nhdsWithin 0 {0} ᶜ) (nhds (
                (deriv^[2] f 0 / 2) ^ 2 - deriv^[3] f 0 / 6)) ›.add h_simplify5 using 2 <;> ring
          have h_simplify7 : Filter.Tendsto (fun z => f z / z) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
            have h_simplify8 : HasDerivAt f 1 0 := by
              have := hf.2.2.2
              exact this ▸ hasDerivAt_deriv_iff.mpr (
                show DifferentiableAt ℂ f 0 from differentiableAt_of_deriv_ne_zero (by aesop))
            simpa [div_eq_inv_mul, hf.2.2.1] using h_simplify8.tendsto_slope_zero
          convert ‹Filter.Tendsto (fun z =>
            (z - f z + deriv^[2] f 0 / 2 * z * f z) / z ^ 3) (nhdsWithin 0 {0} ᶜ) (
            nhds ((deriv^[2] f 0 / 2) ^ 2 - deriv^[3] f 0 / 6)) ›.mul (
              h_simplify7.inv₀ one_ne_zero) using 2 <;> norm_num ; ring_nf
          by_cases h : ‹ℂ› = 0
          focus simp [h, pow_three, sq, mul_comm]
          grind
        refine h_simplify2.congr' ?_
        rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
        rw [Metric.eventually_nhds_iff]
        refine ⟨1, by norm_num, fun z hz hz' => ?_⟩
        rw [div_add', div_div] ; focus ring
        simp_all [classS]
        exact fun h => hz' <| hf.2.1 (by aesop) (by aesop) <| by aesop
      refine h_simplify.congr' ?_
      rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
      rw [Metric.eventually_nhds_iff]
      refine ⟨1, by norm_num, fun z hz hz' => ?_⟩ ; rw [div_sub_div] <;> ring_nf <;> simp
      · have := hf.2.1
        exact fun h => hz' <|
          this (show z ∈ ball 0 1 from by simpa using hz) (show 0 ∈ ball 0 1 from by norm_num) <|
          by simpa [hf.2.2.1] using h
      · exact hz'
    have h_h0 : h 0 = -deriv^[2] f 0 / 2 := by
      have h_lim : Filter.Tendsto (fun z => 1 / f z - 1 / z) (
        nhdsWithin 0 {0}ᶜ) (nhds (-deriv^[2] f 0 / 2)) := by
          have := h_approx.mul (Filter.tendsto_id.mono_left inf_le_left)
          field_simp
          simpa using this.sub_const (deriv^[2] f 0 / 2) |> Filter.Tendsto.congr' (
            by filter_upwards [self_mem_nhdsWithin] with x hx using by aesop)
      have h_h0 : Filter.Tendsto (fun z => h z) (nhdsWithin 0 {0}ᶜ)
        (nhds (-deriv^[2] f 0 / 2)) := by
        exact h_lim.congr' (by filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (
          ball_mem_nhds _ zero_lt_one)] with z hz hz'; aesop)
      convert tendsto_nhds_unique (hh.continuousOn.continuousAt (
        ball_mem_nhds _ zero_lt_one) |> fun h => h.mono_left inf_le_left) h_h0 using 1
    refine Filter.Tendsto.congr' ?_ h_approx
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (
      ball_mem_nhds _ zero_lt_one)] with z hz hz' using by rw [heq z hz' hz, h_h0] ; ring
  refine HasDerivAt.deriv (hasDerivAt_iff_tendsto_slope_zero.mpr ?_)
  simpa [div_eq_inv_mul] using h_h_expansion

/-
If the coefficient bound holds for class Sigma, then for any f in class S, |a_2^2 - a_3| <= 1.
-/
theorem coeff_bound_of_S_two_three (f : ℂ → ℂ) (hf : f ∈ classS) :
    ‖(deriv^[2] f 0 / 2) ^ 2 - (deriv^[3] f 0 / 6)‖ ≤ 1 := by
  /- By `inv_f_sub_inv_id_analytic`, there exists $h$ analytic on the ball
  such that $h(z) = 1/f(z) - 1/z$ for $z \ne 0$. -/
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ, AnalyticOn ℂ h (ball 0 1) ∧
    ∀ z ∈ ball 0 1, z ≠ 0 → h z = 1 / f z - 1 / z := by
    exact inv_f_sub_inv_id_analytic f hf
  -- By `inv_f_sub_inv_id_analytic`, there exists $g$ in class Sigma such that $g(z) = 1/f(1/z)$.
  obtain ⟨g, hg⟩ : ∃ g ∈ classSigma, ∀ z, 1 < ‖z‖ → g z = z + h (1 / z) := by
    use fun z => 1 / f (1 / z)
    refine ⟨?_, ?_⟩
    · exact inv_f_inv_in_Sigma f hf
    · intro z hz; rw [hh.2 _ _ _] <;> norm_num [show z ≠ 0 by rintro rfl; norm_num at hz]
      exact inv_lt_one_of_one_lt₀ hz
  have := SigmaCoeffBound g hg.1 h hh.1 hg.2
  have := deriv_h_eq f hf h hh.1 hh.2; aesop

/-
If g is the square root transform of f, then g''(0) = 0.
-/
lemma square_root_transform_deriv2 (f : ℂ → ℂ) (hf : f ∈ classS) (g : ℂ → ℂ) (hg : g ∈ classS)
    (h_eq : ∀ z ∈ ball 0 1, g z ^ 2 = f (z ^ 2)) :
    deriv^[2] g 0 = 0 := by
  have h_diff_three_times : deriv (fun z => deriv (fun z =>
    deriv (fun z => g z ^ 2) z) z) 0 = deriv (
    fun z => deriv (fun z => deriv (fun z => f (z ^ 2)) z) z) 0 := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [ball_mem_nhds 0 zero_lt_one] with z hz
    exact Filter.EventuallyEq.deriv_eq (
      by filter_upwards [IsOpen.mem_nhds (
        isOpen_ball) hz] with x hx using Filter.EventuallyEq.deriv_eq (
          by filter_upwards [IsOpen.mem_nhds (isOpen_ball) hx] with y hy using by aesop))
  have h_g''_zero : deriv (fun z => deriv (fun z => deriv (fun z => g z ^ 2) z) z) 0 =
    6 * deriv^[2] g 0 := by
    have h_g''_zero : deriv (fun z => deriv (fun z => deriv (fun z => g z ^ 2) z) z) 0 =
      deriv (fun z => 2 * (deriv g z ^ 2 + g z * deriv^[2] g z)) 0 := by
      have h_g''_zero : ∀ z ∈ ball 0 1, deriv (fun z =>
        deriv (fun z => g z ^ 2) z) z = 2 * (deriv g z ^ 2 + g z * deriv^[2] g z) := by
        have h_diff : ∀ z ∈ ball 0 1, deriv (fun z => g z ^ 2) z = 2 * g z * deriv g z := by
          intro z hz; norm_num [hg.1.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz)]
        intro z hz; rw [Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (
          IsOpen.mem_nhds isOpen_ball hz) fun x hx => h_diff x hx)]
        norm_num [mul_assoc, mul_comm, mul_left_comm, hg.1.differentiableOn.differentiableAt (
          isOpen_ball.mem_nhds hz)] ; ring_nf
        convert HasDerivAt.deriv (HasDerivAt.mul (
          HasDerivAt.mul (hg.1.differentiableOn.differentiableAt (
            isOpen_ball.mem_nhds hz) |> DifferentiableAt.hasDerivAt) (show HasDerivAt (deriv g) (
              deriv (deriv g) z) z from ?_)) (hasDerivAt_const _ _)) using 1 ; focus ring!
        have h_diff : AnalyticOn ℂ (deriv g) (ball 0 1) := by
          apply_rules [DifferentiableOn.analyticOn, hg.1.differentiableOn]
          · apply_rules [DifferentiableOn.deriv, hg.1.differentiableOn]
            exact isOpen_ball
          · exact isOpen_ball
        exact h_diff.differentiableOn.differentiableAt (
           isOpen_ball.mem_nhds hz) |> DifferentiableAt.hasDerivAt
      exact Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (
        ball_mem_nhds _ zero_lt_one) h_g''_zero)
    rw [h_g''_zero] ; norm_num [hg.2.2.1, hg.2.2.2] ; ring_nf
    have h_g''_zero : DifferentiableAt ℂ (deriv g) 0 ∧ DifferentiableAt ℂ (deriv (deriv g)) 0 := by
      have h_g''_zero : AnalyticOn ℂ (deriv g) (ball 0 1) := by
        apply_rules [DifferentiableOn.analyticOn, hg.1.differentiableOn]
        · have h_g''_zero : AnalyticOn ℂ g (ball 0 1) := by
            exact hg.1
          apply_rules [DifferentiableOn.deriv, h_g''_zero.differentiableOn]
          exact isOpen_ball
        · exact isOpen_ball
      have h_g''_zero : AnalyticOn ℂ (deriv (deriv g)) (ball 0 1) := by
        apply_rules [DifferentiableOn.analyticOn, h_g''_zero.differentiableOn]
        · apply_rules [DifferentiableOn.deriv, h_g''_zero.differentiableOn]
          · exact hg.1.differentiableOn
          · exact isOpen_ball
          · exact isOpen_ball
        · exact isOpen_ball
      exact ⟨‹AnalyticOn ℂ (deriv g) (ball 0 1) ›.differentiableOn.differentiableAt (
        ball_mem_nhds _ zero_lt_one),
          ‹AnalyticOn ℂ (deriv (deriv g)) (ball 0 1) ›.differentiableOn.differentiableAt (
            ball_mem_nhds _ zero_lt_one)⟩
    convert congr_arg (· * 2) (HasDerivAt.deriv (HasDerivAt.add (h_g''_zero.1.hasDerivAt.pow 2) (
      HasDerivAt.mul (hg.1.differentiableOn.differentiableAt (ball_mem_nhds _ zero_lt_one) |>
        DifferentiableAt.hasDerivAt) h_g''_zero.2.hasDerivAt))) using 1 ; norm_num [hg.2.2] ; ring
  have h_f'''_zero : deriv (fun z => deriv (fun z => deriv (fun z => f (z ^ 2)) z) z) 0 = 0 := by
    have h_f'_def : ∀ z ∈ ball 0 1, deriv (fun z => f (z ^ 2)) z = 2 * z * deriv f (z ^ 2) := by
      intro z hz; erw [deriv_comp] <;> norm_num ; focus ring
      exact hf.1.differentiableOn.differentiableAt (
        IsOpen.mem_nhds isOpen_ball <| by simpa using hz)
    have h_f''_def : ∀ z ∈ ball 0 1, deriv (fun z => deriv (fun z => f (z ^ 2)) z) z =
      2 * deriv f (z ^ 2) + 4 * z ^ 2 * deriv (deriv f) (z ^ 2) := by
      intro z hz; rw [Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (
        IsOpen.mem_nhds (isOpen_ball) hz) fun x hx => h_f'_def x hx)] ; ring_nf
      convert HasDerivAt.deriv (HasDerivAt.mul (HasDerivAt.mul (hasDerivAt_id z) (
        HasDerivAt.comp z (show HasDerivAt (deriv f) _ _ from hasDerivAt_deriv_iff.mpr ?_) (
          hasDerivAt_pow 2 z))) (hasDerivAt_const _ _)) using 1 <;> norm_num ; focus ring
      have h_diff_deriv : AnalyticOn ℂ (deriv f) (ball 0 1) := by
        apply_rules [DifferentiableOn.analyticOn, hf.1.differentiableOn]
        · have h_diff_deriv : AnalyticOn ℂ f (ball 0 1) := by
            exact hf.1
          apply_rules [DifferentiableOn.deriv, h_diff_deriv.differentiableOn]
          exact isOpen_ball
        · exact isOpen_ball
      have : ‖z ^ 2‖ < 1 := by
        simpa using pow_lt_one₀ (norm_nonneg z) (by simpa using hz) two_ne_zero
      exact h_diff_deriv.differentiableOn.differentiableAt (IsOpen.mem_nhds isOpen_ball <|
        by simpa using this)
    refine HasDerivAt.deriv ?_
    convert HasDerivAt.congr_of_eventuallyEq (HasDerivAt.add (HasDerivAt.const_mul (2 : ℂ) <|
      HasDerivAt.comp _ (show HasDerivAt (deriv f) _ _ from hasDerivAt_deriv_iff.mpr ?_) <|
        hasDerivAt_pow 2 _) <| HasDerivAt.mul (
          HasDerivAt.const_mul (4 : ℂ) <| hasDerivAt_pow 2 _) <|
            HasDerivAt.comp _ (show HasDerivAt (
              deriv (deriv f)) _ _ from hasDerivAt_deriv_iff.mpr ?_) <|
              hasDerivAt_pow 2 _) <| Filter.eventuallyEq_of_mem (
                ball_mem_nhds _ zero_lt_one) fun x hx =>
                  h_f''_def x hx using 1 <;> norm_num
    · have h_diff_deriv : AnalyticOn ℂ (deriv f) (ball 0 1) := by
        apply_rules [DifferentiableOn.analyticOn, hf.1.differentiableOn]
        · have h_diff_deriv : AnalyticOn ℂ f (ball 0 1) := by
            exact hf.1
          apply_rules [DifferentiableOn.deriv, h_diff_deriv.differentiableOn]
          exact isOpen_ball
        · exact isOpen_ball
      exact h_diff_deriv.differentiableOn.differentiableAt (ball_mem_nhds _ zero_lt_one)
    · have h_f'''_zero : AnalyticOn ℂ (deriv (deriv f)) (ball 0 1) := by
        apply_rules [DifferentiableOn.analyticOn, hf.1.differentiableOn]
        · have h_f'''_zero : AnalyticOn ℂ (deriv f) (ball 0 1) := by
            apply_rules [DifferentiableOn.analyticOn, hf.1.differentiableOn]
            · have h_diff_deriv : AnalyticOn ℂ f (ball 0 1) := by
                exact hf.1
              apply_rules [DifferentiableOn.deriv, h_diff_deriv.differentiableOn]
              exact isOpen_ball
            · exact isOpen_ball
          apply_rules [DifferentiableOn.deriv, h_f'''_zero.differentiableOn]
          · exact hf.1.differentiableOn
          · exact isOpen_ball
          · exact isOpen_ball
        · exact isOpen_ball
      exact h_f'''_zero.differentiableOn.differentiableAt (ball_mem_nhds _ zero_lt_one)
  grind +ring

/-
If g is the square root transform of f, then g'''(0) = (3/2) f''(0).
-/
lemma square_root_transform_deriv3 (f : ℂ → ℂ) (hf : f ∈ classS) (g : ℂ → ℂ) (hg : g ∈ classS)
    (h_eq : ∀ z ∈ ball 0 1, g z ^ 2 = f (z ^ 2)) :
    deriv^[3] g 0 = 3 / 2 * deriv^[2] f 0 := by
  -- Let $L(z) = g(z)^2$ and $R(z) = f(z^2)$.
  set L : ℂ → ℂ := fun z => g z ^ 2
  set R : ℂ → ℂ := fun z => f (z ^ 2)

  have h_f_deriv_diff : AnalyticOn ℂ (deriv f) (ball 0 1) := by
          apply_rules [DifferentiableOn.analyticOn, hf.1.differentiableOn]
          · apply_rules [DifferentiableOn.deriv, hf.1.differentiableOn]
            exact isOpen_ball
          · exact isOpen_ball
  have h_g_deriv_diff : AnalyticOn ℂ (deriv g) (ball 0 1) := by
          apply_rules [DifferentiableOn.analyticOn, hg.1]
          · have h_diff : AnalyticOn ℂ g (ball 0 1) := by
              exact hg.1
            apply_rules [DifferentiableOn.deriv, h_diff.differentiableOn]
            exact isOpen_ball
          · exact isOpen_ball
  have h_g_deriv2_diff : AnalyticOn ℂ (deriv (deriv g)) (ball 0 1) := by
          apply_rules [DifferentiableOn.analyticOn, h_g_deriv_diff.differentiableOn]
          · apply_rules [DifferentiableOn.deriv, h_g_deriv_diff.differentiableOn]
            · exact hg.1.differentiableOn
            · exact isOpen_ball
            · exact isOpen_ball
          · exact isOpen_ball

  /- By definition of $L$ and $R$, we know that $L^{(4)}(0) = 8 g'''(0)$ and
  $R^{(4)}(0) = 12 f''(0)$. -/
  have hL : deriv^[4] L 0 = 8 * deriv^[3] g 0 := by
    -- We know $g(0)=0, g'(0)=1, g''(0)=0$.
    have hg0 : g 0 = 0 := by
      exact hg.2.2.1
    have hg1 : deriv g 0 = 1 := by
      exact hg.2.2.2
    have hg2 : deriv^[2] g 0 = 0 := by
      exact square_root_transform_deriv2 f hf g hg h_eq
    /- We'll use the fact that $g$ is analytic on the unit disk to compute
    the derivatives of $L$. -/
    have hL_deriv1 : ∀ z ∈ ball 0 1, deriv L z = 2 * g z * deriv g z := by
      intro z hz; rw [show L = fun z => g z ^ 2 from rfl]
      norm_num [pow_two, hg.1.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz)]
      ring
    have hL_deriv2 : ∀ z ∈ ball 0 1, deriv^[2] L z = 2 * (deriv g z)^2 + 2 * g z *
      deriv^[2] g z := by
      intro z hz
      convert HasDerivAt.deriv (HasDerivAt.congr_of_eventuallyEq (HasDerivAt.mul (
        HasDerivAt.mul (hasDerivAt_const _ _) (hasDerivAt_deriv_iff.mpr _)) (
          hasDerivAt_deriv_iff.mpr _)) (Filter.eventuallyEq_of_mem (
            IsOpen.mem_nhds (isOpen_ball) hz) fun x hx => hL_deriv1 x hx)) using 1
      · norm_num ; ring
      · exact hg.1.differentiableOn.differentiableAt (IsOpen.mem_nhds isOpen_ball hz)
      · exact h_g_deriv_diff.differentiableOn.differentiableAt (
         IsOpen.mem_nhds isOpen_ball hz)
    have hL_deriv3 : ∀ z ∈ ball 0 1, deriv^[3] L z = 6 * deriv g z * deriv^[2] g z +
      2 * g z * deriv^[3] g z := by
      -- Apply the product rule to each term in the second derivative.
      have hL_deriv3 : ∀ z ∈ ball 0 1, deriv (fun z => 2 * (deriv g z)^2 +
        2 * g z * deriv^[2] g z) z = 6 * deriv g z * deriv^[2] g z + 2 * g z * deriv^[3] g z := by
        intro z hz
        apply_rules [HasDerivAt.deriv]
        have h_deriv2 : HasDerivAt (deriv g) (deriv^[2] g z) z := by
          have h_deriv2 : AnalyticOn ℂ (deriv g) (ball 0 1) := by
            apply_rules [DifferentiableOn.analyticOn, hg.1.differentiableOn]
          exact h_deriv2.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz) |>
            DifferentiableAt.hasDerivAt
        convert HasDerivAt.add (HasDerivAt.const_mul 2 (h_deriv2.pow 2)) (
          HasDerivAt.mul (HasDerivAt.const_mul 2 (
            hasDerivAt_deriv_iff.mpr _)) (hasDerivAt_deriv_iff.mpr _)) using 1 <;>
        norm_num [hg.1.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz)] ; focus ring!
        have h_diff : AnalyticAt ℂ (deriv g) z := by
          have h_diff : AnalyticOn ℂ g (ball 0 1) := by
            exact hg.1
          apply_rules [DifferentiableOn.analyticAt, h_diff.differentiableOn]
          focus apply_rules [DifferentiableOn.deriv, h_diff.differentiableOn]
          · exact isOpen_ball
          · exact isOpen_ball.mem_nhds hz
        exact h_diff.deriv.differentiableAt
      intro z hz; rw [← hL_deriv3 z hz] ; exact Filter.EventuallyEq.deriv_eq (
        Filter.eventuallyEq_of_mem (IsOpen.mem_nhds (isOpen_ball) hz) fun x hx =>
          hL_deriv2 x hx ▸ rfl)
    have hL_deriv4 : ∀ z ∈ ball 0 1, deriv^[4] L z = 6 * (deriv^[2] g z)^2 +
      8 * deriv g z * deriv^[3] g z + 2 * g z * deriv^[4] g z := by
      intro z hz
      convert HasDerivAt.deriv (HasDerivAt.congr_of_eventuallyEq _ (
        Filter.eventuallyEq_of_mem (IsOpen.mem_nhds (isOpen_ball) hz) fun x hx =>
          hL_deriv3 x hx)) using 1
      convert HasDerivAt.add (HasDerivAt.mul (HasDerivAt.mul (hasDerivAt_const _ _) (
        hasDerivAt_deriv_iff.mpr _)) (hasDerivAt_deriv_iff.mpr _)) (
          HasDerivAt.mul (HasDerivAt.mul (hasDerivAt_const _ _) (hasDerivAt_deriv_iff.mpr _)) (
            hasDerivAt_deriv_iff.mpr _)) using 1 <;> norm_num
      · ring
      · exact h_g_deriv_diff.differentiableOn.differentiableAt (IsOpen.mem_nhds isOpen_ball hz)
      · exact h_g_deriv2_diff.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz)
      · exact hg.1.differentiableOn.differentiableAt (IsOpen.mem_nhds isOpen_ball hz)
      · have h_diff : AnalyticOn ℂ (deriv (deriv (deriv g))) (ball 0 1) := by
          apply_rules [DifferentiableOn.analyticOn, hg.1]
          · apply_rules [DifferentiableOn.deriv, hg.1.differentiableOn]
            · exact isOpen_ball
            · exact isOpen_ball
            · exact isOpen_ball
          · exact isOpen_ball
        exact h_diff.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz)
    aesop
  have hR : deriv^[4] R 0 = 12 * deriv^[2] f 0 := by
    -- By definition of $R$, we know that $R'(z) = 2z f'(z^2)$.
    have hR' : ∀ z ∈ ball 0 1, deriv R z = 2 * z * deriv f (z ^ 2) := by
      intro z hz
      convert HasDerivAt.deriv (HasDerivAt.comp z (hf.1.differentiableOn.differentiableAt (
        isOpen_ball.mem_nhds <| by aesop) |>
          DifferentiableAt.hasDerivAt) (hasDerivAt_pow 2 z)) using 1 ; ring
    -- By definition of $R$, we know that $R''(z) = 2 f'(z^2) + 4z^2 f''(z^2)$.
    have hR'' : ∀ z ∈ ball 0 1, deriv^[2] R z = 2 * deriv f (z ^ 2) +
      4 * z ^ 2 * deriv^[2] f (z ^ 2) := by
      intro z hz
      convert HasDerivAt.deriv (HasDerivAt.congr_of_eventuallyEq (
        HasDerivAt.mul (HasDerivAt.const_mul 2 (hasDerivAt_id z)) (HasDerivAt.comp z (
          show HasDerivAt (deriv f) _ _ from hasDerivAt_deriv_iff.mpr ?_) (hasDerivAt_pow 2 z))) (
            Filter.eventuallyEq_of_mem (IsOpen.mem_nhds (isOpen_ball) hz) fun x hx =>
              hR' x hx)) using 1 <;> norm_num ; focus ring
      have : ‖z ^ 2‖ < 1 := by
        simpa using pow_lt_one₀ (norm_nonneg z) (by simpa using hz) two_ne_zero
      exact h_f_deriv_diff.differentiableOn.differentiableAt (
        IsOpen.mem_nhds isOpen_ball <| by simpa using this)
    -- By definition of $R$, we know that $R'''(z) = 12z f''(z^2) + 8z^3 f'''(z^2)$.
    have hR''' : ∀ z ∈ ball 0 1, deriv^[3] R z = 12 * z * deriv^[2] f (z ^ 2) +
      8 * z ^ 3 * deriv^[3] f (z ^ 2) := by
      intro z hz
      refine HasDerivAt.deriv (HasDerivAt.congr_of_eventuallyEq ?_ (
        Filter.eventuallyEq_of_mem (IsOpen.mem_nhds (isOpen_ball) hz) fun x hx => hR'' x hx))
      convert HasDerivAt.add (HasDerivAt.const_mul 2 (HasDerivAt.comp z (
        show HasDerivAt (deriv f) _ _ from hasDerivAt_deriv_iff.mpr ?_) (hasDerivAt_pow 2 z))) (
          HasDerivAt.mul (HasDerivAt.const_mul 4 (hasDerivAt_pow 2 z)) (
            HasDerivAt.comp z (show HasDerivAt (deriv^[2] f) _ _ from hasDerivAt_deriv_iff.mpr ?_) (
              hasDerivAt_pow 2 z))) using 1 <;> norm_num ; focus ring
      · exact h_f_deriv_diff.differentiableOn.differentiableAt (
        IsOpen.mem_nhds (isOpen_ball) <| by simpa using hz)
      · have h_diff : AnalyticOn ℂ (deriv (deriv f)) (ball 0 1) := by
          apply_rules [DifferentiableOn.analyticOn, hf.1.differentiableOn]
          · apply_rules [DifferentiableOn.deriv, h_f_deriv_diff.differentiableOn]
            · exact hf.1.differentiableOn
            · exact isOpen_ball
            · exact isOpen_ball
          · exact isOpen_ball
        exact h_diff.differentiableOn.differentiableAt (
          IsOpen.mem_nhds (isOpen_ball) <| by simpa using hz)
    convert HasDerivAt.deriv (HasDerivAt.congr_of_eventuallyEq (HasDerivAt.add (HasDerivAt.mul (
      HasDerivAt.const_mul 12 (hasDerivAt_id 0)) (HasDerivAt.comp _ (
        show HasDerivAt (deriv^[2] f) _ _ from hasDerivAt_deriv_iff.mpr ?_) (hasDerivAt_pow 2 _))) (
          HasDerivAt.mul (HasDerivAt.const_mul 8 (hasDerivAt_pow 3 _)) (
            HasDerivAt.comp _ (show HasDerivAt (deriv^[3] f) _ _ from hasDerivAt_deriv_iff.mpr ?_) (
              hasDerivAt_pow 2 _)))) (Filter.eventuallyEq_of_mem (
                ball_mem_nhds _ zero_lt_one) fun x hx => hR''' x hx)) using 1 <;> norm_num
    · have h_diff : AnalyticOn ℂ (deriv (deriv f)) (ball 0 1) := by
        apply_rules [DifferentiableOn.analyticOn, h_f_deriv_diff.differentiableOn]
        · apply_rules [DifferentiableOn.deriv, h_f_deriv_diff.differentiableOn]
          · exact hf.1.differentiableOn
          · exact isOpen_ball
          · exact isOpen_ball
        · exact isOpen_ball
      exact h_diff.differentiableOn.differentiableAt (ball_mem_nhds _ zero_lt_one)
    · have h_diff : AnalyticOn ℂ (deriv (deriv (deriv f))) (ball 0 1) := by
        apply_rules [DifferentiableOn.analyticOn, hf.1]
        · apply_rules [DifferentiableOn.deriv, hf.1.differentiableOn] <;> exact isOpen_ball
        · exact isOpen_ball
      exact h_diff.differentiableOn.differentiableAt (ball_mem_nhds _ zero_lt_one)
  -- Since $L(z) = R(z)$ for all $z$ in the unit disk, their derivatives must also be equal.
  have h_deriv_eq : deriv^[4] L 0 = deriv^[4] R 0 := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [ball_mem_nhds 0 zero_lt_one] with z hz using
      Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_of_mem (
        IsOpen.mem_nhds (isOpen_ball) hz) fun x hx =>
          Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_of_mem (
            IsOpen.mem_nhds (isOpen_ball) hx) fun y hy =>
              Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_of_mem (
                IsOpen.mem_nhds (isOpen_ball) hy) fun z hz => h_eq z hz
  linear_combination' h_deriv_eq / 8 - hL / 8 + hR / 8

/-
For any function f in class S, the second coefficient a_2 satisfies |a_2| <= 2.
-/
theorem bieberbach_second_coeff (f : ℂ → ℂ) (hf : f ∈ classS) :
    ‖deriv^[2] f 0 / 2‖ ≤ 2 := by
      -- Let $g$ be the square root transform of $f$, so $g \in S$ and $g(z)^2 = f(z^2)$.
  obtain ⟨g, hg₁, hg₂⟩ := square_root_transform_in_S f hf
  have := coeff_bound_of_S_two_three g hg₁
  rw [square_root_transform_deriv2 f hf g hg₁ hg₂,
    square_root_transform_deriv3 f hf g hg₁ hg₂] at this
  norm_num at this
  norm_num [div_eq_mul_inv] at * ; linarith!
