/-
Copyright (c) 2025 [Your Name]. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name], [Collaborator Name if applicable]
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic

public import ComplexAnalysis.PoissonIntegral
public import ComplexAnalysis.Positive.HerglotzRieszUnique

/-!
# The Herglotz–Riesz Representation Theorem

This file proves the Herglotz–Riesz representation theorem for positive harmonic functions on
the unit disc, as well as for analytic functions with positive real part on the unit disc.

## Main Results

Theorem `HerglotzRiesz_representation_harmonic`:
Every harmonic function `u : ℂ → ℝ` on the unit disc with `u(0) = 1` and
`u(z) > 0` for all `z` in the unit disc can be represented as
```
u z = ∫ (1 - ‖z‖^2) / ‖x - z‖^2 dμ(x)
```
where `μ` is a uniquely determined probability measure supported on the unit circle.

We also prove the analytic version, Theorem `HerglotzRiesz_representation_analytic`:
Every analytic function `p` on the unit disc with `p(0) = 1` and
mapping the unit disc into the right half-plane can be represented as
```
  p(z) = ∫ (x + z)/(x - z) dμ(x)
```
where `μ` is a uniquely determined probability measure supported on the unit circle.

## Implementation Notes

The proof proceeds by:

1. The existence of μ is proven in `HerglotzRiesz_representation_existence`.
The construction uses the Banach-Alaoglu theorem and the Riesz-Markov-Kakutani representation
theorem. Furthermore, we use the Poisson integral formula `harmonic_representation_scaled_radius`.
2. Uniqueness of μ is established via the identity principle in
Theorem `HerglotzRiesz_representation_uniqueness`.
3. Finally, we combine the two parts to obtain `HerglotzRiesz_representation_analytic`
and derive the harmonic version `HerglotzRiesz_representation_harmonic`.

## References

* G. Herglotz, "Über Potenzreihen mit positivem, reellen Teil im Einheitskreis", 1911,
Ber. Sächs. Ges. Wiss. Leipzig, 63, 501–511.
* F. Riesz, "Sur certains systèmes singuliers d'équations intégrales", 1911,
Ann. Sci. Éc. Norm. Supér., 28, 33–62.

## Tags

Herglotz theorem, Herglotz–Riesz theorem, Poisson integral, positive harmonic function,
positive real part, unit disc
-/
public section

open Complex InnerProductSpace MeasureTheory Metric Set Topology

/-! ## Properties of Herglotz–Riesz functions-/

/-- The Herglotz-Riesz kernel is integrable on the unit circle. -/
lemma herglotz_integrable (μ : ProbabilityMeasure (sphere (0 : ℂ) 1))
    (w : ℂ) (hw : w ∈ ball 0 1) :
    Integrable (fun x : (sphere (0 : ℂ) 1) => (x + w) / (x - w)) μ := by
  have h_bounded : ∃ C : ℝ, ∀ x ∈ μ.toMeasure.support, ‖(x + w) / (x - w)‖ ≤ C := by
    have h_cont : ContinuousOn (fun x : ℂ => (x + w) / (x - w)) (Metric.sphere 0 1) := by
      exact continuousOn_of_forall_continuousAt
        fun x hx => ContinuousAt.div (continuousAt_id.add continuousAt_const)
          (continuousAt_id.sub continuousAt_const) (sub_ne_zero_of_ne <| by aesop)
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_sphere 0 1) h_cont
    use C ; aesop
  refine MeasureTheory.Integrable.mono' (g := fun _ => h_bounded.choose) ?_ ?_ ?_
  · norm_num
  · have h_measurable : Measurable (fun x : ℂ => (x + w) / (x - w)) := by
      exact Measurable.mul (measurable_id.add_const _) (Measurable.inv (measurable_id.sub_const _))
    exact h_measurable.aestronglyMeasurable.comp_measurable measurable_subtype_coe
  · filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1 (
      show μ.toMeasure (μ.toMeasure.supportᶜ) = 0 by simp)] with x hx using
        h_bounded.choose_spec x <| by simpa using hx

/-- The Herglotz-Riesz representation produces a ℂ differentiable function. -/
lemma herglotz_hasDerivAt (μ : ProbabilityMeasure (sphere (0 : ℂ) 1))
    (w₀ : ℂ) (hw₀ : ‖w₀‖ < 1) :
    HasDerivAt (fun w : ℂ  => ∫ x : (sphere (0 : ℂ) 1), (x + w) / (x - w) ∂μ)
      (∫ x : (sphere (0 : ℂ) 1), 2 * x / (x - w₀) ^ 2 ∂μ) w₀ := by
  have h_diff_quot : Filter.Tendsto
    (fun w => (∫ x : (sphere (0 : ℂ) 1), ((x + w) / (x - w) - (x + w₀) / (x - w₀)) ∂μ) / (w - w₀))
      (nhdsWithin w₀ {w₀}ᶜ) (nhds (∫ x : (sphere (0 : ℂ) 1), 2 * x / (x - w₀)^2 ∂μ)) := by
    have h_diff_quot : Filter.Tendsto
      (fun w => ∫ x : (sphere (0 : ℂ) 1), ((x + w) / (x - w) - (x + w₀) / (x - w₀)) / (w - w₀) ∂μ)
        (nhdsWithin w₀ {w₀}ᶜ) (nhds (∫ x : (sphere (0 : ℂ) 1), 2 * x / (x - w₀)^2 ∂μ)) := by
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence ?_ ?_ ?_ ?_ ?_
      · use fun x => 8 / (1 - ‖w₀‖) ^ 2
      · refine Filter.eventually_of_mem self_mem_nhdsWithin fun n hn =>
          Measurable.aestronglyMeasurable ?_
        fun_prop
      · have h_bound : ∀ x ∈ μ.toMeasure.support, ∀ n, ‖n - w₀‖ < (1 - ‖w₀‖) / 2 →
          ‖((x + n) / (x - n) - (x + w₀) / (x - w₀)) / (n - w₀)‖ ≤ 8 / (1 - ‖w₀‖)^2 := by
          intros x hx n hn
          have h_norm : ‖(x : ℂ)‖ = 1 := by simp
          have h_bound : ‖((x + n) / (x - n) - (x + w₀) / (x - w₀)) / (n - w₀)‖ ≤
            8 / (1 - ‖w₀‖)^2 := by
            have h_denom : ‖x - n‖ ≥ (1 - ‖w₀‖) / 2 ∧ ‖x - w₀‖ ≥ (1 - ‖w₀‖) := by
              have h_triangle : ‖(x : ℂ) - n‖ ≥ 1 - ‖n‖ ∧ ‖(x : ℂ) - w₀‖ ≥ 1 - ‖w₀‖ := by
                exact ⟨by have := norm_sub_norm_le (x : ℂ) n; linarith,
                  by have := norm_sub_norm_le (x : ℂ) w₀; linarith⟩
              exact ⟨by cases abs_cases (‖n‖ - ‖w₀‖)
                <;> linarith [norm_sub_norm_le n w₀], h_triangle.2⟩
            have h_bound : ‖((x + n) / (x - n) - (x + w₀) / (x - w₀)) / (n - w₀)‖ ≤
              2 / (‖x - n‖ * ‖x - w₀‖) := by
              rw [div_sub_div] <;> norm_num [sub_ne_zero, show x ≠ n from by
                rintro rfl; exact absurd h_denom.left (by norm_num; linarith),
                  show x ≠ w₀ from by
                    rintro rfl
                    exact absurd h_denom.right (by norm_num; linarith)]
              have h_num : ‖((x + n) * (x - w₀) - (x - n) * (x + w₀))‖ = ‖2 * (n - w₀)‖ := by
                ring_nf
                norm_num [show (x : ℂ) * n * 2 - x * w₀ * 2 = (n * 2 - w₀ * 2) * x from by ring,
                  norm_mul]
              by_cases h : n - w₀ = 0 <;>
                simp_all [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
              positivity
            refine le_trans h_bound ?_
            rw [div_le_div_iff₀] <;> nlinarith [norm_nonneg (x - n), norm_nonneg (x - w₀)]
          exact h_bound
        rw [eventually_nhdsWithin_iff]
        rw [Metric.eventually_nhds_iff]
        exact ⟨(1 - ‖w₀‖) / 2, half_pos (sub_pos.mpr hw₀), fun n hn hn' =>
          Filter.eventually_of_mem (MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (
            show μ.toMeasure (μ.toMeasure.supportᶜ) = 0 from by simp)) fun x hx =>
              h_bound x (by aesop) n hn⟩
      · norm_num
      · have h_tendsto : ∀ x ∈ μ.toMeasure.support,
          Filter.Tendsto (fun n => ((x + n) / (x - n) - (x + w₀) / (x - w₀)) / (n - w₀))
            (nhdsWithin w₀ {w₀}ᶜ) (nhds (2 * x / (x - w₀) ^ 2)) := by
          intro x hx
          have h_norm : ‖(x : ℂ)‖ = 1 := by simp
          have h_lim : HasDerivAt (fun n : ℂ => (x + n) / (x - n))
            (2 * x / (x - w₀) ^ 2) w₀ := by
            convert HasDerivAt.div (HasDerivAt.add (hasDerivAt_const _ _) (hasDerivAt_id w₀))
              (HasDerivAt.sub (hasDerivAt_const _ _) (hasDerivAt_id w₀)) _ using 1 <;> norm_num
            · ring
            · exact sub_ne_zero_of_ne <| by
                rintro rfl
                exact absurd hw₀ <| by simp [h_norm]
          rw [hasDerivAt_iff_tendsto_slope] at h_lim
          exact h_lim.congr fun n => by rw [slope_def_field]
        refine MeasureTheory.measure_mono_null (t := μ.toMeasure.supportᶜ) ?_ ?_
        · exact fun x hx => fun hx' => hx <| h_tendsto x hx'
        · exact Measure.measure_compl_support
    simpa only [MeasureTheory.integral_div] using h_diff_quot
  rw [hasDerivAt_iff_tendsto_slope]
  refine h_diff_quot.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ (sub_pos.mpr hw₀))] with w hw₁ hw₂
  simp_all [div_eq_inv_mul, slope_def_field]
  have h_integrable :
    MeasureTheory.Integrable (fun x : (sphere (0 : ℂ) 1) => ((x : ℂ) - w)⁻¹ * ((x : ℂ) + w)) μ
      ∧ MeasureTheory.Integrable (fun x : (sphere (0 : ℂ) 1) =>
        ((x : ℂ) - w₀)⁻¹ * ((x : ℂ) + w₀)) μ := by
    have h_integrable2 (w : ℂ) (hw : ‖w‖ < 1) :
      MeasureTheory.Integrable (fun x : (sphere (0 : ℂ) 1) =>
        ((x : ℂ) - w)⁻¹ * ((x : ℂ) + w)) μ := by
      have h_integrable3 : MeasureTheory.Integrable (fun x : (sphere (0 : ℂ) 1) =>
        ((x : ℂ) + w) / ((x : ℂ) - w)) μ := by
          apply herglotz_integrable μ w
          simp [hw]
      simpa only [div_eq_inv_mul] using h_integrable3
    exact ⟨h_integrable2 w (by linarith [norm_sub_norm_le w w₀, dist_eq_norm w w₀]),
      h_integrable2 w₀ hw₀⟩
  exact Or.inl <| MeasureTheory.integral_sub h_integrable.1 h_integrable.2

/-- Every Herglotz–Riesz representation is analytic, maps 0 to 1 and the unit disc
into the right half-plane. -/
theorem HerglotzRiesz_realPos (μ : ProbabilityMeasure (sphere (0 : ℂ) 1)) :
    let p : ℂ → ℂ := fun z => ∫ x : (sphere (0 : ℂ) 1), (x + z) / (x - z) ∂μ
    AnalyticOn ℂ p (ball 0 1) ∧ p 0 = 1 ∧ MapsTo p (ball 0 1) {w : ℂ | 0 < w.re} := by
  refine ⟨?_, ?_, ?_⟩
  · apply_rules [DifferentiableOn.analyticOn]
    · refine fun z hz => DifferentiableAt.differentiableWithinAt ?_
      apply HasDerivAt.differentiableAt
      apply herglotz_hasDerivAt μ z
      apply mem_ball.mp at hz
      rw [dist_eq_norm, sub_zero] at hz
      exact hz
    · exact isOpen_ball
  · simp
  · have h_real_part (z : ℂ) (hz : z ∈ ball 0 1) :
      0 < Complex.re (∫ x : (sphere (0 : ℂ) 1), ((x + z) / (x - z)) ∂μ) := by
      have h_real_part (x : ℂ) (hx : ‖x‖ = 1) : 0 < Complex.re ((x + z) / (x - z)) := by
        norm_num [Complex.div_re]
        rw [← add_div, lt_div_iff₀] <;> norm_num [Complex.normSq, Complex.norm_def] at *
        · rw [Real.sqrt_lt'] at hz <;> nlinarith
        · rw [Real.sqrt_lt'] at hz <;> nlinarith [sq_nonneg (x.re * z.im - x.im * z.re)]
      have h_integral_pos : 0 < ∫ x : (sphere (0 : ℂ) 1), Complex.re ((x + z) / (x - z)) ∂μ := by
        rw [integral_pos_iff_support_of_nonneg_ae]
        · simp_all [Function.support]
          rw [show {x : ↑ (sphere (0 : ℂ) 1) | ¬ ((x + z) / (x - z) |> Complex.re) = 0} =
            Set.univ from Set.eq_univ_iff_forall.mpr fun x =>
             ne_of_gt <| h_real_part x <| by simp]
          aesop
        · filter_upwards
          intro x
          have h_norm : ‖(x : ℂ)‖ = 1 := by simp
          apply le_of_lt (h_real_part x h_norm)
        · refine Integrable.mono' (g:= fun x => ‖(x + z) / (x - z)‖) ?_ ?_ ?_
          · exact Integrable.norm (herglotz_integrable μ z hz)
          · exact Measurable.aestronglyMeasurable (Measurable.comp (Complex.measurable_re)
              (Measurable.div (Continuous.measurable (by continuity))
                (Continuous.measurable (by continuity))))
          · exact Filter.Eventually.of_forall fun x => Complex.abs_re_le_norm _
      convert h_integral_pos using 1
      have h_integral_re (f : (sphere (0 : ℂ) 1) → ℂ) (hf : Integrable f μ) :
        ∫ x : (sphere (0 : ℂ) 1), Complex.re (f x) ∂μ = Complex.re (
          ∫ x : (sphere (0 : ℂ) 1), f x ∂μ) := by exact (by convert integral_re hf)
      rw [h_integral_re]
      exact herglotz_integrable μ z hz
    exact fun z hz => h_real_part z hz

/-! ## Existence of the Herglotz–Riesz measure -/

/-- `u` is the real part of `p`. -/
abbrev u (p : ℂ → ℂ) (z : ℂ) : ℝ := (p z).re

/-- `u_n` is `u` scaled by `r n`. -/
abbrev u_n (p : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℝ := u p (r n * z)

abbrev C_unit_circle := C(↥(sphere (0 : ℂ) 1), ℝ)

/-- The Poisson kernel function for a fixed z in the unit disc, viewed as a
continuous function on the unit circle. -/
noncomputable def poisson_kernel_func (z : ℂ) (hz : z ∈ (ball 0 1)) : C_unit_circle :=
  ⟨fun w => ((w : ℂ) + z) / ((w : ℂ) - z) |> Complex.re, by
    /- The denominator w - z is never zero for w on the unit circle and
     z in the unit disc. -/
    have h_denom_ne_zero : ∀ w : (sphere (0 : ℂ) 1), w - z ≠ 0 := by
      intro w hw; simp_all [sub_eq_zero]
      rw [← hw] at hz
      have hw_norm : ‖(w : ℂ)‖ = 1 := by simp
      linarith [hw_norm, hz]
    exact Complex.continuous_re.comp (Continuous.div (
      continuous_subtype_val.add continuous_const) (
        continuous_subtype_val.sub continuous_const) fun w => h_denom_ne_zero w)⟩

/-- `circleMap` takes values on the unit circle. -/
lemma circleMap_mem_unit_circle (t : ℝ) : circleMap 0 1 t ∈ (sphere (0 : ℂ) 1) := by
  apply circleMap_mem_sphere
  norm_num

/-- The value of the functional `Λ_n` on `C_unit_circle`. -/
noncomputable def Λ_n_val (p : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ) (f : C_unit_circle) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t in 0..2*Real.pi, f ⟨
    circleMap 0 1 t, circleMap_mem_unit_circle t⟩ * u_n p r n (circleMap 0 1 t)

/-- The linear map `Λ_n_linear`. -/
noncomputable def Λ_n_linear (p : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ)
    (h : Continuous (u_n p r n ∘ circleMap 0 1)) : C_unit_circle →ₗ[ℝ] ℝ where
  toFun f := Λ_n_val p r n f
  map_add' f g := by
    unfold Λ_n_val; simp [add_mul]
    rw [← mul_add, intervalIntegral.integral_add]
    · apply_rules [Continuous.intervalIntegrable]
      exact Continuous.mul (f.continuous.comp <| by continuity) h
    · apply_rules [Continuous.intervalIntegrable]
      exact Continuous.mul (g.continuous.comp <| by continuity) h
  map_smul' c f := by
    unfold Λ_n_val
    simp [mul_assoc, mul_left_comm, ← intervalIntegral.integral_const_mul]

/-- The bound `Λ_n_bound` for the functional `Λ_n`, defined as
1/2π ∫ t in 0..2*π  |u_n(e^{it})| dt. -/
noncomputable def Λ_n_bound (p : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t in 0..2*Real.pi, |u_n p r n (circleMap 0 1 t)|

-- The continuous linear functional `Λ_n`.
noncomputable def Λ_n (p : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ)
    (h : Continuous (u_n p r n ∘ circleMap 0 1)) : C_unit_circle →L[ℝ] ℝ :=
  LinearMap.mkContinuous (Λ_n_linear p r n h) (Λ_n_bound p r n) (by
  /- By the properties of the integral and the bound on the integrand,
  we can show that the absolute value of the integral is less than or equal
  to the integral of the absolute value. -/
  have h_integral_bound : ∀ f : C_unit_circle, |∫ t in (0 : ℝ)..2 * Real.pi, f ⟨
    circleMap 0 1 t, circleMap_mem_unit_circle t⟩ * u_n p r n (circleMap 0 1 t)| ≤
      ∫ t in (0 : ℝ)..2 * Real.pi, |u_n p r n (circleMap 0 1 t)| * ‖f‖ := by
    intros f
    have h_integral_bound : |∫ t in (0 : ℝ)..2 * Real.pi, f ⟨
      circleMap 0 1 t, circleMap_mem_unit_circle t⟩ * u_n p r n (circleMap 0 1 t)| ≤
        ∫ t in (0 : ℝ)..2 * Real.pi, |f ⟨circleMap 0 1 t, circleMap_mem_unit_circle t⟩ *
          u_n p r n (circleMap 0 1 t)| := by
      simpa only [intervalIntegral.integral_of_le Real.two_pi_pos.le] using
        norm_integral_le_integral_norm (_ : ℝ → ℝ)
    refine le_trans h_integral_bound (
      intervalIntegral.integral_mono_on ?_ ?_ ?_ ?_) <;> norm_num [abs_mul]
    · positivity
    · apply_rules [Continuous.intervalIntegrable]
      fun_prop (disch := norm_num)
    · exact Continuous.intervalIntegrable (by continuity) _ _
    · exact fun x _ _ => by rw [mul_comm] ; exact mul_le_mul_of_nonneg_left (
        ContinuousMap.norm_coe_le_norm f _) (abs_nonneg _)
  unfold Λ_n_linear Λ_n_bound
  simp_all [div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm]
  unfold Λ_n_val; intro f; convert mul_le_mul_of_nonneg_left (h_integral_bound f) (
    by positivity : 0 ≤ (1 : ℝ) / (2 * Real.pi)) using 1; focus ring_nf
  · norm_num [mul_assoc, mul_comm, mul_left_comm, abs_mul, abs_inv, abs_of_nonneg, Real.pi_pos.le]
  · ring)

/-- We also need the dual space of `C_unit_circle`. -/
abbrev C_unit_circleDual := C_unit_circle →L[ℝ] ℝ

def K : Set C_unit_circleDual := {Λ | ∀ f : C_unit_circle, ‖f‖ < 1 → |Λ f| ≤ 1}

def K_weak : Set (WeakDual ℝ C_unit_circle) := K

/-- The complex Poisson kernel is integrable on the unit circle
with respect to any finite measure. -/
lemma complex_kernel_integrable (μ : Measure (sphere (0 : ℂ) 1))
    [IsFiniteMeasure μ] (z : ℂ) (hz : z ∈ ball 0 1) :
    Integrable (fun w : (sphere (0 : ℂ) 1) => ((w : ℂ) + z) / ((w : ℂ) - z)) μ := by
  /- The function f(w)=(w+z)(w-z) is continuous on the unit circle. -/
  have h_cont : Continuous (fun w : (sphere (0 : ℂ) 1) => ((w : ℂ) + z) / ((w : ℂ) - z)) := by
    refine Continuous.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · norm_num at *
      intro a ha h_eq
      have : a = z := sub_eq_zero.mp h_eq
      rw [this] at ha
      linarith [ha, hz]
  apply_rules [Continuous.integrable_of_hasCompactSupport]
  rw [hasCompactSupport_iff_eventuallyEq]
  simp [Filter.EventuallyEq]

/-- The integral of the Poisson kernel is the real part of
the integral of the Herglotz–Riesz kernel. -/
lemma integral_poisson_eq_re_integral (μ : Measure (sphere (0 : ℂ) 1))
    [IsFiniteMeasure μ] (z : ℂ) (hz : z ∈ ball 0 1) :
    ∫ w, (poisson_kernel_func z hz) w ∂μ = (∫ w : (sphere (0 : ℂ) 1),
      ((w : ℂ) + z) / ((w : ℂ) - z) ∂μ).re := by
  convert (integral_re _)
  any_goals tauto
  · exact rfl
  · convert complex_kernel_integrable μ z hz using 1

/-- `u_n p` is positive on the unit circle when `p` takes value in the right half-plane`. -/
lemma u_n_pos (p : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ) (hp : MapsTo p (ball 0 1) {w : ℂ | 0 < w.re})
    (hr : r n ∈ Ioo 0 1) (z : ℂ) (hz : z ∈ (sphere 0 1)) : 0 < u_n p r n z := by
  have h_rnz_in_D : (r n : ℂ) * z ∈ Metric.ball 0 1 := by
    simp
    have hz_norm : ‖z‖ = 1 := by simp [Metric.sphere] at hz; exact hz
    rw [abs_of_pos hr.1, hz_norm] ; linarith [hr.2]
  generalize_proofs at *; aesop

/-- The mean value property for `u_n p` at 0. -/
lemma u_n_mean_value (p : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ)
    (hp_analytic : AnalyticOn ℂ p (ball 0 1))
    (hp0 : p 0 = 1)
    (hr : r n ∈ Ioo 0 1) :
    (1 / (2 * Real.pi)) * ∫ t in 0..2*Real.pi, u_n p r n (circleMap 0 1 t) = 1 := by
  /- By the Cauchy integral formula (or mean value property),
  1/2π ∫ t in 0..2*π  f(e^{it}) dt = f(0) = p(0) = 1. -/
  have h_mean_value_property : (1 / (2 * Real.pi)) * ∫ t in (0)..2 * Real.pi,
    p (r n * circleMap 0 1 t) = p 0 := by
    /- Since `p` is analytic on the unit disc and r_n is in (0, 1),
    the function `z ↦ p(r_n z)` is analytic on the closed unit disc. -/
    have h_analytic : AnalyticOn ℂ (fun z => p (r n * z)) (closedBall 0 1) := by
      apply_rules [hp_analytic.comp, AnalyticOn.mul, analyticOn_id, analyticOn_const]
      intro z hz
      exact lt_of_le_of_lt (
        by simpa [abs_of_pos hr.1] using mul_le_mul_of_nonneg_left (
          mem_closedBall_zero_iff.mp hz) hr.1.le) hr.2
    have := @Complex.circleIntegral_div_sub_of_differentiable_on_off_countable
    specialize @this 1 0 0 {0} ; norm_num at this
    specialize @this (fun z => p (r n * z)) ?_ ?_ <;> norm_num at *
    · exact h_analytic.continuousOn
    · intro z hz hz'; exact h_analytic.differentiableOn.differentiableAt (
        Metric.closedBall_mem_nhds_of_mem (by aesop))
    · simp_all [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, circleIntegral]
      simp_all [mul_left_comm (circleMap 0 1 _), mul_comm, ne_of_gt (Real.pi_pos)]
  -- Taking the real part of both sides of the mean value property, we get the desired result.
  have h_real_part : (1 / (2 * Real.pi)) * ∫ t in (0)..2 * Real.pi,
    (p (r n * circleMap 0 1 t)).re = (p 0).re := by
    convert congr_arg Complex.re h_mean_value_property using 1
    -- The integral of the real part of a function is the real part of the integral.
    have h_real_part_integral (f : ℝ → ℂ) (hf : Continuous f) :
      ∫ t in (0)..2 * Real.pi, (f t).re = (∫ t in (0)..2 * Real.pi, f t).re := by
      rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
        intervalIntegral.integral_of_le Real.two_pi_pos.le]
      convert (integral_re (hf.integrableOn_Ioc))
      infer_instance
    rw [h_real_part_integral] ; focus norm_num [mul_assoc, mul_comm, mul_left_comm]
    refine ContinuousOn.comp_continuous (s := {z : ℂ | ‖z‖ < 1}) ?_ ?_ ?_
    · refine hp_analytic.continuousOn.mono fun x hx => ?_
      simp only [Metric.mem_ball, Complex.dist_eq, sub_zero]
      exact hx
    · continuity
    · norm_num [circleMap, abs_of_pos hr.1]
      linarith [hr.2]
  aesop

/-- `u_n p r n` composed with `circleMap` is continuous. -/
lemma u_n_continuous (p : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ)
    (hp_analytic : AnalyticOn ℂ p (ball (0 : ℂ) 1))
    (hr : r n ∈ Ioo 0 1) :
    Continuous (u_n p r n ∘ circleMap 0 1) := by
  -- Since `p` is analytic and `circleMap` is continuous, their composition is continuous.
  have h_cont : Continuous (fun t => p (r n * circleMap 0 1 t)) := by
    refine hp_analytic.continuousOn.comp_continuous ?_ ?_
    · continuity
    · simp [circleMap]
      simpa only [abs_of_pos hr.1] using hr.2
  exact Complex.continuous_re.comp h_cont

/-- The sequence `u(p(r_n · z))` converges to `u(p(z))` as `r_n` converges to 1. -/
lemma u_limit_at_z (p : ℂ → ℂ) (r_seq : ℕ → ℝ)
    (hp_analytic : AnalyticOn ℂ p (ball (0 : ℂ) 1))
    (hr_lim : Filter.Tendsto r_seq Filter.atTop (nhds 1))
    (z : ℂ) (hz : z ∈ ball 0 1) :
    Filter.Tendsto (fun n => u p (r_seq n * z)) Filter.atTop (nhds (u p z)) := by
  have h_cont : Filter.Tendsto (fun n => p (r_seq n * z)) Filter.atTop (nhds (p z)) := by
    convert hp_analytic.continuousOn.continuousAt _ |> Filter.Tendsto.comp <| ?_ using 2
    · apply IsOpen.mem_nhds
      · exact isOpen_ball
      · exact hz
    · simpa using Filter.Tendsto.mul (
      Complex.continuous_ofReal.continuousAt.tendsto.comp hr_lim) tendsto_const_nhds
  exact Filter.Tendsto.comp (Complex.continuous_re.tendsto _) h_cont

/-- The real part of an analytic function is harmonic. -/
lemma harmonic_of_analytic_real
    (u : ℂ → ℝ)
    (p : ℂ → ℂ)
    (hp : AnalyticOn ℂ p (ball 0 1))
    (h_real : ∀ z ∈ ball 0 1, (p z).re = u z) :
    InnerProductSpace.HarmonicOnNhd u (ball 0 1) := by
  have h_harmonic : ∀ x ∈ ball 0 1, InnerProductSpace.HarmonicAt (fun z => (p z).re) x := by
    intro x hx
    have hx': ‖x‖ < 1 := by simpa using hx
    have h_analytic : AnalyticAt ℂ p x := by
      apply_rules [DifferentiableOn.analyticAt, hp.differentiableOn]
      apply IsOpen.mem_nhds
      · exact isOpen_ball
      · exact hx
    have h_harmonic : InnerProductSpace.HarmonicAt (fun z => (p z).re) x := by
      exact AnalyticAt.harmonicAt_re h_analytic
    exact h_harmonic
  intros x hx
  have h_eq : ∀ᶠ z in nhds x, u z = (p z).re := by
    exact Filter.eventually_of_mem (IsOpen.mem_nhds (Metric.isOpen_ball) hx) fun z hz =>
      h_real z hz ▸ rfl
  exact (InnerProductSpace.harmonicAt_congr_nhds h_eq).mpr (h_harmonic x hx)

/-- The value of `u` at `r_n * z` is equal to the functional
`Λ_n` applied to the Poisson kernel at `z`. -/
lemma u_approx_eq_Lambda (p : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ)
    (hp_analytic : AnalyticOn ℂ p (ball 0 1))
    (hr : r n ∈ Ioo 0 1)
    (z : ℂ) (hz : z ∈ ball 0 1) :
    u p (r n * z) = Λ_n_val p r n (poisson_kernel_func z hz) := by
  have : InnerProductSpace.HarmonicOnNhd (u p) (ball 0 1) := by
    refine harmonic_of_analytic_real (u p) p hp_analytic ?_
    simp [u]
  convert harmonic_representation_scaled_radius this hr hz using 1
  unfold poisson_kernel_func Λ_n_val; norm_num [circleMap]
  simp [add_comm, u_n]
  congr 1
  ext t
  rw [mul_comm (↑t : ℂ) I]

lemma K_eq_polar : K_weak = WeakDual.polar ℝ (Metric.ball 0 1) := by
  ext Λ
  simp [K_weak, K, WeakDual.polar, Metric.ball, dist_eq_norm]
  constructor
  · intro h f hf; apply h; simp at hf; exact hf
  · intro h f hf; apply h; simp; exact hf

/-- We apply the Banach-Alaoglu theorem to show that `K` is compact in the weak* topology. -/
lemma K_weak_compact : CompactSpace K_weak := by
  rw [K_eq_polar]
  have h_nhds : Metric.ball (0 : C_unit_circle) 1 ∈ 𝓝 0 := by
    rw [Metric.mem_nhds_iff]
    use 1
    simp
  have h_compact : IsCompact (WeakDual.polar ℝ (Metric.ball (0 : C_unit_circle) 1)) :=
    WeakDual.isCompact_polar ℝ h_nhds
  rw [isCompact_iff_compactSpace] at h_compact
  exact h_compact

/-- As a separable space, `C_unit_circle` contains a dense sequence `dense_seq`. -/
noncomputable def dense_seq : ℕ → C_unit_circle := TopologicalSpace.denseSeq C_unit_circle

noncomputable def embed (Λ : WeakDual ℝ C_unit_circle) : ℕ → ℝ := fun n => Λ (dense_seq n)

lemma embed_continuous : Continuous embed := by
  apply continuous_pi
  intro n
  exact (WeakBilin.eval_continuous (topDualPairing ℝ C_unit_circle) (dense_seq n))

lemma embed_injective : Function.Injective embed := by
  /- To prove injectivity, assume that two elements `Λ` and `Λ'` in the dual space
  have the same image under the embedding. This means that for every `n`,
  `Λ (dense_seq n) = Λ' (dense_seq n)`. -/
  intro Λ Λ' h_eq
  have h_eval : ∀ f : C_unit_circle, Λ f = Λ' f := by
    /- Since the dense sequence is dense in `C_unit_circle`, for any `f` in `C_unit_circle`,
    there exists a sequence `f_n` in the dense sequence such that `f_n` converges to `f`. -/
    have h_dense : ∀ f : C_unit_circle, ∃ (
      f_n : ℕ → C_unit_circle), (∀ n, f_n n ∈ Set.range dense_seq) ∧
        Filter.Tendsto f_n Filter.atTop (nhds f) := by
      intro f
      obtain ⟨f_n, hf_n⟩ : ∃ (f_n : ℕ → C_unit_circle),
        (∀ n, f_n n ∈ Set.range dense_seq) ∧ Filter.Tendsto f_n Filter.atTop (nhds f) := by
        have h_dense : Dense (Set.range dense_seq) := by
          exact TopologicalSpace.denseRange_denseSeq _
        exact mem_closure_iff_seq_limit.mp (h_dense f)
      exact ⟨f_n, hf_n⟩
    have h_cont : ∀ f : C_unit_circle, ∀ (f_n : ℕ → C_unit_circle),
      Filter.Tendsto f_n Filter.atTop (nhds f) → Filter.Tendsto (
        fun n => Λ (f_n n)) Filter.atTop (nhds (Λ f)) ∧
          Filter.Tendsto (fun n => Λ' (f_n n)) Filter.atTop (nhds (Λ' f)) := by
      exact fun f f_n hf_n => ⟨Λ.continuous.continuousAt.tendsto.comp hf_n,
        Λ'.continuous.continuousAt.tendsto.comp hf_n⟩
    /- By combining the results from `h_dense` and `h_cont`, we can conclude that
    `Λ(f) = Λ'(f)` for any `f` in `C_unit_circle`. -/
    intros f
    obtain ⟨f_n, hf_n_range, hf_n_conv⟩ := h_dense f
    have h_eq_seq : ∀ n, Λ (f_n n) = Λ' (f_n n) := by
      intro n
      obtain ⟨m, hm⟩ : ∃ m, f_n n = dense_seq m := by
        simpa [eq_comm] using hf_n_range n
      replace h_eq := congr_fun h_eq m; aesop
    exact tendsto_nhds_unique (h_cont f f_n hf_n_conv |>.1) (
      by simpa only [h_eq_seq] using h_cont f f_n hf_n_conv |>.2)
  /- Since `Λ` and `Λ'` are equal on all elements of `C_unit_circle`,
  they must be equal as linear functionals. -/
  apply ContinuousLinearMap.ext; intro f; exact h_eval f

/-- The metrizability of the space `K_weak`. -/
lemma K_weak_metrizable : TopologicalSpace.MetrizableSpace (Subtype K_weak) := by
  let embed_K : K_weak → (ℕ → ℝ) := fun Λ => embed Λ.val
  have h_cont : Continuous embed_K := embed_continuous.comp continuous_subtype_val
  have h_inj : Function.Injective embed_K := by
    intro Λ₁ Λ₂ h
    apply Subtype.ext
    apply embed_injective
    exact h
  have h_compact : CompactSpace K_weak := K_weak_compact
  have h_t2 : T2Space (ℕ → ℝ) := inferInstance
  have h_closed_embedding : IsClosedEmbedding embed_K :=
    Continuous.isClosedEmbedding h_cont h_inj
  have h_embedding : IsEmbedding embed_K := h_closed_embedding.isEmbedding
  exact h_embedding.metrizableSpace

/-- `|Λ f| ≤ 1` whenever `‖f‖ < 1`. -/
lemma norm_lambda_leq_one (p : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ)
    (hp_analytic : AnalyticOn ℂ p (ball (0 : ℂ) 1))
    (hp0 : p 0 = 1)
    (hp_map : MapsTo p (ball (0 : ℂ) 1) {w : ℂ | 0 < w.re})
    (hr : r n ∈ Ioo 0 1) :
    let Λ := Λ_n p r n (u_n_continuous p r n hp_analytic hr)
    ∀ f : C_unit_circle, ‖f‖ < 1 → |Λ f| ≤ 1 := by
  intros Λ f hf
  have h_abs : |Λ f| ≤ (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..2 * Real.pi,
    |u_n p r n (circleMap 0 1 t)| := by
    have h_abs : |Λ_n_val p r n f| ≤ (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..2 * Real.pi,
      |u_n p r n (circleMap 0 1 t)| := by
      have h_abs : |Λ_n_val p r n f| ≤ (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..2 * Real.pi,
        |f ⟨circleMap 0 1 t, circleMap_mem_unit_circle t⟩| * |u_n p r n (circleMap 0 1 t)| := by
        rw [Λ_n_val]
        norm_num [← abs_mul]
        rw [abs_mul, abs_of_nonneg (by positivity)]
        gcongr
        simpa only [intervalIntegral.integral_of_le Real.two_pi_pos.le] using
          norm_integral_le_integral_norm (_ : ℝ → ℝ)
      refine le_trans h_abs (mul_le_mul_of_nonneg_left (
        intervalIntegral.integral_mono_on ?_ ?_ ?_ ?_) (by positivity))
      · positivity
      · apply_rules [Continuous.intervalIntegrable]
        exact Continuous.mul (continuous_abs.comp <| f.continuous.comp <| by continuity)
          (continuous_abs.comp <| by exact u_n_continuous p r n hp_analytic hr)
      · apply_rules [Continuous.intervalIntegrable]
        exact Continuous.abs (u_n_continuous p r n hp_analytic hr)
      · exact fun t ht => mul_le_of_le_one_left (abs_nonneg _) (
          by simpa using f.norm_coe_le_norm ⟨
            circleMap 0 1 t, circleMap_mem_unit_circle t⟩ |> le_trans <| le_of_lt hf)
    exact h_abs
  -- Since `u_n` is the real part of p(r_n e^{it}), we have |u_n(e^{it})| = u_n(e^{it}).
  have h_abs_eq : ∫ t in (0 : ℝ)..2 * Real.pi, |u_n p r n (circleMap 0 1 t)| =
    ∫ t in (0 : ℝ)..2 * Real.pi, u_n p r n (circleMap 0 1 t) := by
    refine intervalIntegral.integral_congr fun t ht => abs_of_nonneg ?_
    apply le_of_lt; exact u_n_pos p r n hp_map hr (circleMap 0 1 t) (circleMap_mem_unit_circle t)
  have := u_n_mean_value p r n hp_analytic hp0 hr; aesop

/-- The space `K_weak` is sequentially compact. -/
lemma K_weak_seq_compact : SeqCompactSpace (Subtype K_weak) := by
  have h₁ : CompactSpace (Subtype K_weak) := K_weak_compact
  have h₂ : TopologicalSpace.MetrizableSpace (Subtype K_weak) := K_weak_metrizable
  exact FirstCountableTopology.seq_compact_of_compact

/-- The sequence of functionals `Λ_n`. -/
noncomputable def Λ_seq (p : ℂ → ℂ) (r : ℕ → ℝ) (hp_analytic : AnalyticOn ℂ p (ball (0 : ℂ) 1))
    (hr : ∀ n, r n ∈ Ioo 0 1) (n : ℕ) : WeakDual ℝ C_unit_circle :=
  Λ_n p r n (u_n_continuous p r n hp_analytic (hr n))

/-- The sequence `Λ_seq` is in `K_weak`. -/
lemma Λ_seq_mem_K (p : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ)
    (hp_analytic : AnalyticOn ℂ p (ball (0 : ℂ) 1))
    (hp0 : p 0 = 1)
    (hp_map : MapsTo p (ball (0 : ℂ) 1) {w : ℂ | 0 < w.re})
    (hr : ∀ k, r k ∈ Ioo 0 1) :
    Λ_seq p r hp_analytic hr n ∈ K_weak := by
  exact fun f hf => by simpa using norm_lambda_leq_one p r n hp_analytic hp0 hp_map (hr n) f hf

/-- There exists a subsequence Λ_{n_k} converging to some Λ in the weak* topology. -/
lemma Λ_seq_converging_subsequence (p : ℂ → ℂ) (r : ℕ → ℝ)
    (hp_analytic : AnalyticOn ℂ p (ball (0 : ℂ) 1))
    (hp0 : p 0 = 1)
    (hp_map : MapsTo p (ball (0 : ℂ) 1) {w : ℂ | 0 < w.re})
    (hr : ∀ n, r n ∈ Ioo 0 1) :
    ∃ (phi : ℕ → ℕ) (Λ : WeakDual ℝ C_unit_circle), StrictMono phi ∧
    ∀ f : C_unit_circle, Filter.Tendsto (fun k => (Λ_seq p r hp_analytic hr (phi k)) f)
     Filter.atTop (nhds (Λ f)) := by
  -- By Lemma `Λ_seq_mem_K`, each Λ_n is in `K_weak`.
  have h_seq_in_K : ∀ n, Λ_seq p r hp_analytic hr n ∈ K_weak := by
    exact fun n ↦ Λ_seq_mem_K p r n hp_analytic hp0 hp_map hr
  -- We can use `K_weak_seq_compact`.
  obtain ⟨phi, hphi⟩ : ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ Λ : WeakDual ℝ C_unit_circle,
    Filter.Tendsto (fun k => Λ_seq p r hp_analytic hr (phi k)) Filter.atTop (nhds Λ) := by
    have := K_weak_seq_compact
    obtain ⟨Λ, hΛ⟩ : ∃ Λ : Subtype K_weak, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Filter.Tendsto (fun k => ⟨Λ_seq p r hp_analytic hr (phi k), h_seq_in_K (phi k)⟩ : ℕ →
        Subtype K_weak) Filter.atTop (nhds Λ) := by
      have := this.1
      have := this (fun n => Set.mem_univ (
        ⟨Λ_seq p r hp_analytic hr n, h_seq_in_K n⟩ : Subtype K_weak)) ; aesop
    exact ⟨hΛ.choose, hΛ.choose_spec.1, Λ,
      by simpa using tendsto_subtype_rng.mp hΛ.choose_spec.2⟩
  obtain ⟨Λ, hΛ⟩ := hphi.2
  refine ⟨phi, Λ, hphi.1, ?_⟩
  intro f
  -- By the definition of the weak* topology, the evaluation maps are continuous.
  have h_eval_cont : Continuous (fun Λ : WeakDual ℝ C_unit_circle => Λ f) := by
    exact WeakDual.eval_continuous f
  exact h_eval_cont.continuousAt.tendsto.comp hΛ

/-- Each Λ_n is a positive functional. -/
lemma Λ_n_nonneg (p : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ)
    (hp_analytic : AnalyticOn ℂ p (ball (0 : ℂ) 1))
    (hp_map : MapsTo p (ball (0 : ℂ) 1) {w : ℂ | 0 < w.re})
    (hr : r n ∈ Ioo 0 1) :
    let Λ := Λ_n p r n (u_n_continuous p r n hp_analytic hr)
    ∀ f : C_unit_circle, 0 ≤ f → 0 ≤ Λ f := by
  intro Λ f hf_nonneg
  /- Since `u_n` is positive on the unit circle and `f` is non-negative,
  their product `f * u_n` is non-negative. -/
  have h_prod_nonneg : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
      0 ≤ f (⟨circleMap 0 1 t, circleMap_mem_unit_circle t⟩) * u_n p r n (circleMap 0 1 t) := by
    exact fun t ht => mul_nonneg (hf_nonneg _) (le_of_lt (u_n_pos p r n hp_map hr _ (
      circleMap_mem_unit_circle t)))
  refine mul_nonneg (by positivity) (
    intervalIntegral.integral_nonneg (by positivity) fun t ht => h_prod_nonneg t ht)

/-- We apply the Riesz–Markov–Kakutani representation theorem for `Λ` to obtain the measure `μ`. -/
lemma riesz_rep (Λ : WeakDual ℝ C_unit_circle)
    (h_pos : ∀ f : C_unit_circle, 0 ≤ f → 0 ≤ Λ f) :
    ∃ μ : Measure (sphere (0 : ℂ) 1), IsFiniteMeasure μ ∧
    ∀ f : C_unit_circle, Λ f = ∫ z, f z ∂μ := by

  /- Since Λ is a positive linear functional on C(∂𝔻, ℝ),
  it is a positive linear functional on C_c(∂𝔻, ℝ). -/
  have h_ext : ∃ (Λ_c : CompactlySupportedContinuousMap (sphere (0 : ℂ) 1) ℝ →ₚ[ℝ] ℝ),
    ∀ (f : CompactlySupportedContinuousMap (sphere (0 : ℂ) 1) ℝ),
      Λ_c f = Λ (ContinuousMap.mk (fun z : (sphere (0 : ℂ) 1) => f z)) := by
    refine ⟨?_, ?_⟩
  -- Define the positive linear functional
    · exact { toFun := fun f => Λ ⟨fun z => f z, f.continuous⟩
              map_add' := by intro x y; convert Λ.map_add _ _ using 1
              map_smul' := by intro m x; convert Λ.map_smul m _ using 1
              monotone' := by
                intro f g hfg
                have key : 0 ≤ Λ ⟨fun z => g z - f z, by continuity⟩ := by
                  apply h_pos; intro z; exact sub_nonneg_of_le (hfg z)
                calc Λ ⟨fun z => f z, f.continuous⟩
                  ≤ Λ ⟨fun z => f z, f.continuous⟩ + Λ ⟨fun z => g z - f z, by continuity⟩ :=
                    le_add_of_nonneg_right key
                _ = Λ ⟨fun z => g z, g.continuous⟩ := by
                    rw [← Λ.map_add]; congr 1; ext z; simp }
    · intro f; rfl
  obtain ⟨Λ_c, hΛ_c⟩ := h_ext
  refine ⟨RealRMK.rieszMeasure Λ_c, ?_, ?_⟩
  · constructor ; norm_num [RealRMK.rieszMeasure]
  · intro f
    obtain ⟨f_c, hf_c⟩ : ∃ f_c : CompactlySupportedContinuousMap (sphere (0 : ℂ) 1) ℝ,
      ∀ z : (sphere (0 : ℂ) 1), f_c z = f z := by
      refine ⟨⟨f, ?_⟩, ?_⟩
      · rw [hasCompactSupport_iff_eventuallyEq]
        simp [Filter.EventuallyEq]
      · exact fun z ↦ rfl
    convert RealRMK.integral_rieszMeasure Λ_c f_c using 1
    · rw [RealRMK.integral_rieszMeasure] ; aesop
    convert RealRMK.integral_rieszMeasure Λ_c f_c using 1
    simp only [hf_c]


/-- Convergence of the subsequence of linear functionals. -/
lemma convergence_sub_seq_functionals (p : ℂ → ℂ) (r : ℕ → ℝ)
    (hp_analytic : AnalyticOn ℂ p (ball (0 : ℂ) 1))
    (hp0 : p 0 = 1)
    (hp_map : MapsTo p (ball (0 : ℂ) 1) {w : ℂ | 0 < w.re})
    (hr : ∀ n, r n ∈ Ioo 0 1) :
    ∃ (μ : ProbabilityMeasure (sphere (0 : ℂ) 1)) (phi : ℕ → ℕ),
      StrictMono phi ∧ ∀ f : C_unit_circle, 0 ≤ f →
        Filter.Tendsto (fun k => (Λ_seq p r hp_analytic hr (phi k)) f)
          Filter.atTop (nhds (∫ z, f z ∂μ)) := by
  have := Λ_seq_converging_subsequence p r hp_analytic hp0 hp_map hr
  obtain ⟨phi, Λ, hphi, hΛ⟩ := this
  obtain ⟨μ, hμ⟩ := riesz_rep Λ (by
    intro f hf_nonneg
    specialize hΛ f
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hΛ fun k =>
     Λ_n_nonneg p r (phi k) hp_analytic hp_map (hr (phi k)) f hf_nonneg)
  -- We need to show that `μ` is a probability measure.
  have h_prob : IsProbabilityMeasure μ := by
    have h_const : Λ (1 : C_unit_circle) = 1 := by
      convert tendsto_nhds_unique (hΛ 1) _
      convert tendsto_const_nhds.congr' _
      filter_upwards [Filter.eventually_gt_atTop 0] with k hk
      convert Eq.symm (u_n_mean_value p r (phi k) hp_analytic hp0 (hr (phi k))) using 1
      unfold Λ_seq; unfold Λ_n; unfold Λ_n_linear; norm_num
      unfold Λ_n_val; norm_num; ring_nf
      exact congr_arg₂ _ (congr_arg₂ _ rfl (by norm_num)) rfl
    have h : μ Set.univ = 1 := by
      rw [← ENNReal.toReal_eq_one_iff] ; aesop
    exact ⟨by simpa using h⟩
  use ⟨μ, h_prob⟩
  use phi
  exact ⟨hphi, fun f hf => by simpa only [hμ.2] using hΛ f⟩

/-- The value of `u` at `z` is equal to the real part of the integral
of the Herglotz–Riesz kernel against the measure `μ`, under hypothesis of
weak* convergence of `Λ_seq`. -/
lemma u_eq_limit_Lambda (p : ℂ → ℂ) (r : ℕ → ℝ)
    (hp_analytic : AnalyticOn ℂ p (ball (0 : ℂ) 1))
    (hr : ∀ n, r n ∈ Ioo 0 1)
    (hr_lim : Filter.Tendsto r Filter.atTop (nhds 1))
    (μ : ProbabilityMeasure (sphere (0 : ℂ) 1))
    (phi : ℕ → ℕ)
    (hphi_strict_mono : StrictMono phi)
    (hΛ_tendsto : ∀ f : C_unit_circle,
      Filter.Tendsto (fun k => (Λ_seq p r hp_analytic hr (phi k)) f)
        Filter.atTop (nhds (∫ z, f z ∂μ)))
    (z : ℂ) (hz : z ∈ ball 0 1) :
    u p z = (∫ w : (sphere (0 : ℂ) 1), ((w : ℂ) + z) / ((w : ℂ) - z) ∂μ).re := by
  -- Applying `u_approx_eq_Lambda` to the limit expression.
  have h_lambda_limit : Filter.Tendsto (fun k => u p (r (phi k) * z)) Filter.atTop (
    nhds (∫ w, (poisson_kernel_func z hz w) ∂μ)) := by
    convert hΛ_tendsto (poisson_kernel_func z hz) using 1
    exact funext fun k => u_approx_eq_Lambda p r (phi k) hp_analytic (hr (phi k)) z hz
  have h_u_limit : Filter.Tendsto (fun k =>
    u p (r (phi k) * z)) Filter.atTop (nhds (u p z)) := by
    convert u_limit_at_z p r hp_analytic _ z hz |> Filter.Tendsto.comp <|
      hphi_strict_mono.tendsto_atTop using 1
    exact hr_lim
  exact tendsto_nhds_unique h_u_limit h_lambda_limit ▸ integral_poisson_eq_re_integral μ z hz

/-- If two analytic functions on the unit disc have the same value at 0
and equal real parts, then they are equal on the unit disc. -/
lemma analytic_unique_of_real_part
    (f g : ℂ → ℂ)
    (hf : AnalyticOn ℂ f (ball (0 : ℂ) 1))
    (hg : AnalyticOn ℂ g (ball (0 : ℂ) 1))
    (h_re : ∀ z ∈ (ball (0 : ℂ) 1), (f z).re = (g z).re)
    (h_zero : f 0 = g 0) :
    EqOn f g (ball (0 : ℂ) 1) := by
  -- Let `h(z) = f(z) - g(z)`. We need to show that `h(z) = 0` for all z in the unit disc.
  let h : ℂ → ℂ := fun z => f z - g z
  have ball_zero_one_eq : ball (0 : ℂ) 1 = {z : ℂ | ‖z‖ < 1} := by
    ext z
    simp [Metric.mem_ball]
  rw [ball_zero_one_eq] at ⊢ hf hg

  let unitDisc := {z : ℂ | ‖z‖ < 1}
  have h_analytic : AnalyticOn ℂ h unitDisc := by
    exact hf.sub hg
  have h_zero : h 0 = 0 := by aesop
  have h_real_part : ∀ z ∈ unitDisc, (h z).re = 0 := by aesop
  /- Since `h` is analytic on the unit disc and its real part is zero,
  by the Cauchy-Riemann equations, `h` must be constant. -/
  have h_const : ∀ z ∈ unitDisc, h z = h 0 := by
    have h_const : ∀ z ∈ unitDisc, deriv h z = 0 := by
      intro z hz
      have h_cauchy_riemann : HasDerivAt h (deriv h z) z := by
        exact h_analytic.differentiableOn.differentiableAt (
          IsOpen.mem_nhds (
            isOpen_lt continuous_norm continuous_const) hz) |> DifferentiableAt.hasDerivAt
      have h_cauchy_riemann : HasDerivAt (fun x : ℝ => h (z + x)) (
        deriv h z) 0 ∧ HasDerivAt (
          fun x : ℝ => h (z + Complex.I * x)) (deriv h z * Complex.I) 0 := by
        constructor
        · rw [hasDerivAt_iff_tendsto_slope_zero] at *
          convert h_cauchy_riemann.comp (show Filter.Tendsto (
            fun t : ℝ => ↑t) (𝓝[≠] 0) (𝓝[≠] 0) from Filter.Tendsto.inf (
              Continuous.tendsto' (by continuity) _ _ <|
                by norm_num) <| by aesop) using 2 ; aesop
        · convert HasDerivAt.comp 0 (show HasDerivAt h (deriv h z) (
          z + Complex.I * 0) from by simpa using h_cauchy_riemann) (
            HasDerivAt.const_add z <| HasDerivAt.const_mul Complex.I <|
              hasDerivAt_id 0 |> HasDerivAt.ofReal_comp) using 1 ; norm_num
      have h_cauchy_riemann : HasDerivAt (
        fun x : ℝ => (h (z + x)).re) (deriv h z).re 0 ∧ HasDerivAt (
          fun x : ℝ => (h (z + Complex.I * x)).re) (deriv h z * Complex.I).re 0 := by
        field_simp
        constructor
        · rw [hasDerivAt_iff_tendsto_slope_zero] at *
          convert Complex.continuous_re.continuousAt.tendsto.comp h_cauchy_riemann.1 using 2
          norm_num
        · rw [hasDerivAt_iff_tendsto_slope_zero] at *
          convert Complex.continuous_re.continuousAt.tendsto.comp (
            h_cauchy_riemann.2.tendsto_slope_zero) using 2
          · norm_num
          ring_nf
      have h_cauchy_riemann : HasDerivAt (fun x : ℝ => (h (z + x)).re) 0 0 ∧ HasDerivAt (
        fun x : ℝ => (h (z + Complex.I * x)).re) 0 0 := by
        have h_cauchy_riemann : ∀ᶠ x in nhds 0, (h (z + x)).re = 0 ∧
          (h (z + Complex.I * x)).re = 0 := by
          rw [Metric.eventually_nhds_iff]
          obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp (
            IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) hz);
          exact ⟨ε, hε, fun y hy => ⟨h_real_part _ <| hε' <| by simpa using hy,
            h_real_part _ <| hε' <| by simpa using hy⟩⟩
        exact ⟨HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const _ _) (
          by filter_upwards [h_cauchy_riemann.filter_mono (
            Complex.continuous_ofReal.continuousAt)] with x hx using hx.1),
              HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const _ _) (
                by filter_upwards [h_cauchy_riemann.filter_mono (
                  Complex.continuous_ofReal.continuousAt)] with x hx using hx.2)⟩
      simp_all [Complex.ext_iff, hasDerivAt_iff_tendsto_slope_zero]
      exact ⟨tendsto_nhds_unique (by tauto) h_cauchy_riemann.1, neg_eq_zero.mp (
        tendsto_nhds_unique (by tauto) h_cauchy_riemann.2)⟩

    have h_ftc (z : ℂ) (hz : z ∈ unitDisc) : h z = h 0 := by
      have h_ftc_step (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : deriv (fun t => h (t * z)) t = 0 := by
        have h_ftc_step' : deriv (fun t => h (t * z)) t = deriv h (t * z) * z := by
          convert HasDerivAt.deriv (HasDerivAt.comp (t : ℂ) (
            h_analytic.differentiableOn.differentiableAt (IsOpen.mem_nhds (
              show IsOpen unitDisc from isOpen_lt continuous_norm continuous_const) ?_) |>
                DifferentiableAt.hasDerivAt) (hasDerivAt_mul_const z)) using 1
          exact show ‖(t : ℂ) * z‖ < 1 from
            by simpa [abs_of_nonneg ht.1] using lt_of_le_of_lt (
              mul_le_of_le_one_left (norm_nonneg _) (mod_cast ht.2)) (by simpa using hz)
        simp_all [unitDisc]
        exact Or.inl <| h_const _ <| by simpa [abs_of_nonneg ht.1] using lt_of_le_of_lt (
          mul_le_of_le_one_left (norm_nonneg _) ht.2) hz
      /- By fundamental theorem of calculus, if the derivative of a function is zero,
      then the function is constant. -/
      have h_ftc : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → ∫ t in a..b, deriv (
        fun t => h (t * z)) t = h (b * z) - h (a * z) := by
        intros a b _ _ _; rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
        · intro x hx
          have h_diff : DifferentiableAt ℂ (fun t => h (t * z)) x := by
            have h_diff : DifferentiableOn ℂ h unitDisc := by
              exact h_analytic.differentiableOn
            refine h_diff.differentiableAt ?_ |> DifferentiableAt.comp ?_ <|
              differentiableAt_id.mul_const _
            exact IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) (
              show ‖ (x : ℂ) * z‖ < 1 from by simpa [abs_of_nonneg (
                show 0 ≤ x by cases Set.mem_uIcc.mp hx <;> linarith)] using lt_of_le_of_lt (
                  mul_le_of_le_one_left (norm_nonneg _) (
                    show |x| ≤ 1 by cases Set.mem_uIcc.mp hx <;> exact abs_le.mpr ⟨
                      by linarith, by linarith⟩)) hz)
          convert h_diff.hasDerivAt.comp_ofReal using 1
        · exact (ContinuousOn.intervalIntegrable (
          by rw [continuousOn_congr fun t ht => h_ftc_step t ⟨by linarith [Set.mem_Icc.mp (
            by simpa [*] using ht)], by linarith [Set.mem_Icc.mp (
              by simpa [*] using ht)]⟩] ; exact continuousOn_const))
      simp at *
      have := h_ftc 0 1; rw [intervalIntegral.integral_congr fun t ht => h_ftc_step t (
        by norm_num at ht; linarith) (
          by norm_num at ht; linarith)] at this; norm_num at *; linear_combination' this.symm
    exact h_ftc
  exact fun z hz => sub_eq_zero.mp (h_const z hz |> Eq.trans <| h_zero)

/-- Every analytic function `p` on the unit disc with `p(0) = 1` and
mapping the unit disc to the right half-plane admits a Herglotz–Riesz representation. -/
theorem HerglotzRiesz_representation_existence (p : ℂ → ℂ)
    (hp_analytic : AnalyticOn ℂ p (ball (0 : ℂ) 1))
    (hp0 : p 0 = 1)
    (hp_map : MapsTo p (ball (0 : ℂ) 1) {w : ℂ | 0 < w.re}) :
    ∃ μ : ProbabilityMeasure (sphere (0 : ℂ) 1),
    ∀ z ∈ (ball (0 : ℂ) 1), p z = ∫ x : (sphere (0 : ℂ) 1), (x + z) / (x - z) ∂μ := by
  let r : ℕ → ℝ := fun n => 1 - 1 / (n + 2)
  have hr : ∀ n, r n ∈ Ioo 0 1 := by
    intro n ; simp [r] ; constructor
    · have : (1 : ℝ) < (↑n+2 : ℝ) := by linarith
      exact inv_lt_one_of_one_lt₀ this
    · linarith
  obtain ⟨μ, phi, hphi_strict_mono,
    hΛ_tendsto⟩ := convergence_sub_seq_functionals p r hp_analytic hp0 hp_map hr
  obtain ⟨hq_analytic,hq0,_⟩ := HerglotzRiesz_realPos μ
  dsimp at *
  /- We apply `u_eq_limit_Lambda`. -/
  have h_u_eq_limit_Lambda : ∀ z ∈ (ball (0 : ℂ) 1), u p z =
    (∫ w : (sphere (0 : ℂ) 1), ((w : ℂ) + z) / ((w : ℂ) - z) ∂μ).re := by
    apply_rules [u_eq_limit_Lambda]
    · exact le_trans (tendsto_const_nhds.sub
      <| tendsto_const_nhds.div_atTop
      <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop) <| by norm_num
    · intro f
      /- Since `f` is a continuous function on the unit circle,
      we can write it as the difference of two non-negative continuous functions. -/
      obtain ⟨f_pos, f_neg, hf_pos, hf_neg, hf⟩ : ∃ f_pos f_neg : C((sphere (0 : ℂ) 1), ℝ),
        0 ≤ f_pos ∧ 0 ≤ f_neg ∧ f = f_pos - f_neg := by
        use ContinuousMap.mk (fun x => max (f x) 0), ContinuousMap.mk (fun x => max (-f x) 0)
        exact ⟨fun x => le_max_right _ _, fun x =>
          le_max_right _ _, by ext x; simp [max_def] ; split_ifs <;> linarith⟩
      convert Filter.Tendsto.sub (
        hΛ_tendsto f_pos hf_pos) (hΛ_tendsto f_neg hf_neg) using 2 ; focus aesop
      rw [← integral_sub] ; focus aesop
      · exact Continuous.integrable_of_hasCompactSupport (by continuity) (
          by exact HasCompactSupport.of_compactSpace f_pos)
      · exact Continuous.integrable_of_hasCompactSupport (by continuity) (
          by exact HasCompactSupport.of_compactSpace f_neg)
  -- By `analytic_unique_of_real_part`, `p(z) = q(z)` for all `z` in the unit disc.
  have h_p_eq_q : ∀ z ∈ (ball (0 : ℂ) 1),
    p z = ∫ w : (sphere (0 : ℂ) 1), ((w : ℂ) + z) / ((w : ℂ) - z) ∂μ := by
    apply_rules [analytic_unique_of_real_part]
    rw [hp0]
    exact hq0.symm
  exact ⟨μ, h_p_eq_q⟩

/-! ## Main results -/

/-- Every analytic function `p` on the unit disc with `p(0) = 1` and
mapping the unit disc into the right half-plane admits a unique
Herglotz–Riesz representation. -/
theorem HerglotzRiesz_representation_analytic
    (p : ℂ → ℂ) (hp_analytic : AnalyticOn ℂ p (ball (0 : ℂ) 1)) (hp0 : p 0 = 1)
    (h_real_pos : MapsTo p (ball (0 : ℂ) 1) {w : ℂ | 0 < w.re}) :
    ∃! μ : ProbabilityMeasure (sphere (0 : ℂ) 1),
    ∀ z ∈ (ball (0 : ℂ) 1), p z = ∫ x : (sphere (0 : ℂ) 1), (x + z) / (x - z) ∂μ := by
    -- Existence
    obtain ⟨μ, hμ_rep⟩ :=
     HerglotzRiesz_representation_existence p hp_analytic hp0 h_real_pos
    -- Uniqueness
    refine ExistsUnique.intro ?μ ?hμ ?uniq
    · exact μ
    · exact hμ_rep
    · intro ν  hν
      -- split the conjunction
      symm
      refine HerglotzRiesz_representation_uniqueness μ ν ?_
      intro z hz
      calc ∫ x : (sphere (0 : ℂ) 1), (x + z) / (x - z) ∂μ
            = p z := (hμ_rep z hz).symm
        _ = ∫ x : (sphere (0 : ℂ) 1), (x + z) / (x - z) ∂ν := hν z hz

/- Every harmonic function `u` on the unit disc with `u(0) = 1` and
`u(z) > 0` for all `z` admits a unique Herglotz–Riesz integral representation. -/
theorem HerglotzRiesz_representation_harmonic
    (f : ℂ → ℝ)
    (h_pos : ∀ z ∈ (ball (0 : ℂ) 1), 0 < f z)
    (h_u_zero : f 0 = 1) (h_harmonic : HarmonicOnNhd f (ball (0 : ℂ) 1)) :
    ∃! μ : ProbabilityMeasure (sphere (0 : ℂ) 1),
    ∀ z ∈ (ball (0 : ℂ) 1), f z = ∫ x : (sphere (0 : ℂ) 1),  (1 - ‖z‖^2) / ‖x - z‖^2 ∂μ := by

  let unitDisc := ball (0 : ℂ) 1
  let unitCircle := sphere (0 : ℂ) 1
  have exists_analytic_of_harmonic_unitDisc (g : ℂ → ℝ) (hg : HarmonicOnNhd g unitDisc) :
    ∃ F : ℂ → ℂ, AnalyticOn ℂ F unitDisc ∧ (∀ z ∈ unitDisc, (F z).re = g z) ∧ F 0 = g 0 := by
    have h_ball : unitDisc = Metric.ball (0 : ℂ) 1 := by
      ext z; simp [unitDisc, Metric.mem_ball, dist_zero_right]
    rw [h_ball] at hg
    obtain ⟨G, hG_analytic, hG_real⟩ := harmonic_is_realOfHolomorphic hg
    -- Convert AnalyticOnNhd to AnalyticOn
    have hG_on : AnalyticOn ℂ G (Metric.ball 0 1) := by
      apply AnalyticOnNhd.analyticOn hG_analytic
    let c := (G 0).im
    let F := fun z => G z - I * c
    refine ⟨F, ?_, ?_, ?_⟩
    · rw [h_ball]; exact hG_on.sub analyticOn_const
    · -- We need to show that Re(F) = g.
      intro z hz; rw [h_ball] at hz; simp only [F]
      rw [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      simp
      exact hG_real hz
    · simp only [F]
      apply Complex.ext
      · simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
        exact hG_real (by simp)
      · simp [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, c]

  obtain ⟨F, hF_analytic, hF_re⟩ : ∃ F : ℂ → ℂ, AnalyticOn ℂ F unitDisc ∧
    (∀ z ∈ unitDisc, (F z).re = f z) ∧ (F 0) = f 0 := by
    exact exists_analytic_of_harmonic_unitDisc f h_harmonic

  have h_real_pos : MapsTo F unitDisc {w : ℂ | 0 < w.re} := by
    intro z hz
    simp only [Set.mem_setOf]
    rw [hF_re.1 z hz]
    exact h_pos z hz
  have hF0 : F 0 = 1 := by simp [hF_re.2, h_u_zero]

  obtain ⟨μ, h_rep⟩ := HerglotzRiesz_representation_existence F hF_analytic hF0 h_real_pos

  -- Taking the real part and using `real_part_herglotz_kernel`, we get
  have h_real_part : ∀ z ∈ unitDisc, f z = ∫ x : unitCircle, (1 - ‖z‖^2) / ‖(x : ℂ) - z‖^2 ∂μ := by
    have h_real_part' : ∀ z ∈ unitDisc, (F z).re = ∫ x : unitCircle, ((x + z) / (x - z)).re ∂μ := by
      intro z hz; rw [h_rep z hz] ; rw [← integral_re_add_im]
      · aesop
      refine Integrable.mono' (g := fun x => 2 / (1 - ‖z‖)) ?_ ?_ ?_
      · norm_num [integrable_const_iff]
      · refine Measurable.aestronglyMeasurable ?_; fun_prop
      · have hz' : ‖z‖ < 1 := by simpa [unitDisc, Metric.mem_ball, dist_eq_norm] using hz
        simp_all
        refine Filter.Eventually.of_forall fun x => ?_
        have hx : ‖(x : ℂ)‖ = 1 := by simp
        gcongr <;> norm_num [hx]
        · exact hz'
        · exact le_trans (norm_add_le _ _) (by linarith [hx, hz'])
        · simpa using norm_sub_le (x - z) (-z)
    have h_real_part_eq : ∀ z ∈ unitDisc, ∀ x : unitCircle,
      ((x + z) / (x - z)).re = (1 - ‖z‖^2) / ‖(x : ℂ) - z‖^2 := by
      intros z hz x;
      have hx : ‖(x : ℂ)‖ = 1 := by simp
      exact real_part_herglotz_kernel hx
    exact fun z hz => by rw [← hF_re.1 z hz, h_real_part' z hz, integral_congr_ae (
      Filter.Eventually.of_forall fun x => h_real_part_eq z hz x)]
  refine ExistsUnique.intro ?μ ?hμ ?uniq
  · exact μ
  · exact h_real_part
  · intro ν hν
    symm
    set g : ℂ → ℂ := fun z => ∫ x : unitCircle, (x + z) / (x - z) ∂ν
    -- Apply theorem `HerglotzRiesz_realPos` to g.
    have hg : AnalyticOn ℂ g unitDisc ∧ g 0 = 1 ∧ MapsTo g unitDisc {w : ℂ | 0 < w.re} := by
      have := HerglotzRiesz_realPos ν
      exact this
    obtain ⟨hg_analytic, hg0, hg_map⟩ := hg
    /- By `analytic_unique_of_real_part`, since `F` and `g` are analytic,
    have the same real part `u`, and `F(0)=g(0)=1`, we must have `f=g` on the unit disc. -/
    have h_fg_equal : ∀ z ∈ unitDisc, F z = g z := by
      apply analytic_unique_of_real_part F g hF_analytic hg_analytic
      · intro z hz
        have hz' : ‖z‖ < 1 := by simpa [unitDisc, Metric.mem_ball, dist_eq_norm] using hz
        have hg_real_part : (g z).re = ∫ x : unitCircle, (1 - ‖z‖^2) / ‖(x : ℂ) - z‖^2 ∂ν := by
          have hg_real_part' : (g z).re = ∫ x : unitCircle, ((x + z) / (x - z)).re ∂ν := by
            have h_integrable : Integrable (fun x : unitCircle => ((x + z) / (x - z))) ν := by
              refine Integrable.mono' (g := fun x => 2 / (1 - ‖z‖)) ?_ ?_ ?_
              · norm_num [integrable_const_iff]
              · refine Measurable.aestronglyMeasurable ?_
                fun_prop
              · filter_upwards with x
                rw [norm_div]
                have hx : ‖(x : ℂ)‖ = 1 := by simp
                gcongr
                · exact sub_pos_of_lt (by simpa using hz')
                · exact le_trans (norm_add_le _ _) (by linarith[hz', hx])
                · have := norm_sub_norm_le (x : ℂ) z
                  exact le_trans (sub_le_sub_right (show ‖ (x : ℂ)‖ ≥ 1 from by simp) _) this
            exact (integral_re h_integrable) ▸ rfl
          rw [hg_real_part']
          refine integral_congr_ae ?_
          filter_upwards with x
          have hx : ‖(x : ℂ)‖ = 1 := by simp
          exact real_part_herglotz_kernel hx
        rw [hF_re.1 z hz, hg_real_part, hν z hz]
      · rw [hF_re.2, h_u_zero] ; exact hg0.symm
    apply HerglotzRiesz_representation_uniqueness μ ν
    intro z hz
    calc ∫ (x : unitCircle), (↑x + z) / (↑x - z) ∂μ
      _ = F z := (h_rep z hz).symm
      _ = g z := h_fg_equal z hz
      _ = ∫ (x : unitCircle), (↑x + z) / (↑x - z) ∂ν := rfl
