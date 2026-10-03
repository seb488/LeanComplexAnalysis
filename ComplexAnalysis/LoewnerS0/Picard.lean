import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Picard iteration for Carathéodory differential equations

Let `G : ℝ → E → E` be a time-dependent vector field which is only *measurable* in time (for each
fixed `x`), but Lipschitz in space uniformly in time and bounded. Then the integral equation

  `w(t) = z - ∫₀ᵗ G(s, w(s)) ds`,  `t ≥ 0`,

has a solution. Mathlib's Picard–Lindelöf theorem assumes continuity in time, so we redo the Picard
iteration: the iterates `w₀ = z`, `w_{n+1} = z - ∫₀ᵗ G(s, wₙ(s)) ds` satisfy
`‖w_{n+1}(t) - wₙ(t)‖ ≤ M Lⁿ t^{n+1}/(n+1)!`, so they converge, and the limit solves the equation
by dominated convergence.

Measurability of `s ↦ G(s, w(s))` for continuous (or strongly measurable) `w` is obtained by
approximating `w` by simple functions (`aestronglyMeasurable_comp`).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal Nat Interval

noncomputable section

namespace LoewnerS0.Picard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {G : ℝ → E → E}

/-! ### Measurability of `s ↦ G(s, w(s))` -/

section Measurability

variable {μ : Measure ℝ}

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma aestronglyMeasurable_comp_simpleFunc
    (hmeas : ∀ x, AEStronglyMeasurable (fun s => G s x) μ) (f : SimpleFunc ℝ E) :
    AEStronglyMeasurable (fun s => G s (f s)) μ := by
  have heq : (fun s => G s (f s)) =
      fun s => ∑ y ∈ f.range, (f ⁻¹' {y}).indicator (fun s => G s y) s := by
    funext s
    rw [Finset.sum_eq_single (f s)]
    · rw [Set.indicator_of_mem (by simp)]
    · intro y _ hy
      rw [Set.indicator_of_notMem]
      simp only [mem_preimage, mem_singleton_iff]
      exact fun h => hy h.symm
    · intro h
      exact absurd (f.mem_range_self s) h
  rw [heq]
  exact Finset.aestronglyMeasurable_fun_sum _ fun y _ =>
    (hmeas y).indicator (f.measurableSet_preimage {y})

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- **Carathéodory functions**: if `G` is continuous in space and a.e. strongly measurable in
time, then `s ↦ G(s, w(s))` is a.e. strongly measurable for strongly measurable `w`. -/
lemma aestronglyMeasurable_comp (hcont : ∀ s, Continuous (G s))
    (hmeas : ∀ x, AEStronglyMeasurable (fun s => G s x) μ) {w : ℝ → E}
    (hw : StronglyMeasurable w) : AEStronglyMeasurable (fun s => G s (w s)) μ :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => aestronglyMeasurable_comp_simpleFunc hmeas (hw.approx n))
    (Eventually.of_forall fun s => ((hcont s).tendsto (w s)).comp (hw.tendsto_approx s))

end Measurability

/-! ### The Picard iterates -/

/-- The Picard operator `w ↦ (t ↦ z - ∫₀ᵗ G(s, w(s)) ds)`. -/
def picard (G : ℝ → E → E) (z : E) (w : ℝ → E) (t : ℝ) : E :=
  z - ∫ s in (0)..t, G s (w s)

/-- The Picard iterates. -/
def iter (G : ℝ → E → E) (z : E) : ℕ → ℝ → E
  | 0 => fun _ => z
  | n + 1 => picard G z (iter G z n)

/-- The limit of the Picard iterates (for `t ≥ 0`). -/
def sol (G : ℝ → E → E) (z : E) (t : ℝ) : E :=
  z + ∑' n, (iter G z (n + 1) t - iter G z n t)

section Iteration

variable {L : ℝ≥0} {M : ℝ} (hlip : ∀ s, LipschitzWith L (G s)) (hbd : ∀ s x, ‖G s x‖ ≤ M)
  (hmeas : ∀ x, AEStronglyMeasurable (fun s => G s x) volume) (z : E)
include hlip hbd hmeas

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma intervalIntegrable_comp {w : ℝ → E} (hw : Continuous w) (a b : ℝ) :
    IntervalIntegrable (fun s => G s (w s)) volume a b := by
  have hm := aestronglyMeasurable_comp (fun s => (hlip s).continuous) hmeas hw.stronglyMeasurable
  rw [intervalIntegrable_iff]
  exact IntegrableOn.of_bound measure_Ioc_lt_top hm.restrict M
    (Eventually.of_forall fun s => hbd s _)

omit [CompleteSpace E] in
lemma continuous_iter (n : ℕ) : Continuous (iter G z n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    show Continuous (fun t => z - ∫ s in (0)..t, G s (iter G z n s))
    exact continuous_const.sub
      (intervalIntegral.continuous_primitive (intervalIntegrable_comp hlip hbd hmeas ih) 0)

omit [CompleteSpace E] in
lemma norm_iter_succ_sub_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖iter G z (n + 1) t - iter G z n t‖ ≤ M * L ^ n * t ^ (n + 1) / (n + 1)! := by
  induction n generalizing t with
  | zero =>
    show ‖(z - ∫ s in (0)..t, G s z) - z‖ ≤ _
    rw [sub_sub_cancel_left, norm_neg]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := M)
      (f := fun s => G s z) (fun s _ => hbd s z)
    simpa [abs_of_nonneg ht] using this
  | succ n ih =>
    have hc := continuous_iter hlip hbd hmeas z
    show ‖(z - ∫ s in (0)..t, G s (iter G z (n + 1) s)) -
      (z - ∫ s in (0)..t, G s (iter G z n s))‖ ≤ _
    rw [sub_sub_sub_cancel_left, ← intervalIntegral.integral_sub
      (intervalIntegrable_comp hlip hbd hmeas (hc n) 0 t)
      (intervalIntegrable_comp hlip hbd hmeas (hc (n + 1)) 0 t)]
    refine (intervalIntegral.norm_integral_le_of_norm_le ht
      (g := fun s => (L * (M * L ^ n / (n + 1)!)) * s ^ (n + 1)) ?_ ?_).trans (le_of_eq ?_)
    · filter_upwards with s hs
      rw [← dist_eq_norm, dist_comm]
      refine ((hlip s).dist_le_mul _ _).trans ?_
      rw [dist_eq_norm]
      calc (L : ℝ) * ‖iter G z (n + 1) s - iter G z n s‖
          ≤ L * (M * L ^ n * s ^ (n + 1) / (n + 1)!) :=
            mul_le_mul_of_nonneg_left (ih hs.1.le) L.2
        _ = (L * (M * L ^ n / (n + 1)!)) * s ^ (n + 1) := by ring
    · exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
    · rw [intervalIntegral.integral_const_mul, integral_pow]
      push_cast [Nat.factorial_succ]
      field_simp
      ring

omit [NormedSpace ℝ E] [CompleteSpace E] hlip hmeas in
lemma M_nonneg : 0 ≤ M := (norm_nonneg _).trans (hbd 0 0)

omit [CompleteSpace E] hlip hmeas in
/-- The iterates move at most `M t` from the initial value. -/
lemma norm_iter_sub_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : ‖iter G z n t - z‖ ≤ M * t := by
  have hM := M_nonneg hbd
  cases n with
  | zero =>
    show ‖z - z‖ ≤ M * t
    rw [sub_self, norm_zero]
    positivity
  | succ n =>
    show ‖(z - ∫ s in (0)..t, G s (iter G z n s)) - z‖ ≤ M * t
    rw [sub_sub_cancel_left, norm_neg]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := M)
      (f := fun s => G s (iter G z n s)) (fun s _ => hbd s _)
    simpa [abs_of_nonneg ht] using this

omit [CompleteSpace E] in
/-- The bound of `norm_iter_succ_sub_le` in summable form `M t (Lt)ⁿ/n!`. -/
lemma norm_iter_succ_sub_le' (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖iter G z (n + 1) t - iter G z n t‖ ≤ M * t * ((L * t) ^ n / n !) := by
  have hM := M_nonneg hbd
  refine (norm_iter_succ_sub_le hlip hbd hmeas z n ht).trans ?_
  have hf : (n ! : ℝ) ≤ (n + 1)! := by exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  have hf0 : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [mul_pow, div_le_iff₀ (by positivity)]
  calc M * L ^ n * t ^ (n + 1) = M * t * (L ^ n * t ^ n / n !) * n ! := by
        field_simp
        ring
    _ ≤ M * t * (L ^ n * t ^ n / n !) * (n + 1)! := by
        gcongr

omit [CompleteSpace E] hlip hbd hmeas in
lemma summable_majorant (t : ℝ) : Summable fun n : ℕ => M * t * ((L * t) ^ n / n !) :=
  (Real.summable_pow_div_factorial (L * t)).mul_left (M * t)

omit [CompleteSpace E] in
lemma summable_bound {t : ℝ} (ht : 0 ≤ t) :
    Summable fun n : ℕ => ‖iter G z (n + 1) t - iter G z n t‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => norm_iter_succ_sub_le' hlip hbd hmeas z n ht) (summable_majorant t)

lemma tendsto_iter {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => iter G z n t) atTop (𝓝 (sol G z t)) := by
  have hs : Summable fun n => iter G z (n + 1) t - iter G z n t :=
    Summable.of_norm (summable_bound hlip hbd hmeas z ht)
  have h1 := hs.hasSum.tendsto_sum_nat
  have h2 : ∀ n, iter G z n t =
      z + ∑ i ∈ Finset.range n, (iter G z (i + 1) t - iter G z i t) := by
    intro n
    rw [Finset.sum_range_sub (fun i => iter G z i t)]
    show iter G z n t = z + (iter G z n t - z)
    abel
  rw [show (fun n => iter G z n t) = fun n =>
    z + ∑ i ∈ Finset.range n, (iter G z (i + 1) t - iter G z i t) from funext h2]
  exact tendsto_const_nhds.add h1

lemma aestronglyMeasurable_sol {t : ℝ} (ht : 0 ≤ t) :
    AEStronglyMeasurable (fun s => G s (sol G z s)) (volume.restrict (Ι 0 t)) := by
  have hc := continuous_iter hlip hbd hmeas z
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n s => G s (iter G z n s)) (fun n => ?_) ?_
  · exact (aestronglyMeasurable_comp (fun s => (hlip s).continuous) hmeas
      (hc n).stronglyMeasurable).restrict
  · rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with s hs
    rw [uIoc_of_le ht] at hs
    exact ((hlip s).continuous.tendsto _).comp (tendsto_iter hlip hbd hmeas z hs.1.le)

/-- **Existence**: the limit of the Picard iterates solves the integral equation. -/
theorem sol_spec {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => G s (sol G z s)) volume 0 t ∧
      sol G z t = z - ∫ s in (0)..t, G s (sol G z s) := by
  have hc := continuous_iter hlip hbd hmeas z
  have hint : IntervalIntegrable (fun s => G s (sol G z s)) volume 0 t := by
    rw [intervalIntegrable_iff]
    exact IntegrableOn.of_bound measure_Ioc_lt_top (aestronglyMeasurable_sol hlip hbd hmeas z ht)
      M (Eventually.of_forall fun s => hbd s _)
  refine ⟨hint, ?_⟩
  -- pass to the limit in `iter (n + 1) t = z - ∫₀ᵗ G(s, iter n s) ds`
  have hlim1 : Tendsto (fun n => iter G z (n + 1) t) atTop (𝓝 (sol G z t)) :=
    (tendsto_iter hlip hbd hmeas z ht).comp (tendsto_add_atTop_nat 1)
  have hlim2 : Tendsto (fun n => z - ∫ s in (0)..t, G s (iter G z n s)) atTop
      (𝓝 (z - ∫ s in (0)..t, G s (sol G z s))) := by
    refine tendsto_const_nhds.sub ?_
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      (Eventually.of_forall fun n => (aestronglyMeasurable_comp (fun s => (hlip s).continuous)
        hmeas (hc n).stronglyMeasurable).restrict)
      (Eventually.of_forall fun n => Eventually.of_forall fun s _ => hbd s _)
      intervalIntegrable_const ?_
    filter_upwards with s hs
    rw [uIoc_of_le ht] at hs
    exact ((hlip s).continuous.tendsto _).comp (tendsto_iter hlip hbd hmeas z hs.1.le)
  exact tendsto_nhds_unique hlim1 hlim2

end Iteration

end LoewnerS0.Picard
