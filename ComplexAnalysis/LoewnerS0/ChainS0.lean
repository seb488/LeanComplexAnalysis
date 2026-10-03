import LoewnerS0.ChainGenerator
import LoewnerS0.LoewnerExist

/-!
# Normal Loewner chains give parametric representations (assuming Osgood's theorem)

Let `F` be a Loewner chain on the unit ball `𝔹` of a finite-dimensional complex inner product
space with `{e⁻ᵗ F_t}` locally bounded, and let `h = LoewnerS0.chainField F` be its Herglotz vector
field (`LoewnerS0.ChainGenerator`). Assuming Osgood's theorem:

* the transition maps `v(z, t) = v(z, 0, t) = F_t⁻¹(F_0(z))` are Lipschitz in `t`, with
  `‖v(z, t) - v(z, s)‖ ≤ (t - s) 4‖z‖/(1-‖z‖)²`;
* at almost every `t`, `∂_t v(z, t) = lim (v(w, t, t+ε) - w)/ε = -h(v(z, t), t)` with
  `w = v(z, t)` (semigroup property and `LoewnerS0.IsLoewnerChain.tendsto_transition`);
* so `v` solves the Loewner ODE (`LoewnerS0.IsLoewnerChain.isLoewnerSolution_transition`, by the
  fundamental theorem of calculus for absolutely continuous functions);
* `F_t(v(z, t)) = F_0(z)`, `‖v(z, t)‖ ≤ e^{-t} ‖z‖/(1-‖z‖)²` and `e⁻ᵗ F_t(w) = w + O(‖w‖²)`
  uniformly in `t` give `eᵗ v(z, t) → F_0(z)`.

Hence `S⁰'(𝔹) ⊆ S⁰(𝔹)` (`LoewnerS0.classS0'_subset_classS0_of_osgood`).
-/

open Function Complex Metric Set Filter MeasureTheory
open scoped Topology InnerProductSpace NNReal

noncomputable section

namespace LoewnerS0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {F : ℝ → E → E}

namespace IsLoewnerChain

variable (hF : IsLoewnerChain F) (hO : OsgoodTheorem E)

section Lipschitz

include hF hO

/-- `‖v(z, t) - v(z, s)‖ ≤ (t - s) 4‖z‖/(1-‖z‖)²`. -/
lemma norm_transition_sub_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {z : E}
    (hz : z ∈ unitBall E) :
    ‖transition F 0 t z - transition F 0 s z‖ ≤ (t - s) * (4 * ‖z‖ / (1 - ‖z‖) ^ 2) := by
  have hz1 : ‖z‖ < 1 := mem_unitBall.mp hz
  have hw : ‖transition F 0 s z‖ ≤ ‖z‖ := hF.norm_transition_le hO le_rfl hs hz
  rw [← hF.transition_transition le_rfl hs hst hz, norm_sub_rev]
  have h1 := hF.norm_sub_transition_le hO hs hst hz1 hw
  have h2 := one_sub_exp_sub_le (s := s) (t := t)
  have hc0 : 0 ≤ 4 * ‖z‖ / (1 - ‖z‖) ^ 2 := by
    have : 0 < 1 - ‖z‖ := by linarith
    positivity
  exact h1.trans (mul_le_mul_of_nonneg_right h2 hc0)

/-- `t ↦ v(z, t)` is Lipschitz on `[0, ∞)`. -/
lemma lipschitzOnWith_transition {z : E} (hz : z ∈ unitBall E) :
    LipschitzOnWith (4 * ‖z‖ / (1 - ‖z‖) ^ 2).toNNReal (fun t => transition F 0 t z) (Ici 0) := by
  have hc0 : 0 ≤ 4 * ‖z‖ / (1 - ‖z‖) ^ 2 := by
    have : 0 < 1 - ‖z‖ := by linarith [mem_unitBall.mp hz]
    positivity
  refine LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_
  rw [Real.coe_toNNReal _ hc0, dist_eq_norm, Real.dist_eq]
  rcases le_total s t with hst | hts
  · rw [norm_sub_rev, abs_of_nonpos (by linarith), mul_comm]
    have := hF.norm_transition_sub_le hO hs hst hz
    linarith
  · rw [abs_of_nonneg (by linarith), mul_comm]
    exact hF.norm_transition_sub_le hO ht hts hz

end Lipschitz

variable (hloc : IsLocallyBounded fun t z => (Real.exp (-t) : ℂ) • F t z)
include hF hO hloc

/-- **The Loewner ODE for the transition maps** holds almost everywhere:
`∂_t v(z, t) = -h(v(z, t), t)`. -/
theorem ae_hasDerivAt_transition {z : E} (hz : z ∈ unitBall E) :
    ∀ᵐ t, 0 < t → HasDerivAt (fun τ => transition F 0 τ z)
      (-chainField F t (transition F 0 t z)) t := by
  have hlip := hF.lipschitzOnWith_transition hO hz
  have hdiff : ∀ᵐ t : ℝ, 0 < t → DifferentiableAt ℝ (fun τ => transition F 0 τ z) t := by
    have hm : ∀ m : ℕ, ∀ᵐ t : ℝ, t ∈ Icc (0 : ℝ) m →
        DifferentiableWithinAt ℝ (fun τ => transition F 0 τ z) (Icc 0 m) t :=
      fun m => (hlip.mono Icc_subset_Ici_self).ae_differentiableWithinAt_of_mem
    filter_upwards [ae_all_iff.mpr hm] with t ht ht0
    obtain ⟨m, hmt⟩ := exists_nat_gt t
    exact (ht m ⟨ht0.le, hmt.le⟩).differentiableAt (Icc_mem_nhds ht0 hmt)
  filter_upwards [hdiff, hF.ae_isGoodTime hO hloc] with t hd hg ht
  have hgood := hg ht
  have hwB : transition F 0 t z ∈ unitBall E := hF.transition_mem le_rfl ht.le hz
  have h1 := (hd ht).hasDerivAt
  have h2 := h1.tendsto_slope_zero_right
  have h3 := hF.tendsto_transition hO hloc hgood hwB
  have h4 : Tendsto (fun ε : ℝ => ε⁻¹ • (transition F 0 (t + ε) z - transition F 0 t z))
      (𝓝[>] 0) (𝓝 (-chainGen F t (transition F 0 t z))) := by
    refine h3.neg.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0 : ℝ) < ε := hε
    rw [← hF.transition_transition le_rfl ht.le (by linarith : t ≤ t + ε) hz, ← smul_neg,
      neg_sub]
  have h5 := tendsto_nhds_unique h2 h4
  rw [hF.chainField_eq hO hloc hgood, ← h5]
  exact h1

/-- The transition maps `v(z, t) = v(z, 0, t)` **solve the Loewner ODE** of the Herglotz vector
field of the chain. -/
theorem isLoewnerSolution_transition [CompleteSpace E] :
    IsLoewnerSolution (chainField F) fun t z => transition F 0 t z := by
  intro z hz t ht
  have hz1 : ‖z‖ < 1 := mem_unitBall.mp hz
  have hh := hF.isHerglotzVF_chainField hO hloc
  set M := 4 * ‖z‖ / (1 - ‖z‖) ^ 2 with hM
  have hM0 : 0 ≤ M := by
    have : 0 < 1 - ‖z‖ := by linarith
    positivity
  have hnorm : ∀ s, 0 ≤ s → ‖transition F 0 s z‖ ≤ ‖z‖ := fun s hs =>
    hF.norm_transition_le hO le_rfl hs hz
  have hbd : ∀ s, 0 ≤ s → ‖chainField F s (transition F 0 s z)‖ ≤ M := fun s hs =>
    (isCaratheodory_chainField s).norm_le_of_norm_le hz1 (hnorm s hs)
  -- measurability and integrability of the field along the solution
  set ρ := max ‖z‖ (1 / 2) with hρ
  have hρ0 : 0 < ρ := lt_max_of_lt_right (by norm_num)
  have hρ1 : ρ < 1 := max_lt hz1 (by norm_num)
  have hlip := hF.lipschitzOnWith_transition hO hz
  set γ : ℝ → E := fun s => transition F 0 (max s 0) z with hγ
  have hγc : Continuous γ := by
    have h1 : ContinuousOn (fun τ => transition F 0 τ z) (Ici 0) := hlip.continuousOn
    exact h1.comp_continuous (continuous_id.max continuous_const) fun s => le_max_right s 0
  have hint0 := Picard.intervalIntegrable_comp (G := retractedField (chainField F) ρ)
    (lipschitzWith_retractedField hh hρ0 hρ1) (norm_retractedField_le hh hρ0 hρ1)
    (aestronglyMeasurable_retractedField hh hρ0 hρ1) hγc
  have hG : ∀ s, 0 ≤ s → retractedField (chainField F) ρ s (γ s) =
      chainField F s (transition F 0 s z) := by
    intro s hs
    rw [retractedField_of_nonneg hs, hγ]
    simp only [max_eq_left hs]
    rw [radialRetraction_of_norm_le hρ0 ((hnorm s hs).trans (le_max_left _ _))]
  have hint : ∀ τ, 0 ≤ τ →
      IntervalIntegrable (fun s => chainField F s (transition F 0 s z)) volume 0 τ := by
    intro τ hτ
    refine (hint0 0 τ).congr ?_
    rw [uIoc_of_le hτ]
    exact fun s hs => hG s hs.1.le
  refine ⟨hF.transition_mem le_rfl ht hz, hint t ht, ?_⟩
  -- the fundamental theorem of calculus for the absolutely continuous function
  -- `τ ↦ v(z, τ) + ∫₀^τ h(v(z, s), s) ds`
  set g := fun s => chainField F s (transition F 0 s z) with hg
  have hsub : uIcc 0 t ⊆ Ici 0 := by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self
  have hlipI : LipschitzOnWith M.toNNReal (fun τ => ∫ s in (0)..τ, g s) (uIcc 0 t) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have ha0 : 0 ≤ a := hsub ha
    have hb0 : 0 ≤ b := hsub hb
    rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left (hint a ha0) (hint b hb0),
      Real.coe_toNNReal _ hM0]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := M) fun s hs => ?_).trans ?_
    · refine hbd s ?_
      rcases hs with ⟨hs1, -⟩
      exact (le_min hb0 ha0).trans hs1.le
    · rw [Real.dist_eq, abs_sub_comm]
  have hac : AbsolutelyContinuousOnInterval
      (fun τ => transition F 0 τ z + ∫ s in (0)..τ, g s) 0 t :=
    (hlip.mono hsub).absolutelyContinuousOnInterval.add hlipI.absolutelyContinuousOnInterval
  have hder : ∀ᵐ τ, τ ∈ uIcc 0 t →
      HasDerivAt (fun τ => transition F 0 τ z + ∫ s in (0)..τ, g s) 0 τ := by
    have hne : ∀ᵐ τ : ℝ, τ ≠ 0 := by simp [ae_iff, measure_singleton]
    filter_upwards [hF.ae_hasDerivAt_transition hO hloc hz, (hint t ht).ae_hasDerivAt_integral,
      hne] with τ h1 h2 h3 hτ
    have hτ0 : 0 < τ := lt_of_le_of_ne (hsub hτ) (Ne.symm h3)
    have := (h1 hτ0).add (h2 hτ 0 left_mem_uIcc)
    rwa [neg_add_cancel] at this
  obtain ⟨C, hC⟩ := hac.const_of_ae_hasDerivAt_zero hder
  have hC0 := hC 0 left_mem_uIcc
  have hCt := hC t right_mem_uIcc
  rw [intervalIntegral.integral_same, add_zero, hF.transition_self le_rfl hz] at hC0
  rw [← hC0] at hCt
  show transition F 0 t z = z - ∫ s in (0)..t, g s
  rw [eq_sub_iff_add_eq]
  exact hCt

/-- **Normal Loewner chains give parametric representations**: `F_0(z) = lim eᵗ v(z, t)`. -/
theorem isParametricRep_of_chain [CompleteSpace E] {f : E → E} (hf : EqOn (F 0) f (unitBall E)) :
    IsParametricRep f (chainField F) fun t z => transition F 0 t z where
  herglotz := hF.isHerglotzVF_chainField hO hloc
  solution := hF.isLoewnerSolution_transition hO hloc
  tendsto z hz := by
    have hh := hF.isHerglotzVF_chainField hO hloc
    have hv := hF.isLoewnerSolution_transition hO hloc
    obtain ⟨K, hK0, hK⟩ := hF.exists_norm_exp_neg_smul_sub_le hloc
    have hz1 : ‖z‖ < 1 := mem_unitBall.mp hz
    set c := ‖z‖ / (1 - ‖z‖) ^ 2 with hc
    have hc0 : 0 ≤ c := by
      have : 0 < 1 - ‖z‖ := by linarith
      positivity
    have hdecay : ∀ t, 0 ≤ t → ‖transition F 0 t z‖ ≤ Real.exp (-t) * c := fun t ht =>
      hv.norm_le_exp hh hz ht
    -- for large `t`, `‖v(z, t)‖ ≤ 1/2`
    have hsmall : ∀ᶠ t in atTop, Real.exp (-t) * c ≤ 1 / 2 := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.mul_const c)
      rw [zero_mul] at this
      exact this.eventually (eventually_le_nhds (by norm_num))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : Tendsto (fun t : ℝ => K * c ^ 2 * Real.exp (-t)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (K * c ^ 2)
      rwa [mul_zero] at this
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hbound
    filter_upwards [hsmall, eventually_ge_atTop 0] with t hts ht
    set v := transition F 0 t z with hv_def
    have hvs : ‖v‖ ≤ 1 / 2 := (hdecay t ht).trans hts
    have hFv : F t v = f z := by
      rw [hF.apply_transition le_rfl ht hz, hf hz]
    have heq : ((Real.exp t : ℝ) : ℂ) • v - f z =
        -(((Real.exp t : ℝ) : ℂ) • ((Real.exp (-t) : ℂ) • F t v - v)) := by
      rw [hFv, smul_sub, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, Complex.ofReal_one, one_smul]
      abel
    rw [heq, norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have h1 := hK t ht v hvs
    have h2 : ‖v‖ ^ 2 ≤ (Real.exp (-t) * c) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hdecay t ht) 2
    calc Real.exp t * ‖(Real.exp (-t) : ℂ) • F t v - v‖ ≤ Real.exp t * (K * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ ≤ Real.exp t * (K * (Real.exp (-t) * c) ^ 2) := by gcongr
      _ = K * c ^ 2 * (Real.exp t * Real.exp (-t)) * Real.exp (-t) := by ring
      _ = K * c ^ 2 * Real.exp (-t) := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

end IsLoewnerChain

/-- **Normal Loewner chains give parametric representations** (assuming Osgood's theorem):
`S⁰'(𝔹) ⊆ S⁰(𝔹)`. -/
theorem classS0'_subset_classS0_of_osgood [CompleteSpace E] (hO : OsgoodTheorem E) :
    classS0' E ⊆ classS0 E := by
  rintro f ⟨F, hF, hF0, hloc⟩
  exact ⟨_, _, hF.isParametricRep_of_chain hO hloc hF0⟩

end LoewnerS0
