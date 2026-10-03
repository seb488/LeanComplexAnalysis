import LoewnerS0.ChainTransition
import LoewnerS0.Vitali

/-!
# Estimates for normal Loewner chains (assuming Osgood's theorem)

Let `F` be a Loewner chain on `𝔹` such that `{e⁻ᵗ F_t}` is locally uniformly bounded, i.e.
`‖F_t(z)‖ ≤ eᵗ C(r)` for `‖z‖ ≤ r < 1`. By the Cauchy estimates and the bound
`‖z - v(z, s, t)‖ ≤ (t - s) 4r/(1-r)²` for the transition maps, for every `r < 1` there are
constants such that for `0 ≤ s ≤ t` and `‖a‖, ‖b‖, ‖x‖, ‖w‖ ≤ r`:

* `‖DF_t(x)‖ ≤ eᵗ C₁` (`exists_norm_fderiv_le`);
* `‖F_t(w) - F_s(w)‖ ≤ eᵗ K (t - s)` (`exists_norm_sub_le`): `F` is locally Lipschitz in time;
* `‖DF_t(x) - DF_s(x)‖ ≤ eᵗ K (t - s)` (`exists_norm_fderiv_sub_le`);
* `‖F_t(a) - F_t(b) - DF_t(b)(a - b)‖ ≤ eᵗ K ‖a - b‖²` (`exists_norm_sub_sub_fderiv_le`);
* `‖e⁻ᵗ F_t(w) - w‖ ≤ K ‖w‖²` for `‖w‖ ≤ 1/2` (`exists_norm_exp_neg_smul_sub_le`).
-/

open Function Complex Metric Set Filter
open scoped Topology InnerProductSpace NNReal

noncomputable section

namespace LoewnerS0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {F : ℝ → E → E}

omit [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] in
lemma closedBall_subset_closedBall_of_le {x : E} {ρ δ r' : ℝ} (hx : ‖x‖ ≤ ρ) (h : ρ + δ ≤ r') :
    closedBall x δ ⊆ closedBall (0 : E) r' := by
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  rw [mem_closedBall_zero_iff]
  calc ‖w‖ = ‖(w - x) + x‖ := by rw [sub_add_cancel]
    _ ≤ ‖w - x‖ + ‖x‖ := norm_add_le _ _
    _ ≤ r' := by linarith

omit [FiniteDimensional ℂ E] in
lemma exists_bound_of_isLocallyBounded
    (hloc : IsLocallyBounded fun t z => (Real.exp (-t) : ℂ) • F t z) {r : ℝ} (hr : r < 1) :
    ∃ C, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ z : E, ‖z‖ ≤ r → ‖F t z‖ ≤ Real.exp t * C := by
  obtain ⟨C, hC⟩ := hloc r hr
  refine ⟨max C 0, le_max_right _ _, fun t ht z hz => ?_⟩
  have h1 := hC t ht z hz
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  have h2 : ‖F t z‖ = Real.exp t * (Real.exp (-t) * ‖F t z‖) := by
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [h2]
  exact mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) (Real.exp_pos _).le

namespace IsLoewnerChain

variable (hF : IsLoewnerChain F) (hloc : IsLocallyBounded fun t z => (Real.exp (-t) : ℂ) • F t z)
include hF hloc

omit [FiniteDimensional ℂ E] in
/-- `‖DF_t(x)‖ ≤ eᵗ C₁` for `‖x‖ ≤ r`. -/
lemma exists_norm_fderiv_le {r : ℝ} (hr : r < 1) :
    ∃ C₁, 0 ≤ C₁ ∧ ∀ t, 0 ≤ t → ∀ x : E, ‖x‖ ≤ r → ‖fderiv ℂ (F t) x‖ ≤ Real.exp t * C₁ := by
  set ρ := max r 0 with hρ
  have hρ1 : ρ < 1 := max_lt hr one_pos
  have hρ0 : 0 ≤ ρ := le_max_right _ _
  set δ := (1 - ρ) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_isLocallyBounded hloc (r := ρ + δ) (by rw [hδ]; linarith)
  refine ⟨C / δ, div_nonneg hC0 hδ0.le, fun t ht x hx => ?_⟩
  have hxρ : ‖x‖ ≤ ρ := hx.trans (le_max_left _ _)
  have hsub := closedBall_subset_closedBall_of_le (δ := δ) hxρ le_rfl
  have hsubB : closedBall x δ ⊆ unitBall E :=
    hsub.trans (closedBall_subset_ball (by rw [hδ]; linarith))
  have := SCV.norm_fderiv_le_of_forall_mem_closedBall_norm_le hδ0 (hF.differentiableOn t ht)
    isOpen_unitBall hsubB fun w hw => hC t ht w (mem_closedBall_zero_iff.mp (hsub hw))
  rwa [mul_div_assoc] at this

omit hloc in
/-- The derivatives `DF_t` are holomorphic. -/
lemma differentiableOn_fderiv {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableOn ℂ (fderiv ℂ (F t)) (unitBall E) :=
  (((hF.differentiableOn t ht).contDiffOn_of_isOpen isOpen_unitBall 2).fderiv_of_isOpen
    isOpen_unitBall (m := 1) (by norm_num)).differentiableOn (by norm_num)

/-- **`F_t(a) - F_t(b) - DF_t(b)(a - b) = O(eᵗ ‖a - b‖²)`** on `closedBall 0 r`. -/
lemma exists_norm_sub_sub_fderiv_le {r : ℝ} (hr : r < 1) :
    ∃ K, 0 ≤ K ∧ ∀ t, 0 ≤ t → ∀ a b : E, ‖a‖ ≤ r → ‖b‖ ≤ r →
      ‖F t a - F t b - fderiv ℂ (F t) b (a - b)‖ ≤ Real.exp t * K * ‖a - b‖ ^ 2 := by
  set ρ := max r 0 with hρ
  have hρ1 : ρ < 1 := max_lt hr one_pos
  have hρ0 : 0 ≤ ρ := le_max_right _ _
  set δ := (1 - ρ) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := hF.exists_norm_fderiv_le hloc (r := ρ + δ) (by rw [hδ]; linarith)
  refine ⟨C₁ / δ, div_nonneg hC₁0 hδ0.le, fun t ht a b ha hb => ?_⟩
  have haρ : ‖a‖ ≤ ρ := ha.trans (le_max_left _ _)
  have hbρ : ‖b‖ ≤ ρ := hb.trans (le_max_left _ _)
  have hρB : closedBall (0 : E) ρ ⊆ unitBall E := closedBall_subset_ball hρ1
  -- `DF_t` is Lipschitz on `closedBall 0 ρ`
  have hDlip : ∀ x ∈ closedBall (0 : E) ρ,
      ‖fderiv ℂ (F t) x - fderiv ℂ (F t) b‖ ≤ Real.exp t * (C₁ / δ) * ‖x - b‖ := by
    intro x hx
    refine (convex_closedBall (0 : E) ρ).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
      (fun y hy => (hF.differentiableOn_fderiv ht).differentiableAt
        (isOpen_unitBall.mem_nhds (hρB hy))) (fun y hy => ?_) (mem_closedBall_zero_iff.mpr hbρ) hx
    have hsub := closedBall_subset_closedBall_of_le (δ := δ) (mem_closedBall_zero_iff.mp hy) le_rfl
    have hsubB : closedBall y δ ⊆ unitBall E :=
      hsub.trans (closedBall_subset_ball (by rw [hδ]; linarith))
    have := SCV.norm_fderiv_le_of_forall_mem_closedBall_norm_le hδ0
      (hF.differentiableOn_fderiv ht) isOpen_unitBall hsubB
      fun w hw => hC₁ t ht w (mem_closedBall_zero_iff.mp (hsub hw))
    rwa [mul_div_assoc] at this
  -- the mean value inequality on `closedBall 0 ρ ∩ closedBall b ‖a - b‖`
  set S := closedBall (0 : E) ρ ∩ closedBall b ‖a - b‖ with hS
  have hSconv : Convex ℝ S := (convex_closedBall _ _).inter (convex_closedBall _ _)
  have haS : a ∈ S := ⟨mem_closedBall_zero_iff.mpr haρ, by rw [mem_closedBall, dist_eq_norm]⟩
  have hbS : b ∈ S := ⟨mem_closedBall_zero_iff.mpr hbρ, mem_closedBall_self (norm_nonneg _)⟩
  have key := hSconv.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℂ) (f := F t)
    (φ := fderiv ℂ (F t) b) (C := Real.exp t * (C₁ / δ) * ‖a - b‖)
    (fun x hx => (hF.differentiableOn t ht).differentiableAt
      (isOpen_unitBall.mem_nhds (hρB hx.1)))
    (fun x hx => (hDlip x hx.1).trans (mul_le_mul_of_nonneg_left
      (by have := hx.2; rwa [mem_closedBall, dist_eq_norm] at this) (by positivity))) hbS haS
  calc ‖F t a - F t b - fderiv ℂ (F t) b (a - b)‖
      ≤ Real.exp t * (C₁ / δ) * ‖a - b‖ * ‖a - b‖ := key
    _ = Real.exp t * (C₁ / δ) * ‖a - b‖ ^ 2 := by ring

/-- **Normalization**: `‖e⁻ᵗ F_t(w) - w‖ ≤ K ‖w‖²` for `‖w‖ ≤ 1/2`, uniformly in `t`. -/
lemma exists_norm_exp_neg_smul_sub_le :
    ∃ K, 0 ≤ K ∧ ∀ t, 0 ≤ t → ∀ w : E, ‖w‖ ≤ 1 / 2 →
      ‖(Real.exp (-t) : ℂ) • F t w - w‖ ≤ K * ‖w‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := hF.exists_norm_sub_sub_fderiv_le hloc (r := 1 / 2) (by norm_num)
  refine ⟨K, hK0, fun t ht w hw => ?_⟩
  have h1 := hK t ht w 0 hw (by simp)
  rw [hF.map_zero t ht, hF.fderiv_zero t ht] at h1
  simp only [sub_zero, smul_apply, ContinuousLinearMap.id_apply] at h1
  have h2 : (Real.exp (-t) : ℂ) • F t w - w =
      (Real.exp (-t) : ℂ) • (F t w - (Real.exp t : ℂ) • w) := by
    rw [smul_sub, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, Complex.ofReal_one, one_smul]
  rw [h2, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-t) * ‖F t w - (Real.exp t : ℂ) • w‖
      ≤ Real.exp (-t) * (Real.exp t * K * ‖w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = K * ‖w‖ ^ 2 := by
        rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

variable (hO : OsgoodTheorem E)
include hO

/-- **`F` is locally Lipschitz in time**: `‖F_t(w) - F_s(w)‖ ≤ eᵗ K (t - s)` for `‖w‖ ≤ r`. -/
lemma exists_norm_sub_le {r : ℝ} (hr : r < 1) :
    ∃ K, 0 ≤ K ∧ ∀ s t, 0 ≤ s → s ≤ t → ∀ w : E, ‖w‖ ≤ r →
      ‖F t w - F s w‖ ≤ Real.exp t * K * (t - s) := by
  set ρ := max r 0 with hρ
  have hρ1 : ρ < 1 := max_lt hr one_pos
  have hρ0 : 0 ≤ ρ := le_max_right _ _
  obtain ⟨C₁, hC₁0, hC₁⟩ := hF.exists_norm_fderiv_le hloc hρ1
  have hg0 : 0 ≤ 4 * ρ / (1 - ρ) ^ 2 := by
    have : 0 < 1 - ρ := by linarith
    positivity
  refine ⟨C₁ * (4 * ρ / (1 - ρ) ^ 2), mul_nonneg hC₁0 hg0, fun s t hs hst w hw => ?_⟩
  have ht : 0 ≤ t := hs.trans hst
  have hwρ : ‖w‖ ≤ ρ := hw.trans (le_max_left _ _)
  have hwB : w ∈ unitBall E := mem_unitBall.mpr (hwρ.trans_lt hρ1)
  have hv := hF.norm_transition_le hO hs hst hwB
  have hρB : closedBall (0 : E) ρ ⊆ unitBall E := closedBall_subset_ball hρ1
  rw [← hF.apply_transition hs hst hwB]
  have key := (convex_closedBall (0 : E) ρ).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (f := F t) (C := Real.exp t * C₁)
    (fun x hx => (hF.differentiableOn t ht).differentiableAt (isOpen_unitBall.mem_nhds (hρB hx)))
    (fun x hx => hC₁ t ht x (mem_closedBall_zero_iff.mp hx))
    (mem_closedBall_zero_iff.mpr (hv.trans hwρ)) (mem_closedBall_zero_iff.mpr hwρ)
  have h2 := hF.norm_sub_transition_le hO hs hst hρ1 hwρ
  have h3 := (one_sub_exp_sub_le (s := s) (t := t))
  calc ‖F t w - F t (transition F s t w)‖ ≤ Real.exp t * C₁ * ‖w - transition F s t w‖ := key
    _ ≤ Real.exp t * C₁ * ((1 - Real.exp (s - t)) * (4 * ρ / (1 - ρ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ Real.exp t * C₁ * ((t - s) * (4 * ρ / (1 - ρ) ^ 2)) := by
        gcongr
    _ = Real.exp t * (C₁ * (4 * ρ / (1 - ρ) ^ 2)) * (t - s) := by ring

/-- `‖DF_t(x) - DF_s(x)‖ ≤ eᵗ K (t - s)` for `‖x‖ ≤ r`. -/
lemma exists_norm_fderiv_sub_le {r : ℝ} (hr : r < 1) :
    ∃ K, 0 ≤ K ∧ ∀ s t, 0 ≤ s → s ≤ t → ∀ x : E, ‖x‖ ≤ r →
      ‖fderiv ℂ (F t) x - fderiv ℂ (F s) x‖ ≤ Real.exp t * K * (t - s) := by
  set ρ := max r 0 with hρ
  have hρ1 : ρ < 1 := max_lt hr one_pos
  have hρ0 : 0 ≤ ρ := le_max_right _ _
  set δ := (1 - ρ) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨K, hK0, hK⟩ := hF.exists_norm_sub_le hloc hO (r := ρ + δ) (by rw [hδ]; linarith)
  refine ⟨K / δ, div_nonneg hK0 hδ0.le, fun s t hs hst x hx => ?_⟩
  have ht : 0 ≤ t := hs.trans hst
  have hxρ : ‖x‖ ≤ ρ := hx.trans (le_max_left _ _)
  have hsub := closedBall_subset_closedBall_of_le (δ := δ) hxρ le_rfl
  have hsubB : closedBall x δ ⊆ unitBall E :=
    hsub.trans (closedBall_subset_ball (by rw [hδ]; linarith))
  have hxB : x ∈ unitBall E := hsubB (mem_closedBall_self hδ0.le)
  have hd := (hF.differentiableOn t ht).sub (hF.differentiableOn s hs)
  have := SCV.norm_fderiv_le_of_forall_mem_closedBall_norm_le hδ0 hd isOpen_unitBall hsubB
    fun w hw => hK s t hs hst w (mem_closedBall_zero_iff.mp (hsub hw))
  rw [fderiv_sub ((hF.differentiableOn t ht).differentiableAt (isOpen_unitBall.mem_nhds hxB))
    ((hF.differentiableOn s hs).differentiableAt (isOpen_unitBall.mem_nhds hxB))] at this
  calc ‖fderiv ℂ (F t) x - fderiv ℂ (F s) x‖ ≤ Real.exp t * K * (t - s) / δ := this
    _ = Real.exp t * (K / δ) * (t - s) := by ring

/-- `t ↦ F_t(w)` is Lipschitz on `[0, T]`. -/
lemma exists_lipschitzOnWith {r : ℝ} (hr : r < 1) :
    ∃ K, 0 ≤ K ∧ ∀ T, ∀ w : E, ‖w‖ ≤ r →
      LipschitzOnWith (Real.exp T * K).toNNReal (fun t => F t w) (Icc 0 T) := by
  obtain ⟨K, hK0, hK⟩ := hF.exists_norm_sub_le hloc hO hr
  refine ⟨K, hK0, fun T w hw => LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_⟩
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, Real.dist_eq]
  rcases le_total s t with hst | hts
  · rw [norm_sub_rev, abs_of_nonpos (by linarith)]
    calc ‖F t w - F s w‖ ≤ Real.exp t * K * (t - s) := hK s t hs.1 hst w hw
      _ ≤ Real.exp T * K * (t - s) := by
          gcongr
          exact ht.2
      _ = Real.exp T * K * -(s - t) := by ring
  · rw [abs_of_nonneg (by linarith)]
    calc ‖F s w - F t w‖ ≤ Real.exp s * K * (s - t) := hK t s ht.1 hts w hw
      _ ≤ Real.exp T * K * (s - t) := by
          gcongr
          exact hs.2

/-- `t ↦ F_t(w)` is continuous on `[0, ∞)`. -/
lemma continuousOn_apply {w : E} (hw : w ∈ unitBall E) : ContinuousOn (fun t => F t w) (Ici 0) := by
  obtain ⟨K, -, hK⟩ := hF.exists_lipschitzOnWith hloc hO (mem_unitBall.mp hw)
  intro t ht
  have h1 := (hK (t + 1) w le_rfl).continuousOn t ⟨ht, by linarith⟩
  refine h1.mono_of_mem_nhdsWithin ?_
  rw [mem_nhdsWithin]
  refine ⟨Iio (t + 1), isOpen_Iio, by simp, fun τ hτ => ⟨hτ.2, hτ.1.le⟩⟩

/-- `t ↦ DF_t(x)` is continuous on `[0, ∞)`. -/
lemma continuousOn_fderiv {x : E} (hx : x ∈ unitBall E) :
    ContinuousOn (fun t => fderiv ℂ (F t) x) (Ici 0) := by
  obtain ⟨K, hK0, hK⟩ := hF.exists_norm_fderiv_sub_le hloc hO (mem_unitBall.mp hx)
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro η hη
  have hM : 0 < Real.exp (t + 1) * K + 1 := by positivity
  refine ⟨min 1 (η / (Real.exp (t + 1) * K + 1)), lt_min one_pos (div_pos hη hM),
    fun τ hτ hdist => ?_⟩
  rw [Real.dist_eq] at hdist
  have hd1 : |τ - t| < 1 := hdist.trans_le (min_le_left _ _)
  have hd2 : |τ - t| < η / (Real.exp (t + 1) * K + 1) := hdist.trans_le (min_le_right _ _)
  have hτ1 : τ ≤ t + 1 := by have := (abs_lt.mp hd1).2; linarith
  have hb : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t + 1 →
      ‖fderiv ℂ (F b) x - fderiv ℂ (F a) x‖ ≤ (Real.exp (t + 1) * K) * (b - a) := by
    intro a b ha hab hb1
    refine (hK a b ha hab x le_rfl).trans ?_
    gcongr
  rw [dist_eq_norm]
  have hkey : ‖fderiv ℂ (F τ) x - fderiv ℂ (F t) x‖ ≤ (Real.exp (t + 1) * K) * |τ - t| := by
    rcases le_total t τ with htτ | hτt
    · rw [abs_of_nonneg (by linarith)]
      exact hb t τ ht htτ hτ1
    · rw [abs_of_nonpos (by linarith), norm_sub_rev, neg_sub]
      exact hb τ t hτ hτt (by linarith)
  calc ‖fderiv ℂ (F τ) x - fderiv ℂ (F t) x‖ ≤ (Real.exp (t + 1) * K) * |τ - t| := hkey
    _ ≤ (Real.exp (t + 1) * K + 1) * |τ - t| := by
        gcongr; linarith
    _ < (Real.exp (t + 1) * K + 1) * (η / (Real.exp (t + 1) * K + 1)) := by
        gcongr
    _ = η := by field_simp

end IsLoewnerChain

end LoewnerS0
