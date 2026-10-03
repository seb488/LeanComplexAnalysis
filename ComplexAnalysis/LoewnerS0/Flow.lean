import LoewnerS0.SCV
import LoewnerS0.Starlike
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The flow of `ż = -h(z)` for `h ∈ M(𝔹)`

Let `E` be a finite-dimensional complex inner product space and `h ∈ M(𝔹)`. Since
`Re ⟨h(z), z⟩ ≥ 0`, the norm of a solution of `ż = -h(z)` does not increase, so solutions starting
in `𝔹` exist for all `t ≥ 0` and stay in `𝔹`. This file constructs this flow
`LoewnerS0.flow hh t z` and proves its basic properties: initial value, derivative, `‖φ_t(z)‖ ≤ ‖z‖`,
uniqueness, the semigroup law, injectivity, `φ_t(0) = 0`, and the decay estimates used to show that
`e^t φ_t` converges.

Global existence is obtained from mathlib's Picard–Lindelöf theorem applied to the globally
Lipschitz field `-h(π(w))`, where `π` is the radial retraction onto a closed ball of radius `< 1`.
-/

open Complex Metric Set Filter
open scoped Topology InnerProductSpace NNReal

noncomputable section

namespace LoewnerS0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {h : E → E}

/-! ### Estimates for `h ∈ M(𝔹)` on closed balls -/

section Estimates

omit [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] in
lemma closedBall_subset_unitBall {ρ : ℝ} (hρ : ρ < 1) : closedBall (0 : E) ρ ⊆ unitBall E :=
  closedBall_subset_ball hρ

omit [FiniteDimensional ℂ E] in
lemma IsCaratheodory.re_inner_nonneg (hh : IsCaratheodory h) {z : E} (hz : z ∈ unitBall E) :
    0 ≤ (⟪z, h z⟫_ℂ).re := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  · exact (hh.re_inner_pos z hz hz0).le

lemma IsCaratheodory.contDiffOn (hh : IsCaratheodory h) (n : ℕ) :
    ContDiffOn ℂ n h (unitBall E) :=
  hh.isNormalized.differentiableOn.contDiffOn_of_isOpen isOpen_unitBall n

/-- `h` is Lipschitz on closed balls of radius `< 1`. -/
lemma IsCaratheodory.exists_lipschitzOnWith (hh : IsCaratheodory h) {ρ : ℝ} (hρ : ρ < 1) :
    ∃ L : ℝ≥0, LipschitzOnWith L h (closedBall 0 ρ) := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have hcont : ContinuousOn (fderiv ℂ h) (closedBall 0 ρ) :=
    ((hh.contDiffOn 1).continuousOn_fderiv_of_isOpen isOpen_unitBall le_rfl).mono
      (closedBall_subset_unitBall hρ)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) ρ).exists_bound_of_continuousOn hcont
  refine ⟨C.toNNReal, ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℂ)
  · intro x hx
    exact hh.isNormalized.differentiableAt (closedBall_subset_unitBall hρ hx)
  · intro x hx
    rw [← norm_toNNReal]
    exact Real.toNNReal_le_toNNReal (hC x hx)
  · exact convex_closedBall 0 ρ

/-- `h` is bounded on closed balls of radius `< 1`. -/
lemma IsCaratheodory.exists_norm_le (hh : IsCaratheodory h) {ρ : ℝ} (hρ : ρ < 1) :
    ∃ M, 0 ≤ M ∧ ∀ w ∈ closedBall (0 : E) ρ, ‖h w‖ ≤ M := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) ρ).exists_bound_of_continuousOn
    (hh.isNormalized.differentiableOn.continuousOn.mono (closedBall_subset_unitBall hρ))
  exact ⟨max C 0, le_max_right _ _, fun w hw => (hC w hw).trans (le_max_left _ _)⟩

/-- `h(w) = w + O(‖w‖²)` near `0`. -/
lemma IsCaratheodory.exists_norm_sub_le_sq (hh : IsCaratheodory h) :
    ∃ δ₀ > 0, δ₀ < 1 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ w : E, ‖w‖ ≤ δ₀ → ‖h w - w‖ ≤ K * ‖w‖ ^ 2 := by
  have hD : ContDiffAt ℂ 1 (fderiv ℂ h) 0 :=
    ((hh.contDiffOn 2).contDiffAt (unitBall_mem_nhds zero_mem_unitBall)).fderiv_right
      (m := 1) (by norm_num)
  obtain ⟨K, t, ht, hlip⟩ := hD.exists_lipschitzOnWith
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.mp ht
  set δ₀ := min (ε / 2) (1 / 2) with hδ₀_def
  have hδ₀ : 0 < δ₀ := by positivity
  have hδ₀ε : δ₀ ≤ ε / 2 := min_le_left _ _
  have hδ₀1 : δ₀ ≤ 1 / 2 := min_le_right _ _
  have hsub : closedBall (0 : E) δ₀ ⊆ t := fun x hx => hεt (by
    rw [mem_ball]; rw [mem_closedBall] at hx; linarith)
  have hsubB : closedBall (0 : E) δ₀ ⊆ unitBall E := closedBall_subset_unitBall (by linarith)
  refine ⟨δ₀, hδ₀, by linarith, K, K.2, fun w hw => ?_⟩
  have hw' : closedBall (0 : E) ‖w‖ ⊆ closedBall 0 δ₀ := closedBall_subset_closedBall hw
  have hl : ∀ x ∈ closedBall (0 : E) ‖w‖,
      ‖fderiv ℂ h x - ContinuousLinearMap.id ℂ E‖ ≤ K * ‖w‖ := by
    intro x hx
    rw [← hh.isNormalized.fderiv_zero, ← dist_eq_norm]
    have := hlip.dist_le_mul x (hsub (hw' hx)) 0 (hsub (mem_closedBall_self hδ₀.le))
    refine this.trans (mul_le_mul_of_nonneg_left ?_ K.2)
    simpa using hx
  have := (convex_closedBall (0 : E) ‖w‖).norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℂ)
    (fun x hx => hh.isNormalized.differentiableAt (hsubB (hw' hx))) hl
    (mem_closedBall_self (norm_nonneg _)) (show w ∈ closedBall (0 : E) ‖w‖ by simp)
  simpa [hh.map_zero, pow_two, mul_assoc] using this

/-- A positive lower bound for `Re ⟨w, h w⟩` on closed annuli. -/
lemma IsCaratheodory.exists_re_inner_ge (hh : IsCaratheodory h) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁)
    (hr₂ : r₂ < 1) : ∃ m > 0, ∀ w : E, r₁ ≤ ‖w‖ → ‖w‖ ≤ r₂ → m ≤ (⟪w, h w⟫_ℂ).re := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  set A := closedBall (0 : E) r₂ ∩ {w | r₁ ≤ ‖w‖} with hA_def
  have hA : IsCompact A :=
    (isCompact_closedBall 0 r₂).inter_right (isClosed_le continuous_const continuous_norm)
  have hAB : A ⊆ unitBall E := fun w hw => closedBall_subset_unitBall hr₂ hw.1
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · refine ⟨1, one_pos, fun w hw1 hw2 => ?_⟩
    have : w ∈ A := ⟨by simpa using hw2, hw1⟩
    rw [hAe] at this
    exact absurd this (notMem_empty w)
  · have hcont : ContinuousOn (fun w => (⟪w, h w⟫_ℂ).re) A :=
      Complex.continuous_re.comp_continuousOn
        (continuousOn_id.inner (hh.isNormalized.differentiableOn.continuousOn.mono hAB))
    obtain ⟨w₀, hw₀, hmin⟩ := hA.exists_isMinOn hAne hcont
    refine ⟨(⟪w₀, h w₀⟫_ℂ).re, ?_, fun w hw1 hw2 => hmin ⟨by simpa using hw2, hw1⟩⟩
    have hw₀0 : w₀ ≠ 0 := by
      intro h0
      have h1 : r₁ ≤ ‖w₀‖ := hw₀.2
      rw [h0, norm_zero] at h1
      linarith
    exact hh.re_inner_pos w₀ (hAB hw₀) hw₀0

end Estimates

/-! ### The radial retraction -/

section Retraction

/-- The radial retraction of `E` onto `closedBall 0 ρ`. -/
def radialRetraction (ρ : ℝ) (w : E) : E := (ρ / max ρ ‖w‖) • w

omit [FiniteDimensional ℂ E] in
lemma norm_radialRetraction_le {ρ : ℝ} (hρ : 0 < ρ) (w : E) : ‖radialRetraction ρ w‖ ≤ ρ := by
  have hm : 0 < max ρ ‖w‖ := lt_max_of_lt_left hρ
  rw [radialRetraction, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_mul_eq_mul_div,
    div_le_iff₀ hm]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hρ.le

omit [FiniteDimensional ℂ E] in
lemma radialRetraction_of_norm_le {ρ : ℝ} (hρ : 0 < ρ) {w : E} (hw : ‖w‖ ≤ ρ) :
    radialRetraction ρ w = w := by
  rw [radialRetraction, max_eq_left hw, div_self hρ.ne', one_smul]

omit [FiniteDimensional ℂ E] in
lemma dist_radialRetraction_le {ρ : ℝ} (hρ : 0 < ρ) (w₁ w₂ : E) :
    dist (radialRetraction ρ w₁) (radialRetraction ρ w₂) ≤ 2 * dist w₁ w₂ := by
  set m₁ := max ρ ‖w₁‖ with hm₁
  set m₂ := max ρ ‖w₂‖ with hm₂
  have hm₁0 : 0 < m₁ := lt_max_of_lt_left hρ
  have hm₂0 : 0 < m₂ := lt_max_of_lt_left hρ
  have hρm₁ : ρ ≤ m₁ := le_max_left _ _
  have hwm₂ : ‖w₂‖ ≤ m₂ := le_max_right _ _
  have hdiff : |m₁ - m₂| ≤ ‖w₁ - w₂‖ := by
    have := abs_max_sub_max_le_abs ‖w₁‖ ‖w₂‖ ρ
    rw [max_comm ‖w₁‖, max_comm ‖w₂‖] at this
    exact this.trans (abs_norm_sub_norm_le w₁ w₂)
  have e : radialRetraction ρ w₁ - radialRetraction ρ w₂ =
      (ρ / m₁) • (w₁ - w₂) + (ρ / m₁ - ρ / m₂) • w₂ := by
    rw [radialRetraction, radialRetraction, smul_sub, sub_smul]; abel
  have h1 : ‖(ρ / m₁) • (w₁ - w₂)‖ ≤ ‖w₁ - w₂‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one hm₁0).mpr hρm₁)
  have h2 : ‖(ρ / m₁ - ρ / m₂) • w₂‖ ≤ ‖w₁ - w₂‖ := by
    rw [norm_smul, Real.norm_eq_abs, div_sub_div _ _ hm₁0.ne' hm₂0.ne', abs_div,
      abs_of_pos (mul_pos hm₁0 hm₂0)]
    have e2 : |ρ * m₂ - m₁ * ρ| = ρ * |m₁ - m₂| := by
      rw [show ρ * m₂ - m₁ * ρ = -(ρ * (m₁ - m₂)) by ring, abs_neg, abs_mul, abs_of_pos hρ]
    rw [e2, div_mul_eq_mul_div, div_le_iff₀ (mul_pos hm₁0 hm₂0)]
    calc ρ * |m₁ - m₂| * ‖w₂‖ = |m₁ - m₂| * (ρ * ‖w₂‖) := by ring
      _ ≤ ‖w₁ - w₂‖ * (m₁ * m₂) :=
          mul_le_mul hdiff (mul_le_mul hρm₁ hwm₂ (norm_nonneg _) hm₁0.le)
            (by positivity) (norm_nonneg _)
  rw [dist_eq_norm, dist_eq_norm, e, two_mul]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

omit [FiniteDimensional ℂ E] in
lemma lipschitzWith_radialRetraction {ρ : ℝ} (hρ : 0 < ρ) :
    LipschitzWith 2 (radialRetraction (E := E) ρ) :=
  LipschitzWith.of_dist_le_mul fun w₁ w₂ => by
    simpa using dist_radialRetraction_le hρ w₁ w₂

omit [FiniteDimensional ℂ E] in
/-- The modified field `-h(π(w))` still points weakly inwards. -/
lemma IsCaratheodory.re_inner_radialRetraction_nonneg (hh : IsCaratheodory h) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (w : E) : 0 ≤ (⟪w, h (radialRetraction ρ w)⟫_ℂ).re := by
  set c : ℝ := ρ / max ρ ‖w‖ with hc
  have hc0 : 0 < c := div_pos hρ (lt_max_of_lt_left hρ)
  have hmem : radialRetraction ρ w ∈ unitBall E :=
    mem_unitBall.mpr (lt_of_le_of_lt (norm_radialRetraction_le hρ w) hρ1)
  have h1 := hh.re_inner_nonneg hmem
  have e : radialRetraction ρ w = (c : ℂ) • w := by
    rw [radialRetraction, ← hc]; exact (Complex.coe_smul c w).symm
  rw [e, inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul] at h1
  rw [e]
  exact (mul_nonneg_iff_of_pos_left hc0).mp h1

end Retraction

/-! ### Global solutions -/

section Existence

omit [FiniteDimensional ℂ E] in
/-- The derivative of `t ↦ ‖α t‖²`. -/
lemma hasDerivWithinAt_norm_sq {α : ℝ → E} {α' : E} {s : Set ℝ} {t : ℝ}
    (hα : HasDerivWithinAt α α' s t) :
    HasDerivWithinAt (fun τ => ‖α τ‖ ^ 2) (2 * (⟪α t, α'⟫_ℂ).re) s t := by
  have h1 := hα.inner ℂ hα
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t h1
  have e1 : (fun τ => ‖α τ‖ ^ 2) = (Complex.reCLM ∘ fun τ => ⟪α τ, α τ⟫_ℂ) := by
    funext τ
    simp only [Function.comp_apply, Complex.reCLM_apply]
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    rfl
  rw [e1]
  convert h2 using 1
  simp only [Complex.reCLM_apply, Complex.add_re]
  rw [re_inner_comm α' (α t)]
  ring

omit [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] in
lemma lipschitzOnWith_neg {f : E → E} {L : ℝ≥0} {s : Set E} (hf : LipschitzOnWith L f s) :
    LipschitzOnWith L (fun w => -f w) s :=
  LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
    simpa [dist_neg_neg] using hf.dist_le_mul x hx y hy

/-- The modified field `-h(π_ρ(w))` is globally Lipschitz and bounded. -/
lemma IsCaratheodory.exists_modified_field (hh : IsCaratheodory h) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ < 1) : ∃ K : ℝ≥0, ∃ M : ℝ≥0,
      LipschitzWith K (fun w : E => -h (radialRetraction ρ w)) ∧
        ∀ w : E, ‖-h (radialRetraction ρ w)‖ ≤ M := by
  obtain ⟨L, hL⟩ := hh.exists_lipschitzOnWith hρ1
  obtain ⟨M, hM0, hM⟩ := hh.exists_norm_le hρ1
  have hmem : ∀ w : E, radialRetraction ρ w ∈ closedBall (0 : E) ρ := fun w =>
    mem_closedBall_zero_iff.mpr (norm_radialRetraction_le hρ w)
  refine ⟨2 * L, ⟨M, hM0⟩, LipschitzWith.of_dist_le_mul fun w₁ w₂ => ?_, fun w => ?_⟩
  · rw [dist_neg_neg]
    calc dist (h (radialRetraction ρ w₁)) (h (radialRetraction ρ w₂))
        ≤ L * dist (radialRetraction ρ w₁) (radialRetraction ρ w₂) :=
          hL.dist_le_mul _ (hmem w₁) _ (hmem w₂)
      _ ≤ L * (2 * dist w₁ w₂) :=
          mul_le_mul_of_nonneg_left (dist_radialRetraction_le hρ w₁ w₂) L.2
      _ = ((2 * L : ℝ≥0) : ℝ) * dist w₁ w₂ := by push_cast; ring
  · rw [norm_neg]
    exact hM _ (hmem w)

/-- Solutions of the modified equation on `[0, T]`. -/
lemma IsCaratheodory.exists_sol_Icc (hh : IsCaratheodory h) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {z : E} (hz : ‖z‖ ≤ ρ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ α : ℝ → E, α 0 = z ∧ ∀ t ∈ Icc 0 T,
      HasDerivWithinAt α (-h (radialRetraction ρ (α t))) (Icc 0 T) t := by
  obtain ⟨K, M, hK, hM⟩ := hh.exists_modified_field hρ hρ1
  have hPL : IsPicardLindelof (fun _ (w : E) => -h (radialRetraction ρ w)) (tmin := 0) (tmax := T)
      ⟨0, ⟨le_rfl, hT⟩⟩ (0 : E) ⟨ρ + M * T, by positivity⟩ ⟨ρ, hρ.le⟩ M K := by
    refine ⟨fun t _ => hK.lipschitzOnWith, fun x _ => continuousOn_const,
      fun t _ x _ => hM x, ?_⟩
    change (M : ℝ) * max (T - 0) (0 - 0) ≤ (ρ + M * T) - ρ
    rw [sub_zero, sub_self, max_eq_left hT]
    linarith
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt (x := z)
    (by rw [mem_closedBall_zero_iff]; exact hz)
  exact ⟨α, hα0, hα⟩

omit [FiniteDimensional ℂ E] in
/-- Solutions of the modified equation do not move away from `0`. -/
lemma IsCaratheodory.norm_sol_le (hh : IsCaratheodory h) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {T : ℝ} {α : ℝ → E}
    (hα : ∀ t ∈ Icc 0 T, HasDerivWithinAt α (-h (radialRetraction ρ (α t))) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, ‖α t‖ ≤ ‖α 0‖ := by
  have hN : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun τ => ‖α τ‖ ^ 2)
      (2 * (⟪α t, -h (radialRetraction ρ (α t))⟫_ℂ).re) (Icc 0 T) t :=
    fun t ht => hasDerivWithinAt_norm_sq (hα t ht)
  have hanti : AntitoneOn (fun τ => ‖α τ‖ ^ 2) (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      (fun t ht => (hN t ht).continuousWithinAt)
      (fun t ht => (hN t (interior_subset ht)).mono interior_subset)
    intro t _
    rw [inner_neg_right, Complex.neg_re]
    have := hh.re_inner_radialRetraction_nonneg hρ hρ1 (α t)
    linarith
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have := hanti h0 ht ht.1
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.mp this

/-- **Global existence**: a solution of `ż = -h(z)` on `[0, ∞)` starting at `z ∈ 𝔹`. -/
theorem IsCaratheodory.exists_flow_curve (hh : IsCaratheodory h) {z : E} (hz : z ∈ unitBall E) :
    ∃ α : ℝ → E, α 0 = z ∧ (∀ t, 0 ≤ t → ‖α t‖ ≤ ‖z‖) ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt α (-h (α t)) (Ici t) t) ∧
      (∀ t, 0 < t → HasDerivAt α (-h (α t)) t) := by
  set ρ := (1 + ‖z‖) / 2 with hρ_def
  have hz1 : ‖z‖ < 1 := mem_unitBall.mp hz
  have hρ : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by linarith
  have hzρ : ‖z‖ ≤ ρ := by linarith
  obtain ⟨K, M, hK, -⟩ := hh.exists_modified_field hρ hρ1
  have hex : ∀ n : ℕ, ∃ α : ℝ → E, α 0 = z ∧ ∀ t ∈ Icc (0 : ℝ) n,
      HasDerivWithinAt α (-h (radialRetraction ρ (α t))) (Icc 0 n) t :=
    fun n => hh.exists_sol_Icc hρ hρ1 hzρ n.cast_nonneg
  choose α hα0 hα using hex
  have hnorm : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) n, ‖α n t‖ ≤ ‖z‖ := fun n t ht => by
    simpa [hα0 n] using hh.norm_sol_le hρ hρ1 (hα n) t ht
  have hret : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) n, radialRetraction ρ (α n t) = α n t :=
    fun n t ht => radialRetraction_of_norm_le hρ ((hnorm n t ht).trans hzρ)
  -- right derivatives
  have hright : ∀ n : ℕ, ∀ t ∈ Ico (0 : ℝ) n,
      HasDerivWithinAt (α n) (-h (radialRetraction ρ (α n t))) (Ici t) t := fun n t ht =>
    (hα n t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have hcont : ∀ n : ℕ, ContinuousOn (α n) (Icc 0 n) := fun n t ht =>
    (hα n t ht).continuousWithinAt
  -- consistency
  have hcons : ∀ m n : ℕ, m ≤ n → EqOn (α m) (α n) (Icc 0 m) := by
    intro m n hmn
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    apply ODE_solution_unique (v := fun _ (w : E) => -h (radialRetraction ρ w)) (K := K)
      (fun _ => hK) (hcont m) (hright m) ((hcont n).mono (Icc_subset_Icc_right hmn'))
      (fun t ht => hright n t ⟨ht.1, lt_of_lt_of_le ht.2 hmn'⟩)
    rw [hα0, hα0]
  -- the glued solution
  set β : ℝ → E := fun t => α ⌈t⌉₊ t with hβ_def
  have hβ : ∀ n : ℕ, EqOn β (α n) (Icc 0 n) := by
    intro n t ht
    have h1 : ⌈t⌉₊ ≤ n := Nat.ceil_le.mpr ht.2
    exact hcons ⌈t⌉₊ n h1 ⟨ht.1, Nat.le_ceil t⟩
  have hβder : ∀ t, 0 ≤ t → HasDerivWithinAt β (-h (β t)) (Icc 0 (⌈t⌉₊ + 1 : ℕ)) t := by
    intro t ht
    set n := ⌈t⌉₊ + 1 with hn
    have htn : t < n := by
      rw [hn]; push_cast; exact lt_of_le_of_lt (Nat.le_ceil t) (lt_add_one _)
    have htI : t ∈ Icc (0 : ℝ) n := ⟨ht, htn.le⟩
    have := (hα n t htI).congr_of_mem (hβ n) htI
    rwa [hret n t htI, ← hβ n htI] at this
  refine ⟨β, ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · simp [hβ_def, hα0]
  · have htI : t ∈ Icc (0 : ℝ) (⌈t⌉₊) := ⟨ht, Nat.le_ceil t⟩
    rw [hβ _ htI]
    exact hnorm _ t htI
  · have htn : t < ((⌈t⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact lt_of_le_of_lt (Nat.le_ceil t) (lt_add_one _)
    exact (hβder t ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ⟨ht, htn⟩)
  · have htn : t < ((⌈t⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact lt_of_le_of_lt (Nat.le_ceil t) (lt_add_one _)
    exact (hβder t ht.le).hasDerivAt (Icc_mem_nhds ht htn)

end Existence

/-! ### The flow -/

section FlowDef

open Classical in
/-- The flow `φ_t(z)` of `ż = -h(z)`, for `z ∈ 𝔹` and `t ≥ 0` (it is defined as `z` for
`z ∉ 𝔹`). -/
def flow (hh : IsCaratheodory h) (t : ℝ) (z : E) : E :=
  if hz : z ∈ unitBall E then Classical.choose (hh.exists_flow_curve hz) t else z

variable (hh : IsCaratheodory h)

lemma flow_spec {z : E} (hz : z ∈ unitBall E) :
    flow hh 0 z = z ∧ (∀ t, 0 ≤ t → ‖flow hh t z‖ ≤ ‖z‖) ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt (fun τ => flow hh τ z) (-h (flow hh t z)) (Ici t) t) ∧
      (∀ t, 0 < t → HasDerivAt (fun τ => flow hh τ z) (-h (flow hh t z)) t) := by
  simp only [flow, hz, ↓reduceDIte]
  exact Classical.choose_spec (hh.exists_flow_curve hz)

lemma flow_zero {z : E} (hz : z ∈ unitBall E) : flow hh 0 z = z := (flow_spec hh hz).1

lemma norm_flow_le {z : E} (hz : z ∈ unitBall E) {t : ℝ} (ht : 0 ≤ t) :
    ‖flow hh t z‖ ≤ ‖z‖ :=
  (flow_spec hh hz).2.1 t ht

lemma flow_mem {z : E} (hz : z ∈ unitBall E) {t : ℝ} (ht : 0 ≤ t) : flow hh t z ∈ unitBall E :=
  mem_unitBall.mpr ((norm_flow_le hh hz ht).trans_lt (mem_unitBall.mp hz))

lemma hasDerivWithinAt_flow {z : E} (hz : z ∈ unitBall E) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun τ => flow hh τ z) (-h (flow hh t z)) (Ici t) t :=
  (flow_spec hh hz).2.2.1 t ht

lemma hasDerivAt_flow {z : E} (hz : z ∈ unitBall E) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun τ => flow hh τ z) (-h (flow hh t z)) t :=
  (flow_spec hh hz).2.2.2 t ht

lemma continuousOn_flow {z : E} (hz : z ∈ unitBall E) :
    ContinuousOn (fun τ => flow hh τ z) (Ici 0) := by
  intro t ht
  rcases (mem_Ici.mp ht).eq_or_lt with h0 | hpos
  · subst h0
    exact (hasDerivWithinAt_flow hh hz le_rfl).continuousWithinAt
  · exact (hasDerivAt_flow hh hz hpos).continuousAt.continuousWithinAt

/-- **Uniqueness**: a solution of `ż = -h(z)` on `[0, T]` that stays in a closed ball of radius
`< 1` coincides with the flow. -/
lemma eqOn_flow {ρ : ℝ} (hρ1 : ρ < 1) {T : ℝ} {β : ℝ → E} (hβc : ContinuousOn β (Icc 0 T))
    (hβ : ∀ t ∈ Ico 0 T, HasDerivWithinAt β (-h (β t)) (Ici t) t)
    (hβs : ∀ t ∈ Ico 0 T, β t ∈ closedBall (0 : E) ρ) (hβ0 : β 0 ∈ unitBall E) :
    EqOn β (fun t => flow hh t (β 0)) (Icc 0 T) := by
  have hρ'1 : max ρ ‖β 0‖ < 1 := max_lt hρ1 (mem_unitBall.mp hβ0)
  obtain ⟨L, hL⟩ := hh.exists_lipschitzOnWith hρ'1
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ w => -h w)
    (s := fun _ => closedBall (0 : E) (max ρ ‖β 0‖)) (K := L)
    (fun _ _ => lipschitzOnWith_neg hL) hβc hβ
    (fun t ht => closedBall_subset_closedBall (le_max_left _ _) (hβs t ht))
    ((continuousOn_flow hh hβ0).mono Icc_subset_Ici_self)
    (fun t ht => hasDerivWithinAt_flow hh hβ0 ht.1)
    (fun t ht => mem_closedBall_zero_iff.mpr
      ((norm_flow_le hh hβ0 ht.1).trans (le_max_right _ _)))
    (flow_zero hh hβ0).symm

/-- The **semigroup law** `φ_{s+t} = φ_t ∘ φ_s`. -/
lemma flow_add {z : E} (hz : z ∈ unitBall E) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    flow hh (s + t) z = flow hh t (flow hh s z) := by
  have hmem : flow hh s z ∈ unitBall E := flow_mem hh hz hs
  have key := eqOn_flow hh (ρ := ‖z‖) (mem_unitBall.mp hz) (T := t)
    (β := fun τ => flow hh (s + τ) z) ?_ ?_ ?_ (by simpa using hmem)
  · have h2 := key ⟨ht, le_rfl⟩
    simpa using h2
  · exact (continuousOn_flow hh hz).comp (continuous_const_add s).continuousOn
      (fun τ hτ => by simp only [mem_Ici, mem_Icc] at hτ ⊢; linarith)
  · intro τ hτ
    have h1 := hasDerivWithinAt_flow hh hz (add_nonneg hs hτ.1)
    have h2 : HasDerivWithinAt (fun σ : ℝ => s + σ) 1 (Ici τ) τ :=
      ((hasDerivAt_id τ).const_add s).hasDerivWithinAt
    have h3 := HasDerivWithinAt.scomp (x := τ) h1 h2
      (fun σ hσ => by simp only [mem_Ici] at hσ ⊢; linarith)
    simpa [Function.comp_def] using h3
  · intro τ hτ
    exact mem_closedBall_zero_iff.mpr (norm_flow_le hh hz (add_nonneg hs hτ.1))

/-- `‖φ_t(z)‖` is non-increasing in `t`. -/
lemma norm_flow_antitone {z : E} (hz : z ∈ unitBall E) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖flow hh t z‖ ≤ ‖flow hh s z‖ := by
  have e : flow hh t z = flow hh (t - s) (flow hh s z) := by
    rw [← flow_add hh hz hs (sub_nonneg.mpr hst), add_sub_cancel]
  rw [e]
  exact norm_flow_le hh (flow_mem hh hz hs) (sub_nonneg.mpr hst)

/-- Each `φ_t` is **injective** on `𝔹`. -/
lemma flow_injective {z₁ z₂ : E} (hz₁ : z₁ ∈ unitBall E) (hz₂ : z₂ ∈ unitBall E) {t : ℝ}
    (ht : 0 ≤ t) (heq : flow hh t z₁ = flow hh t z₂) : z₁ = z₂ := by
  have hρ1 : max ‖z₁‖ ‖z₂‖ < 1 := max_lt (mem_unitBall.mp hz₁) (mem_unitBall.mp hz₂)
  obtain ⟨L, hL⟩ := hh.exists_lipschitzOnWith hρ1
  rcases ht.eq_or_lt with h0 | htpos
  · subst h0
    rwa [flow_zero hh hz₁, flow_zero hh hz₂] at heq
  have key := ODE_solution_unique_of_mem_Icc_left (v := fun _ w => -h w)
    (s := fun _ => closedBall (0 : E) (max ‖z₁‖ ‖z₂‖)) (K := L) (a := 0) (b := t)
    (f := fun τ => flow hh τ z₁) (g := fun τ => flow hh τ z₂)
    (fun _ _ => lipschitzOnWith_neg hL)
    ((continuousOn_flow hh hz₁).mono Icc_subset_Ici_self)
    (fun τ hτ => (hasDerivAt_flow hh hz₁ hτ.1).hasDerivWithinAt)
    (fun τ hτ => mem_closedBall_zero_iff.mpr
      ((norm_flow_le hh hz₁ hτ.1.le).trans (le_max_left _ _)))
    ((continuousOn_flow hh hz₂).mono Icc_subset_Ici_self)
    (fun τ hτ => (hasDerivAt_flow hh hz₂ hτ.1).hasDerivWithinAt)
    (fun τ hτ => mem_closedBall_zero_iff.mpr
      ((norm_flow_le hh hz₂ hτ.1.le).trans (le_max_right _ _)))
    heq
  have h0 := key ⟨le_rfl, ht⟩
  simpa [flow_zero hh hz₁, flow_zero hh hz₂] using h0

/-- `0` is a fixed point of the flow. -/
lemma flow_zero_right {t : ℝ} (ht : 0 ≤ t) : flow hh t 0 = 0 := by
  have key := eqOn_flow hh (ρ := 0) (by norm_num) (T := t) (β := fun _ => (0 : E))
    continuousOn_const
    (fun τ _ => by simpa [hh.map_zero] using hasDerivWithinAt_const τ (Ici τ) (0 : E))
    (fun τ _ => by simp) (by simp)
  exact (key ⟨ht, le_rfl⟩).symm

end FlowDef

/-! ### Decay of the flow -/

section Decay

variable (hh : IsCaratheodory h)
include hh

/-- Constants describing `h` near `0`: `‖h w - w‖ ≤ K ‖w‖²` for `‖w‖ ≤ δ₁`, with `K δ₁ ≤ 1/4`. -/
lemma IsCaratheodory.exists_local_constants :
    ∃ δ₁ > 0, δ₁ < 1 ∧ ∃ K : ℝ, 0 ≤ K ∧ K * δ₁ ≤ 1 / 4 ∧
      ∀ w : E, ‖w‖ ≤ δ₁ → ‖h w - w‖ ≤ K * ‖w‖ ^ 2 := by
  obtain ⟨δ₀, hδ₀, hδ₀1, K, hK, hKb⟩ := hh.exists_norm_sub_le_sq
  refine ⟨min δ₀ (1 / (4 * (K + 1))), by positivity, lt_of_le_of_lt (min_le_left _ _) hδ₀1,
    K, hK, ?_, fun w hw => hKb w (hw.trans (min_le_left _ _))⟩
  calc K * min δ₀ (1 / (4 * (K + 1))) ≤ K * (1 / (4 * (K + 1))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hK
    _ ≤ 1 / 4 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith

omit hh [FiniteDimensional ℂ E] in
lemma re_inner_ge_of_local {δ₁ K : ℝ} (hK : 0 ≤ K) (hKδ : K * δ₁ ≤ 1 / 4)
    (hloc : ∀ w : E, ‖w‖ ≤ δ₁ → ‖h w - w‖ ≤ K * ‖w‖ ^ 2) {w : E} (hw : ‖w‖ ≤ δ₁) :
    3 / 4 * ‖w‖ ^ 2 ≤ (⟪w, h w⟫_ℂ).re := by
  have hww : (⟪w, w⟫_ℂ).re = ‖w‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) w
  have e : (⟪w, h w⟫_ℂ).re = ‖w‖ ^ 2 + (⟪w, h w - w⟫_ℂ).re := by
    rw [inner_sub_right, Complex.sub_re, hww]; ring
  have h1 : |(⟪w, h w - w⟫_ℂ).re| ≤ ‖w‖ * ‖h w - w‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have h2 : ‖w‖ * ‖h w - w‖ ≤ ‖w‖ * (K * ‖w‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (hloc w hw) (norm_nonneg _)
  have h3 : ‖w‖ * (K * ‖w‖ ^ 2) ≤ 1 / 4 * ‖w‖ ^ 2 := by
    have : K * ‖w‖ ≤ K * δ₁ := mul_le_mul_of_nonneg_left hw hK
    have hw2 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
    calc ‖w‖ * (K * ‖w‖ ^ 2) = (K * ‖w‖) * ‖w‖ ^ 2 := by ring
      _ ≤ (1 / 4) * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right (this.trans hKδ) hw2
  have h4 := neg_abs_le (⟪w, h w - w⟫_ℂ).re
  rw [e]
  linarith

/-- **Exponential decay** near `0`: `‖φ_t(z)‖² ≤ e^{-3t/2} ‖z‖²` for `‖z‖ ≤ δ₁`. -/
lemma norm_flow_sq_le_exp {δ₁ K : ℝ} (hδ₁1 : δ₁ < 1) (hK : 0 ≤ K) (hKδ : K * δ₁ ≤ 1 / 4)
    (hloc : ∀ w : E, ‖w‖ ≤ δ₁ → ‖h w - w‖ ≤ K * ‖w‖ ^ 2) {z : E} (hz : ‖z‖ ≤ δ₁) {t : ℝ}
    (ht : 0 ≤ t) : ‖flow hh t z‖ ^ 2 ≤ Real.exp (-(3 / 2 * t)) * ‖z‖ ^ 2 := by
  have hzB : z ∈ unitBall E := mem_unitBall.mpr (lt_of_le_of_lt hz hδ₁1)
  have hNd : ∀ τ, 0 < τ → HasDerivAt (fun τ => Real.exp (3 / 2 * τ) * ‖flow hh τ z‖ ^ 2)
      (Real.exp (3 / 2 * τ) * (3 / 2) * ‖flow hh τ z‖ ^ 2 +
        Real.exp (3 / 2 * τ) * (2 * (⟪flow hh τ z, -h (flow hh τ z)⟫_ℂ).re)) τ := by
    intro τ hτ
    have h1 : HasDerivAt (fun τ => Real.exp (3 / 2 * τ)) (Real.exp (3 / 2 * τ) * (3 / 2)) τ := by
      simpa using ((hasDerivAt_id τ).const_mul (3 / 2 : ℝ)).exp
    have h2 : HasDerivAt (fun τ => ‖flow hh τ z‖ ^ 2)
        (2 * (⟪flow hh τ z, -h (flow hh τ z)⟫_ℂ).re) τ :=
      (hasDerivWithinAt_norm_sq (s := univ)
        (hasDerivAt_flow hh hzB hτ).hasDerivWithinAt).hasDerivAt univ_mem
    exact h1.mul h2
  have hanti : AntitoneOn (fun τ => Real.exp (3 / 2 * τ) * ‖flow hh τ z‖ ^ 2) (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (f' := fun τ => Real.exp (3 / 2 * τ) * (3 / 2) * ‖flow hh τ z‖ ^ 2 +
        Real.exp (3 / 2 * τ) * (2 * (⟪flow hh τ z, -h (flow hh τ z)⟫_ℂ).re))
    · intro τ hτ
      exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousWithinAt).mul
        (((continuousOn_flow hh hzB) τ hτ).norm.pow 2)
    · intro τ hτ
      rw [interior_Ici] at hτ
      exact (hNd τ hτ).hasDerivWithinAt
    · intro τ hτ
      rw [interior_Ici] at hτ
      have hφ : ‖flow hh τ z‖ ≤ δ₁ := (norm_flow_le hh hzB hτ.le).trans hz
      have h1 := re_inner_ge_of_local hK hKδ hloc hφ
      rw [inner_neg_right, Complex.neg_re]
      have hexp := Real.exp_pos (3 / 2 * τ)
      nlinarith [mul_nonneg hexp.le (sub_nonneg.mpr h1)]
  have h1 := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  simp only [mul_zero, Real.exp_zero, one_mul, flow_zero hh hzB] at h1
  calc ‖flow hh t z‖ ^ 2
      = Real.exp (-(3 / 2 * t)) * (Real.exp (3 / 2 * t) * ‖flow hh t z‖ ^ 2) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-(3 / 2 * t)) * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

/-- **Uniform eventual smallness**: on `closedBall 0 ρ`, `ρ < 1`, the flow enters any given ball
around `0` after a common time `T`. -/
lemma exists_time_flow_le {ρ δ : ℝ} (hρ1 : ρ < 1) (hδ : 0 < δ) :
    ∃ T, 0 ≤ T ∧ ∀ z : E, ‖z‖ ≤ ρ → ∀ t, T ≤ t → ‖flow hh t z‖ ≤ δ := by
  rcases le_or_gt ρ δ with hρδ | hδρ
  · refine ⟨0, le_rfl, fun z hz t ht => ?_⟩
    have hzB : z ∈ unitBall E := mem_unitBall.mpr (lt_of_le_of_lt hz hρ1)
    exact (norm_flow_le hh hzB ht).trans (hz.trans hρδ)
  obtain ⟨m, hm, hmb⟩ := hh.exists_re_inner_ge hδ hρ1
  have hT0 : 0 ≤ ρ ^ 2 / (2 * m) := by positivity
  refine ⟨ρ ^ 2 / (2 * m), hT0, fun z hz t ht => ?_⟩
  have hzB : z ∈ unitBall E := mem_unitBall.mpr (lt_of_le_of_lt hz hρ1)
  set T := ρ ^ 2 / (2 * m) with hT
  suffices hTz : ‖flow hh T z‖ ≤ δ from (norm_flow_antitone hh hzB hT0 ht).trans hTz
  by_contra hcon
  push Not at hcon
  have hann : ∀ τ ∈ Icc 0 T, δ ≤ ‖flow hh τ z‖ ∧ ‖flow hh τ z‖ ≤ ρ := fun τ hτ =>
    ⟨hcon.le.trans (norm_flow_antitone hh hzB hτ.1 hτ.2), (norm_flow_le hh hzB hτ.1).trans hz⟩
  have hQ : AntitoneOn (fun τ => ‖flow hh τ z‖ ^ 2 + 2 * m * τ) (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      (f' := fun τ => 2 * (⟪flow hh τ z, -h (flow hh τ z)⟫_ℂ).re + 2 * m)
    · intro τ hτ
      exact (((continuousOn_flow hh hzB).mono Icc_subset_Ici_self τ hτ).norm.pow 2).add
        (continuousWithinAt_const.mul continuousWithinAt_id)
    · intro τ hτ
      rw [interior_Icc] at hτ
      have h2 := (hasDerivWithinAt_norm_sq (s := univ)
        (hasDerivAt_flow hh hzB hτ.1).hasDerivWithinAt).hasDerivAt univ_mem
      have h3 := h2.fun_add ((hasDerivAt_id τ).const_mul (2 * m))
      simpa using h3.hasDerivWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      have h1 := hmb _ (hann τ (Ioo_subset_Icc_self hτ)).1 (hann τ (Ioo_subset_Icc_self hτ)).2
      rw [inner_neg_right, Complex.neg_re]
      linarith
  have h1 := hQ (left_mem_Icc.mpr hT0) (right_mem_Icc.mpr hT0) hT0
  simp only [flow_zero hh hzB, mul_zero, add_zero] at h1
  have h2 : 2 * m * T = ρ ^ 2 := by rw [hT]; field_simp
  have h3 : ‖z‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have h4 : δ ^ 2 < ‖flow hh T z‖ ^ 2 := pow_lt_pow_left₀ hcon hδ.le two_ne_zero
  nlinarith [sq_nonneg δ]

end Decay

end LoewnerS0
