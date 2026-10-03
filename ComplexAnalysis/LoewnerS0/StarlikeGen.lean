import LoewnerS0.FlowHolo
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Every `h ∈ M(𝔹)` generates a starlike map

Let `E` be a finite-dimensional complex inner product space and `h ∈ M(𝔹)`, with flow `φ_t`
(`LoewnerS0.flow`). The limit

  `f(z) = lim_{t → ∞} e^t φ_t(z)`

exists locally uniformly on `𝔹` (`LoewnerS0.starlikeMap`), and `f` is a normalized starlike map
with `Df(z) h(z) = f(z)`. This proves `StarlikeGeneration E` (`LoewnerS0.starlikeGeneration`).

* convergence: near `0`, `‖φ_t(z)‖² ≤ e^{-3t/2} ‖z‖²`, so `‖d/dt (e^t φ_t(z))‖ ≤ K ‖z‖² e^{-t/2}`;
  on `closedBall 0 ρ` the flow enters this neighbourhood after a common time;
* `f` is holomorphic (Weierstrass), `f(0) = 0`, and `‖f(z) - z‖ ≤ 2K‖z‖²`, so `Df(0) = I`;
* `f(φ_s(z)) = e^{-s} f(z)` (semigroup law); differentiating at `s = 0` gives `Df · h = f`;
* starlikeness: `e^{-s} f(z) = f(φ_s(z)) ∈ f(𝔹)`;
* univalence: `f` is injective near `0` (inverse function theorem); if `f(z₁) = f(z₂)` then
  `f(φ_s(z₁)) = f(φ_s(z₂))` with `φ_s(zᵢ)` close to `0` for large `s`, so `φ_s(z₁) = φ_s(z₂)`,
  and `φ_s` is injective.
-/

open Complex Metric Set Filter Asymptotics
open scoped Topology InnerProductSpace NNReal

noncomputable section

namespace LoewnerS0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {h : E → E}

omit [FiniteDimensional ℂ E] in
/-- A map with `f 0 = 0` and `‖f z - L z‖ ≤ C ‖z‖²` near `0` has derivative `L` at `0`. -/
lemma hasFDerivAt_zero_of_norm_sub_le_sq {f : E → E} {L : E →L[ℂ] E} {δ C : ℝ} (hδ : 0 < δ)
    (h0 : f 0 = 0) (hb : ∀ z : E, ‖z‖ < δ → ‖f z - L z‖ ≤ C * ‖z‖ ^ 2) : HasFDerivAt f L 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have h1 : (fun z : E => f (0 + z) - f 0 - L z) =O[𝓝 0] fun z => ‖z‖ ^ 2 := by
    refine IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with z hz
    rw [mem_ball_zero_iff] at hz
    simpa [h0] using hb z hz
  exact h1.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)

lemma tendsto_mul_exp_neg (C T : ℝ) :
    Tendsto (fun s : ℝ => C * Real.exp (-((s - T) / 2))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => (s - T) / 2) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-T) tendsto_id).atTop_div_const two_pos
  have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
  simpa using h2.const_mul C

variable (hh : IsCaratheodory h)

/-- `e^t φ_t(z)`. -/
def scaledFlow (t : ℝ) (z : E) : E := Real.exp t • flow hh t z

lemma hasDerivWithinAt_scaledFlow {z : E} (hz : z ∈ unitBall E) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun τ => scaledFlow hh τ z)
      (Real.exp t • (flow hh t z - h (flow hh t z))) (Ici t) t := by
  have h3 := ((Real.hasDerivAt_exp t).hasDerivWithinAt (s := Ici t)).fun_smul
    (hasDerivWithinAt_flow hh hz ht)
  have e : (fun τ => scaledFlow hh τ z) = fun i => Real.exp i • flow hh i z := rfl
  rw [e]
  convert h3 using 1
  rw [smul_sub, smul_neg]
  abel

lemma continuousOn_scaledFlow {z : E} (hz : z ∈ unitBall E) :
    ContinuousOn (fun τ => scaledFlow hh τ z) (Ici 0) :=
  Real.continuous_exp.continuousOn.smul (continuousOn_flow hh hz)

lemma scaledFlow_shift {z : E} (hz : z ∈ unitBall E) {T₀ t : ℝ} (hT₀ : 0 ≤ T₀) (ht : T₀ ≤ t) :
    scaledFlow hh t z = Real.exp T₀ • scaledFlow hh (t - T₀) (flow hh T₀ z) := by
  unfold scaledFlow
  rw [← flow_add hh hz hT₀ (sub_nonneg.mpr ht), add_sub_cancel, smul_smul, ← Real.exp_add,
    add_sub_cancel]

/-- The Cauchy estimate near `0`. -/
lemma norm_scaledFlow_sub_le {δ₁ K : ℝ} (hδ₁1 : δ₁ < 1) (hK : 0 ≤ K) (hKδ : K * δ₁ ≤ 1 / 4)
    (hloc : ∀ w : E, ‖w‖ ≤ δ₁ → ‖h w - w‖ ≤ K * ‖w‖ ^ 2) {z : E} (hz : ‖z‖ ≤ δ₁) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖scaledFlow hh t z - scaledFlow hh s z‖ ≤
      2 * K * ‖z‖ ^ 2 * (Real.exp (-(s / 2)) - Real.exp (-(t / 2))) := by
  have hzB : z ∈ unitBall E := mem_unitBall.mpr (lt_of_le_of_lt hz hδ₁1)
  have hB : ∀ τ, HasDerivAt
      (fun τ => 2 * K * ‖z‖ ^ 2 * (Real.exp (-(s / 2)) - Real.exp (-(τ / 2))))
      (K * ‖z‖ ^ 2 * Real.exp (-(τ / 2))) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => Real.exp (-(τ / 2))) (Real.exp (-(τ / 2)) * (-(1 / 2))) τ := by
      have := ((hasDerivAt_id τ).div_const 2).neg.exp
      simpa using this
    have h2 := (h1.const_sub (Real.exp (-(s / 2)))).const_mul (2 * K * ‖z‖ ^ 2)
    convert h2 using 1
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun τ => scaledFlow hh τ z - scaledFlow hh s z)
    (f' := fun τ => Real.exp τ • (flow hh τ z - h (flow hh τ z))) (a := s) (b := t)
    ((continuousOn_scaledFlow hh hzB).sub continuousOn_const |>.mono
      (fun τ hτ => mem_Ici.mpr (hs.trans hτ.1)))
    (fun τ hτ => (hasDerivWithinAt_scaledFlow hh hzB (hs.trans hτ.1)).sub_const _)
    (by simp) hB (fun τ hτ => by
      have hτ0 : 0 ≤ τ := hs.trans hτ.1
      have hφ : ‖flow hh τ z‖ ≤ δ₁ := (norm_flow_le hh hzB hτ0).trans hz
      have h1 := hloc _ hφ
      have h2 := norm_flow_sq_le_exp hh hδ₁1 hK hKδ hloc hz hτ0
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos τ), norm_sub_rev]
      calc Real.exp τ * ‖h (flow hh τ z) - flow hh τ z‖
          ≤ Real.exp τ * (K * ‖flow hh τ z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos τ).le
        _ ≤ Real.exp τ * (K * (Real.exp (-(3 / 2 * τ)) * ‖z‖ ^ 2)) := by gcongr
        _ = K * ‖z‖ ^ 2 * (Real.exp τ * Real.exp (-(3 / 2 * τ))) := by ring
        _ = K * ‖z‖ ^ 2 * Real.exp (-(τ / 2)) := by
            rw [← Real.exp_add]; ring_nf)
  exact key ⟨hst, le_rfl⟩

/-- The uniform Cauchy estimate on `closedBall 0 ρ`, `ρ < 1`. -/
lemma exists_uniform_cauchy {ρ : ℝ} (hρ1 : ρ < 1) :
    ∃ T₀ C : ℝ, 0 ≤ T₀ ∧ ∀ z : E, ‖z‖ ≤ ρ → ∀ s t, T₀ ≤ s → s ≤ t →
      ‖scaledFlow hh t z - scaledFlow hh s z‖ ≤ C * Real.exp (-((s - T₀) / 2)) := by
  obtain ⟨δ₁, hδ₁, hδ₁1, K, hK, hKδ, hloc⟩ := hh.exists_local_constants
  obtain ⟨T₀, hT₀, hT⟩ := exists_time_flow_le hh hρ1 hδ₁
  refine ⟨T₀, Real.exp T₀ * (2 * K * δ₁ ^ 2), hT₀, fun z hz s t hs hst => ?_⟩
  have hzB : z ∈ unitBall E := mem_unitBall.mpr (lt_of_le_of_lt hz hρ1)
  have hz' : ‖flow hh T₀ z‖ ≤ δ₁ := hT z hz T₀ le_rfl
  rw [scaledFlow_shift hh hzB hT₀ (hs.trans hst), scaledFlow_shift hh hzB hT₀ hs, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have key := norm_scaledFlow_sub_le hh hδ₁1 hK hKδ hloc hz' (sub_nonneg.mpr hs)
    (sub_le_sub_right hst T₀)
  have h1 : ‖flow hh T₀ z‖ ^ 2 ≤ δ₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz' 2
  have h2 : 0 ≤ Real.exp (-((t - T₀) / 2)) := (Real.exp_pos _).le
  have hes : Real.exp (-((t - T₀) / 2)) ≤ Real.exp (-((s - T₀) / 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : 2 * K * ‖flow hh T₀ z‖ ^ 2 *
      (Real.exp (-((s - T₀) / 2)) - Real.exp (-((t - T₀) / 2))) ≤
      2 * K * δ₁ ^ 2 * Real.exp (-((s - T₀) / 2)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) (by linarith) (sub_nonneg.mpr hes)
      (by positivity)
  calc Real.exp T₀ * ‖scaledFlow hh (t - T₀) (flow hh T₀ z) - scaledFlow hh (s - T₀) (flow hh T₀ z)‖
      ≤ Real.exp T₀ * (2 * K * ‖flow hh T₀ z‖ ^ 2 *
          (Real.exp (-((s - T₀) / 2)) - Real.exp (-((t - T₀) / 2)))) :=
        mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
    _ ≤ Real.exp T₀ * (2 * K * δ₁ ^ 2 * Real.exp (-((s - T₀) / 2))) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = Real.exp T₀ * (2 * K * δ₁ ^ 2) * Real.exp (-((s - T₀) / 2)) := by ring

/-- The starlike map generated by `h`: `f(z) = lim_{t → ∞} e^t φ_t(z)`. -/
def starlikeMap (z : E) : E := limUnder atTop (fun t : ℝ => scaledFlow hh t z)

lemma tendsto_scaledFlow {z : E} (hz : z ∈ unitBall E) :
    Tendsto (fun t : ℝ => scaledFlow hh t z) atTop (𝓝 (starlikeMap hh z)) := by
  obtain ⟨T₀, C, hT₀, hC⟩ := exists_uniform_cauchy hh (mem_unitBall.mp hz)
  have hcauchy : CauchySeq (fun t : ℝ => scaledFlow hh t z) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((tendsto_mul_exp_neg C T₀).eventually (gt_mem_nhds hε) |>.and (eventually_ge_atTop T₀))
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hC z le_rfl N n (hN N le_rfl).2 hn) (hN N le_rfl).1
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  rw [starlikeMap, hL.limUnder_eq]
  exact hL

/-- The convergence `e^t φ_t → f` is uniform on `closedBall 0 ρ`, `ρ < 1`. -/
lemma exists_uniform_limit {ρ : ℝ} (hρ1 : ρ < 1) :
    ∃ T₀ C : ℝ, 0 ≤ T₀ ∧ ∀ z : E, ‖z‖ ≤ ρ → ∀ s, T₀ ≤ s →
      ‖starlikeMap hh z - scaledFlow hh s z‖ ≤ C * Real.exp (-((s - T₀) / 2)) := by
  obtain ⟨T₀, C, hT₀, hC⟩ := exists_uniform_cauchy hh hρ1
  refine ⟨T₀, C, hT₀, fun z hz s hs => ?_⟩
  have hzB : z ∈ unitBall E := mem_unitBall.mpr (lt_of_le_of_lt hz hρ1)
  have hlim := ((tendsto_scaledFlow hh hzB).sub_const (scaledFlow hh s z)).norm
  exact le_of_tendsto hlim (eventually_atTop.mpr ⟨s, fun t ht => hC z hz s t hs ht⟩)

/-- `f` is holomorphic on `𝔹`. -/
theorem differentiableOn_starlikeMap : DifferentiableOn ℂ (starlikeMap hh) (unitBall E) := by
  intro z₀ hz₀
  set ρ := (1 + ‖z₀‖) / 2 with hρ_def
  have hz₀1 : ‖z₀‖ < 1 := mem_unitBall.mp hz₀
  have hρ1 : ρ < 1 := by linarith
  have hz₀ρ : ‖z₀‖ < ρ := by linarith
  obtain ⟨T₀, C, hT₀, hC⟩ := exists_uniform_limit hh hρ1
  have hG : ∀ n : ℕ, DifferentiableOn ℂ (fun z => scaledFlow hh n z) (ball 0 ρ) := by
    intro n
    have hd := (differentiableOn_flow hh (t := n) n.cast_nonneg).mono
      (ball_subset_ball hρ1.le)
    have e : (fun z => scaledFlow hh n z) = fun z => ((Real.exp n : ℝ) : ℂ) • flow hh n z := by
      funext z; simp only [scaledFlow]; rw [Complex.coe_smul]
    rw [e]
    exact hd.const_smul _
  have hconv : TendstoUniformlyOn (fun n : ℕ => fun z => scaledFlow hh n z) (starlikeMap hh)
      atTop (ball 0 ρ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h1 : Tendsto (fun n : ℕ => C * Real.exp (-(((n : ℝ) - T₀) / 2))) atTop (𝓝 0) :=
      (tendsto_mul_exp_neg C T₀).comp tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((h1.eventually (gt_mem_nhds hε)).and
      (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop T₀)))
    refine eventually_atTop.mpr ⟨N, fun n hn z hz => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hC z (mem_ball_zero_iff.mp hz).le n (hN n hn).2) (hN n hn).1
  have hd := SCV.differentiableOn_of_tendstoUniformlyOn isOpen_ball hG hconv
  exact ((hd z₀ (mem_ball_zero_iff.mpr hz₀ρ)).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz₀ρ))).differentiableWithinAt

lemma starlikeMap_zero : starlikeMap hh 0 = 0 := by
  have h1 := tendsto_scaledFlow hh (zero_mem_unitBall (E := E))
  have h2 : (fun _ : ℝ => (0 : E)) =ᶠ[atTop] fun t : ℝ => scaledFlow hh t 0 :=
    eventually_atTop.mpr ⟨0, fun t ht => by simp [scaledFlow, flow_zero_right hh ht]⟩
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' h2)

/-- `f(z) = z + O(‖z‖²)`. -/
lemma exists_norm_starlikeMap_sub_le :
    ∃ δ₁ > 0, ∃ K : ℝ, ∀ z : E, ‖z‖ < δ₁ → ‖starlikeMap hh z - z‖ ≤ 2 * K * ‖z‖ ^ 2 := by
  obtain ⟨δ₁, hδ₁, hδ₁1, K, hK, hKδ, hloc⟩ := hh.exists_local_constants
  refine ⟨δ₁, hδ₁, K, fun z hz => ?_⟩
  have hzB : z ∈ unitBall E := mem_unitBall.mpr (lt_trans hz hδ₁1)
  have hlim := ((tendsto_scaledFlow hh hzB).sub_const z).norm
  refine le_of_tendsto hlim (eventually_atTop.mpr ⟨0, fun t ht => ?_⟩)
  have key := norm_scaledFlow_sub_le hh hδ₁1 hK hKδ hloc hz.le le_rfl ht
  have h0 : scaledFlow hh 0 z = z := by simp [scaledFlow, flow_zero hh hzB]
  rw [h0] at key
  have h1 : Real.exp (-((0 : ℝ) / 2)) - Real.exp (-(t / 2)) ≤ 1 := by
    have := Real.exp_pos (-(t / 2))
    simp only [zero_div, neg_zero, Real.exp_zero]
    linarith
  have h2 : 0 ≤ 2 * K * ‖z‖ ^ 2 := by positivity
  calc ‖scaledFlow hh t z - z‖ ≤ 2 * K * ‖z‖ ^ 2 * (Real.exp (-((0 : ℝ) / 2)) - Real.exp (-(t / 2))) :=
        key
    _ ≤ 2 * K * ‖z‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 h2
    _ = 2 * K * ‖z‖ ^ 2 := mul_one _

/-- `f` is normalized. -/
theorem isNormalized_starlikeMap : IsNormalized (starlikeMap hh) where
  differentiableOn := differentiableOn_starlikeMap hh
  map_zero := starlikeMap_zero hh
  fderiv_zero := by
    obtain ⟨δ₁, hδ₁, K, hb⟩ := exists_norm_starlikeMap_sub_le hh
    exact (hasFDerivAt_zero_of_norm_sub_le_sq hδ₁ (starlikeMap_zero hh)
      (L := ContinuousLinearMap.id ℂ E) (C := 2 * K) (fun z hz => by simpa using hb z hz)).fderiv

/-- The **functional equation** `f(φ_s(z)) = e^{-s} f(z)`. -/
lemma starlikeMap_flow {z : E} (hz : z ∈ unitBall E) {s : ℝ} (hs : 0 ≤ s) :
    starlikeMap hh (flow hh s z) = Real.exp (-s) • starlikeMap hh z := by
  have h1 := tendsto_scaledFlow hh (flow_mem hh hz hs)
  have h2 : Tendsto (fun t : ℝ => scaledFlow hh (s + t) z) atTop (𝓝 (starlikeMap hh z)) :=
    (tendsto_scaledFlow hh hz).comp (tendsto_atTop_add_const_left _ s tendsto_id)
  have h3 := h2.const_smul (Real.exp (-s))
  have e : ∀ t, 0 ≤ t →
      Real.exp (-s) • scaledFlow hh (s + t) z = scaledFlow hh t (flow hh s z) := by
    intro t ht
    simp only [scaledFlow]
    rw [← flow_add hh hz hs ht, smul_smul, ← Real.exp_add, neg_add_cancel_left]
  have h4 : Tendsto (fun t => scaledFlow hh t (flow hh s z)) atTop
      (𝓝 (Real.exp (-s) • starlikeMap hh z)) :=
    h3.congr' (eventually_atTop.mpr ⟨0, fun t ht => e t ht⟩)
  exact tendsto_nhds_unique h1 h4

/-- `Df(z) h(z) = f(z)`. -/
theorem fderiv_starlikeMap_apply {z : E} (hz : z ∈ unitBall E) :
    fderiv ℂ (starlikeMap hh) z (h z) = starlikeMap hh z := by
  have hd : HasFDerivAt (starlikeMap hh) (fderiv ℂ (starlikeMap hh) z) z :=
    (((differentiableOn_starlikeMap hh) z hz).differentiableAt
      (isOpen_unitBall.mem_nhds hz)).hasFDerivAt
  have hf := hasDerivWithinAt_flow hh hz le_rfl
  rw [flow_zero hh hz] at hf
  have h1 : HasDerivWithinAt (fun s => starlikeMap hh (flow hh s z))
      (fderiv ℂ (starlikeMap hh) z (-h z)) (Ici 0) 0 := by
    have := (hd.restrictScalars ℝ).comp_hasDerivWithinAt_of_eq (0 : ℝ) hf (flow_zero hh hz).symm
    simpa [Function.comp_def] using this
  have h2 : HasDerivWithinAt (fun s => starlikeMap hh (flow hh s z)) (-starlikeMap hh z)
      (Ici 0) 0 := by
    have h3 : HasDerivAt (fun s : ℝ => Real.exp (-s) • starlikeMap hh z)
        (-starlikeMap hh z) 0 := by
      have := ((hasDerivAt_neg (0 : ℝ)).exp).smul_const (starlikeMap hh z)
      simpa using this
    exact h3.hasDerivWithinAt.congr_of_mem (fun s hs => starlikeMap_flow hh hz hs)
      (mem_Ici.mpr le_rfl)
  have := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ h1 h2
  rw [map_neg, neg_inj] at this
  exact this

/-- `f` is injective near `0` (inverse function theorem). -/
lemma exists_injOn_ball : ∃ ε > 0, InjOn (starlikeMap hh) (ball 0 ε) := by
  have hC1 : ContDiffAt ℂ 1 (starlikeMap hh) 0 :=
    ((differentiableOn_starlikeMap hh).contDiffOn_of_isOpen isOpen_unitBall 1).contDiffAt
      (unitBall_mem_nhds zero_mem_unitBall)
  have hs := hC1.hasStrictFDerivAt one_ne_zero
  rw [(isNormalized_starlikeMap hh).fderiv_zero, ← ContinuousLinearEquiv.coe_refl] at hs
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.mp (hs.toOpenPartialHomeomorph (starlikeMap hh)).open_source 0
    hs.mem_toOpenPartialHomeomorph_source
  refine ⟨ε, hε, ?_⟩
  have := ((hs.toOpenPartialHomeomorph (starlikeMap hh)).injOn).mono hεs
  simpa using this

/-- `f` is **univalent** on `𝔹`. -/
theorem injOn_starlikeMap : InjOn (starlikeMap hh) (unitBall E) := by
  intro z₁ hz₁ z₂ hz₂ heq
  obtain ⟨ε, hε, hinj⟩ := exists_injOn_ball hh
  have hρ1 : max ‖z₁‖ ‖z₂‖ < 1 := max_lt (mem_unitBall.mp hz₁) (mem_unitBall.mp hz₂)
  obtain ⟨T, hT0, hT⟩ := exists_time_flow_le hh hρ1 (half_pos hε)
  have h1 : flow hh T z₁ ∈ ball (0 : E) ε := mem_ball_zero_iff.mpr
    (lt_of_le_of_lt (hT z₁ (le_max_left _ _) T le_rfl) (half_lt_self hε))
  have h2 : flow hh T z₂ ∈ ball (0 : E) ε := mem_ball_zero_iff.mpr
    (lt_of_le_of_lt (hT z₂ (le_max_right _ _) T le_rfl) (half_lt_self hε))
  have h3 : starlikeMap hh (flow hh T z₁) = starlikeMap hh (flow hh T z₂) := by
    rw [starlikeMap_flow hh hz₁ hT0, starlikeMap_flow hh hz₂ hT0, heq]
  exact flow_injective hh hz₁ hz₂ hT0 (hinj h1 h2 h3)

/-- `f(𝔹)` is **starlike** with respect to `0`. -/
theorem starConvex_starlikeMap : StarConvex ℝ (0 : E) (starlikeMap hh '' unitBall E) := by
  rintro _ ⟨z, hz, rfl⟩ a b _ hb _
  rw [smul_zero, zero_add]
  rcases hb.eq_or_lt with hb0 | hbpos
  · rw [← hb0, zero_smul]
    exact ⟨0, zero_mem_unitBall, starlikeMap_zero hh⟩
  · have hb1 : b ≤ 1 := by linarith
    have hlog : 0 ≤ -Real.log b := neg_nonneg.mpr (Real.log_nonpos hb hb1)
    refine ⟨flow hh (-Real.log b) z, flow_mem hh hz hlog, ?_⟩
    rw [starlikeMap_flow hh hz hlog, neg_neg, Real.exp_log hbpos]

theorem starlikeMap_mem_classSstar : starlikeMap hh ∈ classSstar E :=
  ⟨⟨isNormalized_starlikeMap hh, injOn_starlikeMap hh⟩, starConvex_starlikeMap hh⟩

omit hh in
/-- **Every `h ∈ M(𝔹)` generates a normalized starlike map `f` with `Df(z) h(z) = f(z)`**
(Suffridge; the map of the constant Loewner chain), on the unit ball of any finite-dimensional
complex inner product space. -/
theorem starlikeGeneration : StarlikeGeneration E := fun _ hh =>
  ⟨starlikeMap hh, starlikeMap_mem_classSstar hh, fun _ hz => fderiv_starlikeMap_apply hh hz⟩

/-- `f` has **parametric representation**: it is `lim e^t v(z, t)` for the constant Herglotz
vector field `h(·, t) = h`, whose Loewner solution is the flow of `h`. -/
theorem isParametricRep_starlikeMap :
    IsParametricRep (starlikeMap hh) (fun _ => h) (fun t z => flow hh t z) where
  herglotz := ⟨fun _ _ => hh, fun _ _ => MeasureTheory.aestronglyMeasurable_const⟩
  solution := by
    intro z hz t ht
    have hcont : ContinuousOn (fun s => h (flow hh s z)) (Icc 0 t) :=
      hh.isNormalized.differentiableOn.continuousOn.comp
        ((continuousOn_flow hh hz).mono Icc_subset_Ici_self) (fun s hs => flow_mem hh hz hs.1)
    have hint : IntervalIntegrable (fun s => h (flow hh s z)) MeasureTheory.volume 0 t :=
      hcont.intervalIntegrable_of_Icc ht
    refine ⟨flow_mem hh hz ht, hint, ?_⟩
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
      ((continuousOn_flow hh hz).mono Icc_subset_Ici_self)
      (fun s hs => hasDerivAt_flow hh hz hs.1) (hcont.neg.intervalIntegrable_of_Icc ht)
    rw [intervalIntegral.integral_neg, flow_zero hh hz] at hftc
    linear_combination (norm := module) -hftc
  tendsto := fun z hz => by
    refine (tendsto_scaledFlow hh hz).congr (fun t => ?_)
    simp only [scaledFlow]
    rw [Complex.coe_smul]

/-- `f ∈ S⁰(𝔹)`. -/
theorem starlikeMap_mem_classS0 : starlikeMap hh ∈ classS0 E :=
  ⟨fun _ => h, fun t z => flow hh t z, isParametricRep_starlikeMap hh⟩

end LoewnerS0
