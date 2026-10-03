import LoewnerS0.LoewnerHolo
import LoewnerS0.StarlikeGen

/-!
# Maps with parametric representation are univalent: `S⁰(𝔹) ⊆ S(𝔹)`

Let `f(z) = lim_{t → ∞} eᵗ v(z, t)` for a solution `v` of the Loewner ODE.

* `f` is holomorphic: `z ↦ eᵗ v(z, t)` is holomorphic (`IsLoewnerSolution.differentiableOn`) and
  converges locally uniformly, with the explicit rate `‖f(z) - eˢ v(z, s)‖ ≤ K(‖z‖) e^{-s}`.
* `f` is normalized: `‖f(z) - z‖ ≤ K(‖z‖) = 8‖z‖²/(1-‖z‖)⁶`.
* `f` is injective: for `h ∈ M(𝔹)` one has `‖Dh(w) - I‖ ≤ C ‖w‖` on `closedBall 0 ρ` (Schwarz
  lemma), so `Re ⟨h(w₁) - h(w₂), w₁ - w₂⟩ ≤ (1 + C max ‖wᵢ‖) ‖w₁ - w₂‖²`; together with the
  exponential decay of `‖v(z, t)‖`, Gronwall's inequality gives
  `eᵗ ‖v(z₁, t) - v(z₂, t)‖ ≥ e^{-C c} ‖z₁ - z₂‖`.
-/

open Complex Metric Set Filter MeasureTheory
open scoped InnerProductSpace Topology NNReal

noncomputable section

namespace LoewnerS0

/-- The constant `K(r) = 8 (r/(1-r)²)²/(1-r)²` of the Cauchy estimate for `eᵗ v(z, t)`. -/
def cauchyConst (r : ℝ) : ℝ := 8 * (r / (1 - r) ^ 2) ^ 2 / (1 - r) ^ 2

lemma cauchyConst_mono {r₁ r₂ : ℝ} (h0 : 0 ≤ r₁) (h12 : r₁ ≤ r₂) (h2 : r₂ < 1) :
    cauchyConst r₁ ≤ cauchyConst r₂ := by
  unfold cauchyConst
  have h1 : 0 < 1 - r₂ := by linarith
  have h1' : 1 - r₂ ≤ 1 - r₁ := by linarith
  have ha : r₁ / (1 - r₁) ^ 2 ≤ r₂ / (1 - r₂) ^ 2 := by
    gcongr
    linarith
  have ha0 : 0 ≤ r₁ / (1 - r₁) ^ 2 := by
    have : 0 < 1 - r₁ := by linarith
    positivity
  gcongr

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] {h v : ℝ → E → E} {f : E → E}

namespace IsParametricRep

/-- The rate of convergence of `eᵗ v(z, t)`. -/
lemma norm_sub_exp_smul_le (hf : IsParametricRep f h v) {z : E} (hz : z ∈ unitBall E) {s : ℝ}
    (hs : 0 ≤ s) : ‖f z - (Real.exp s : ℂ) • v s z‖ ≤ cauchyConst ‖z‖ * Real.exp (-s) := by
  have hlim : Tendsto (fun t => ‖(Real.exp t : ℂ) • v t z - (Real.exp s : ℂ) • v s z‖) atTop
      (𝓝 ‖f z - (Real.exp s : ℂ) • v s z‖) :=
    ((hf.tendsto z hz).sub tendsto_const_nhds).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop s] with t hst
  exact hf.solution.norm_exp_smul_sub_le hf.herglotz hz hs hst

/-- **`f` is holomorphic** (Weierstrass). -/
theorem differentiableOn (hf : IsParametricRep f h v) : DifferentiableOn ℂ f (unitBall E) := by
  have hh := hf.herglotz
  have hv := hf.solution
  suffices H : ∀ r : ℝ, 0 < r → r < 1 → DifferentiableOn ℂ f (ball 0 r) by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_unitBall.mp hz
    have hr := H ((1 + ‖z‖) / 2) (by positivity) (by linarith)
    have hzr : z ∈ ball (0 : E) ((1 + ‖z‖) / 2) := by
      rw [mem_ball_zero_iff]; linarith
    exact ((hr z hzr).differentiableAt (isOpen_ball.mem_nhds hzr)).differentiableWithinAt
  intro r hr0 hr1
  have hsub : ball (0 : E) r ⊆ unitBall E := ball_subset_ball hr1.le
  refine SCV.differentiableOn_of_tendstoUniformlyOn isOpen_ball
    (G := fun n z => (Real.exp n : ℂ) • v n z)
    (fun n => ((hv.differentiableOn hh (Nat.cast_nonneg n)).mono hsub).const_smul _) ?_
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => cauchyConst r * Real.exp (-(n : ℝ))) atTop
      (𝓝 (cauchyConst r * 0)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul _
  rw [mul_zero] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ hn
  refine (hf.norm_sub_exp_smul_le (hsub hz) (Nat.cast_nonneg n)).trans ?_
  exact mul_le_mul_of_nonneg_right (cauchyConst_mono (norm_nonneg z)
    (mem_ball_zero_iff.mp hz).le hr1) (Real.exp_pos _).le

lemma map_zero (hf : IsParametricRep f h v) : f 0 = 0 := by
  have hlim := hf.tendsto 0 zero_mem_unitBall
  have h0 : ∀ t, 0 ≤ t → v t 0 = 0 := fun t ht => norm_le_zero_iff.mp
    ((hf.solution.norm_le hf.herglotz zero_mem_unitBall ht).trans_eq norm_zero)
  refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [h0 t ht, smul_zero]

lemma norm_sub_self_le (hf : IsParametricRep f h v) {z : E} (hz : z ∈ unitBall E) :
    ‖f z - z‖ ≤ cauchyConst ‖z‖ := by
  have := hf.norm_sub_exp_smul_le hz le_rfl
  rwa [Real.exp_zero, Complex.ofReal_one, one_smul, hf.solution.apply_zero hz, neg_zero,
    Real.exp_zero, mul_one] at this

/-- **`f` is normalized.** -/
theorem isNormalized (hf : IsParametricRep f h v) : IsNormalized f := by
  refine ⟨hf.differentiableOn, hf.map_zero, ?_⟩
  refine (hasFDerivAt_zero_of_norm_sub_le_sq (δ := 1 / 2) (C := 512) (by norm_num) hf.map_zero
    fun z hz => ?_).fderiv
  have hz1 : z ∈ unitBall E := mem_unitBall.mpr (by linarith)
  refine (hf.norm_sub_self_le hz1).trans (le_of_eq_of_le rfl ?_)
  unfold cauchyConst
  have h1 : (1 : ℝ) / 2 < 1 - ‖z‖ := by linarith
  have h2 : 0 < 1 - ‖z‖ := by linarith
  have h3 : (1 : ℝ) / 64 ≤ (1 - ‖z‖) ^ 6 := by
    have : ((1 : ℝ) / 2) ^ 6 ≤ (1 - ‖z‖) ^ 6 := pow_le_pow_left₀ (by norm_num) h1.le 6
    norm_num at this ⊢
    linarith
  have hkey : 8 * (‖z‖ / (1 - ‖z‖) ^ 2) ^ 2 / (1 - ‖z‖) ^ 2 = 8 * ‖z‖ ^ 2 / (1 - ‖z‖) ^ 6 := by
    field_simp
  rw [hkey, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg ‖z‖]

end IsParametricRep

/-! ### `Dh(w) = I + O(‖w‖)` uniformly on `M(𝔹)` -/

/-- The constant in `‖Dh(w) - I‖ ≤ C ‖w‖` on `closedBall 0 ρ`. -/
def derivConst (ρ : ℝ) : ℝ := (32 / (1 - (1 + ρ) / 2) ^ 3 + 1) / ((1 + ρ) / 2)

lemma derivConst_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) : 0 ≤ derivConst ρ := by
  unfold derivConst
  have : 0 < 1 - (1 + ρ) / 2 := by linarith
  positivity

section Deriv

variable {g : E → E}

/-- **`Dh(w) = I + O(‖w‖)`** uniformly on `M(𝔹)` (Schwarz lemma for `w ↦ Dh(w)x - x`). -/
theorem IsCaratheodory.norm_fderiv_sub_id_le (hg : IsCaratheodory g) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < 1) {w : E} (hw : ‖w‖ ≤ ρ) :
    ‖fderiv ℂ g w - ContinuousLinearMap.id ℂ E‖ ≤ derivConst ρ * ‖w‖ := by
  set ρ' := (1 + ρ) / 2 with hρ'def
  have hρ'0 : 0 < ρ' := by positivity
  have hρ'1 : ρ' < 1 := by rw [hρ'def]; linarith
  have hwρ' : ‖w‖ < ρ' := by rw [hρ'def]; linarith
  set B := 32 / (1 - ρ') ^ 3 + 1 with hB
  have hB0 : 0 ≤ B := by
    have : 0 < 1 - ρ' := by linarith
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (derivConst_nonneg hρ0 hρ)
    (norm_nonneg _)) fun x => ?_
  -- the holomorphic map `G(w) = Dg(w) x - x`
  set G : E → E := fun w => fderiv ℂ g w x - x with hG
  have hGd : DifferentiableOn ℂ G (ball 0 ρ') :=
    ((hg.isNormalized.differentiableOn.differentiableOn_fderiv_apply isOpen_unitBall x).mono
      (ball_subset_ball hρ'1.le)).sub_const x
  have hG0 : G 0 = 0 := by simp [hG, hg.isNormalized.fderiv_zero]
  have hmaps : MapsTo G (ball 0 ρ') (closedBall (G 0) (B * ‖x‖)) := by
    intro y hy
    rw [hG0, mem_closedBall_zero_iff]
    have hy' : ‖y‖ ≤ ρ' := (mem_ball_zero_iff.mp hy).le
    have hD := hg.norm_fderiv_le hρ'1 hy'
    calc ‖fderiv ℂ g y x - x‖ ≤ ‖fderiv ℂ g y x‖ + ‖x‖ := _root_.norm_sub_le _ _
      _ ≤ 32 / (1 - ρ') ^ 3 * ‖x‖ + ‖x‖ := by
          gcongr
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
      _ = B * ‖x‖ := by rw [hB]; ring
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hGd hmaps
    (mem_ball_zero_iff.mpr hwρ')
  rw [hG0, dist_zero_right, dist_zero_right] at hS
  calc ‖(fderiv ℂ g w - ContinuousLinearMap.id ℂ E) x‖ = ‖G w‖ := by simp [hG]
    _ ≤ B * ‖x‖ / ρ' * ‖w‖ := hS
    _ = derivConst ρ * ‖w‖ * ‖x‖ := by
        rw [derivConst, ← hρ'def, ← hB]; ring

/-- `h - id` is Lipschitz with constant `C m` on `closedBall 0 m`. -/
theorem IsCaratheodory.norm_sub_sub_le (hg : IsCaratheodory g) {ρ m : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < 1) (hm : m ≤ ρ) {w₁ w₂ : E} (h₁ : ‖w₁‖ ≤ m) (h₂ : ‖w₂‖ ≤ m) :
    ‖(g w₁ - w₁) - (g w₂ - w₂)‖ ≤ derivConst ρ * m * ‖w₁ - w₂‖ := by
  have hsub : closedBall (0 : E) m ⊆ unitBall E := closedBall_subset_ball (by linarith)
  have hD : ∀ x ∈ closedBall (0 : E) m,
      HasFDerivAt (fun w => g w - w) (fderiv ℂ g x - ContinuousLinearMap.id ℂ E) x :=
    fun x hx => ((hg.isNormalized.differentiableAt (hsub hx)).hasFDerivAt).sub (hasFDerivAt_id x)
  refine (convex_closedBall (0 : E) m).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (f := fun w => g w - w) (fun x hx => (hD x hx).differentiableAt) (fun x hx => ?_)
    (mem_closedBall_zero_iff.mpr h₂) (mem_closedBall_zero_iff.mpr h₁)
  rw [(hD x hx).fderiv]
  have hx : ‖x‖ ≤ m := mem_closedBall_zero_iff.mp hx
  refine (hg.norm_fderiv_sub_id_le hρ0 hρ (hx.trans hm)).trans ?_
  exact mul_le_mul_of_nonneg_left hx (derivConst_nonneg hρ0 hρ)

end Deriv

/-! ### Injectivity -/

namespace IsParametricRep

/-- **Lower bound for the separation of two trajectories.** -/
theorem norm_sub_ge (hf : IsParametricRep f h v) {z₁ z₂ : E} (hz₁ : z₁ ∈ unitBall E)
    (hz₂ : z₂ ∈ unitBall E) {T : ℝ} (hT : 0 ≤ T) :
    ‖z₁ - z₂‖ * Real.exp (-(derivConst (max ‖z₁‖ ‖z₂‖) *
        (max ‖z₁‖ ‖z₂‖ / (1 - max ‖z₁‖ ‖z₂‖) ^ 2))) ≤
      Real.exp T * ‖v T z₁ - v T z₂‖ := by
  have hh := hf.herglotz
  have hv := hf.solution
  set ρ := max ‖z₁‖ ‖z₂‖ with hρdef
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (norm_nonneg _)
  have hρ1 : ρ < 1 := max_lt (mem_unitBall.mp hz₁) (mem_unitBall.mp hz₂)
  set C := derivConst ρ with hCdef
  have hC0 : 0 ≤ C := derivConst_nonneg hρ0 hρ1
  set c := ρ / (1 - ρ) ^ 2 with hcdef
  have hc0 : 0 ≤ c := by
    have : 0 < 1 - ρ := by linarith
    positivity
  -- decay of both trajectories
  have hdec : ∀ z ∈ unitBall E, ‖z‖ ≤ ρ → ∀ τ, 0 ≤ τ → ‖v τ z‖ ≤ Real.exp (-τ) * c := by
    intro z hz hzρ τ hτ
    refine (hv.norm_le_exp hh hz hτ).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    have : 0 < 1 - ρ := by linarith
    have h1 : 0 < 1 - ‖z‖ := by linarith
    rw [hcdef]
    gcongr
  have hd₁ := hdec z₁ hz₁ (le_max_left _ _)
  have hd₂ := hdec z₂ hz₂ (le_max_right _ _)
  -- the squared distance `ψ`
  set Δ : ℝ → E := fun τ => v τ z₁ - v τ z₂ with hΔ
  have hlip₁ := (hv.lipschitzOnWith_Ici hh hz₁).mono
    (show uIcc 0 T ⊆ Ici 0 by rw [uIcc_of_le hT]; exact Icc_subset_Ici_self)
  have hlip₂ := (hv.lipschitzOnWith_Ici hh hz₂).mono
    (show uIcc 0 T ⊆ Ici 0 by rw [uIcc_of_le hT]; exact Icc_subset_Ici_self)
  have hΔlip : LipschitzOnWith ((4 * ‖z₁‖ / (1 - ‖z₁‖) ^ 2).toNNReal +
      (4 * ‖z₂‖ / (1 - ‖z₂‖) ^ 2).toNNReal) Δ (uIcc 0 T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    have e1 := hlip₁.dist_le_mul a ha b hb
    have e2 := hlip₂.dist_le_mul a ha b hb
    calc dist (Δ a) (Δ b) ≤ dist (v a z₁) (v b z₁) + dist (v a z₂) (v b z₂) := by
          simp only [hΔ]
          rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
          calc ‖v a z₁ - v a z₂ - (v b z₁ - v b z₂)‖ =
              ‖(v a z₁ - v b z₁) - (v a z₂ - v b z₂)‖ := by congr 1; abel
            _ ≤ ‖v a z₁ - v b z₁‖ + ‖v a z₂ - v b z₂‖ := norm_sub_le _ _
      _ ≤ _ := by push_cast; nlinarith
  have hΔbd : ∀ τ ∈ uIcc 0 T, ‖Δ τ‖ ≤ 2 := by
    intro τ hτ
    rw [uIcc_of_le hT] at hτ
    calc ‖Δ τ‖ ≤ ‖v τ z₁‖ + ‖v τ z₂‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add ((hv.norm_le hh hz₁ hτ.1).trans (mem_unitBall.mp hz₁).le)
          ((hv.norm_le hh hz₂ hτ.1).trans (mem_unitBall.mp hz₂).le)
      _ = 2 := by norm_num
  have hψac := absolutelyContinuousOnInterval_norm_sq (by norm_num : (0 : ℝ) ≤ 2) hΔlip hΔbd
  -- the weight `exp K(τ)`, `K(τ) = 2τ + 2Cc(1 - e^{-τ})`
  set K : ℝ → ℝ := fun τ => 2 * τ + 2 * C * c * (1 - Real.exp (-τ)) with hK
  have hKd : ∀ τ, HasDerivAt K (2 + 2 * C * c * Real.exp (-τ)) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => 2 * τ) 2 τ := by
      simpa using (hasDerivAt_id τ).const_mul (2 : ℝ)
    have h2 : HasDerivAt (fun τ : ℝ => 1 - Real.exp (-τ)) (Real.exp (-τ)) τ := by
      simpa using ((hasDerivAt_neg τ).exp).const_sub (1 : ℝ)
    have h3 := h1.add (h2.const_mul (2 * C * c))
    rw [hK]
    convert h3 using 1
  have hKc : ContDiff ℝ 1 K := by
    rw [hK]
    fun_prop
  have hEac : AbsolutelyContinuousOnInterval (fun τ => Real.exp (K τ)) 0 T :=
    ContDiffOn.absolutelyContinuousOnInterval (hKc.exp).contDiffOn
  have hmono := AbsolutelyContinuousOnInterval.le_of_ae_deriv_nonneg hT (hEac.fun_mul hψac)
    (F' := fun τ => Real.exp (K τ) * (2 + 2 * C * c * Real.exp (-τ)) * ‖Δ τ‖ ^ 2 +
      Real.exp (K τ) * (2 * (⟪Δ τ, -h τ (v τ z₁) - -h τ (v τ z₂)⟫_ℂ).re)) (by
      filter_upwards [hv.ae_hasDerivAt hz₁ hT, hv.ae_hasDerivAt hz₂ hT] with τ hτ₁ hτ₂ hτI
      have hψd := hasDerivAt_norm_sq ((hτ₁ hτI).sub (hτ₂ hτI))
      refine ⟨((hKd τ).exp).fun_mul hψd, ?_⟩
      -- the derivative is nonnegative
      have hτ0 : 0 ≤ τ := hτI.1.le
      set m := Real.exp (-τ) * c with hm
      have hm1 : ‖v τ z₁‖ ≤ m := hd₁ τ hτ0
      have hm2 : ‖v τ z₂‖ ≤ m := hd₂ τ hτ0
      have hmρ : min m ρ ≤ ρ := min_le_right _ _
      have hn1 : ‖v τ z₁‖ ≤ min m ρ := le_min hm1 ((hv.norm_le hh hz₁ hτ0).trans (le_max_left _ _))
      have hn2 : ‖v τ z₂‖ ≤ min m ρ := le_min hm2 ((hv.norm_le hh hz₂ hτ0).trans (le_max_right _ _))
      have hφ := (hh.isCaratheodory τ hτ0).norm_sub_sub_le hρ0 hρ1 hmρ hn1 hn2
      have hsplit : -h τ (v τ z₁) - -h τ (v τ z₂) =
          -(Δ τ + ((h τ (v τ z₁) - v τ z₁) - (h τ (v τ z₂) - v τ z₂))) := by
        simp only [hΔ]; abel
      have hre : (⟪Δ τ, -h τ (v τ z₁) - -h τ (v τ z₂)⟫_ℂ).re ≥
          -(1 + C * m) * ‖Δ τ‖ ^ 2 := by
        have h1 : (⟪Δ τ, Δ τ⟫_ℂ).re = ‖Δ τ‖ ^ 2 := by
          simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (Δ τ)
        rw [hsplit, inner_neg_right, inner_add_right, Complex.neg_re, Complex.add_re, h1]
        have h2 := (Complex.re_le_norm (⟪Δ τ, (h τ (v τ z₁) - v τ z₁) -
          (h τ (v τ z₂) - v τ z₂)⟫_ℂ)).trans (norm_inner_le_norm _ _)
        have h3 : ‖(h τ (v τ z₁) - v τ z₁) - (h τ (v τ z₂) - v τ z₂)‖ ≤ C * m * ‖Δ τ‖ :=
          hφ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_left _ _) hC0)
            (norm_nonneg _))
        have h4 : ‖Δ τ‖ * ‖(h τ (v τ z₁) - v τ z₁) - (h τ (v τ z₂) - v τ z₂)‖ ≤
            ‖Δ τ‖ * (C * m * ‖Δ τ‖) := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        nlinarith
      have hE := Real.exp_pos (K τ)
      have hm' : C * m = C * c * Real.exp (-τ) := by rw [hm]; ring
      rw [hm'] at hre
      have : 0 ≤ (2 + 2 * C * c * Real.exp (-τ)) * ‖Δ τ‖ ^ 2 +
          2 * (⟪Δ τ, -h τ (v τ z₁) - -h τ (v τ z₂)⟫_ℂ).re := by nlinarith
      nlinarith)
  -- evaluate
  have hK0 : K 0 = 0 := by simp [hK]
  have hΔ0 : Δ 0 = z₁ - z₂ := by simp [hΔ, hv.apply_zero hz₁, hv.apply_zero hz₂]
  simp only [hK0, Real.exp_zero, one_mul, hΔ0] at hmono
  -- `e^{2T} ‖Δ T‖² ≥ e^{-2Cc} ‖z₁ - z₂‖²`
  have hKT : K T ≤ 2 * T + 2 * C * c := by
    simp only [hK]
    have : 0 ≤ 2 * C * c * Real.exp (-T) := by positivity
    nlinarith
  have h1 : ‖z₁ - z₂‖ ^ 2 ≤ Real.exp (2 * T + 2 * C * c) * ‖Δ T‖ ^ 2 :=
    hmono.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hKT) (by positivity))
  have h2 : (‖z₁ - z₂‖ * Real.exp (-(C * c))) ^ 2 ≤ (Real.exp T * ‖Δ T‖) ^ 2 := by
    have e1 : Real.exp (2 * T + 2 * C * c) = Real.exp T ^ 2 * Real.exp (C * c) ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    have e2 : Real.exp (-(C * c)) ^ 2 * Real.exp (C * c) ^ 2 = 1 := by
      rw [← mul_pow, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_pow]
    rw [e1] at h1
    have e3 : (‖z₁ - z₂‖ * Real.exp (-(C * c))) ^ 2 =
        ‖z₁ - z₂‖ ^ 2 * Real.exp (-(C * c)) ^ 2 := by ring
    rw [e3]
    have h5 : 0 ≤ Real.exp (-(C * c)) ^ 2 := by positivity
    calc ‖z₁ - z₂‖ ^ 2 * Real.exp (-(C * c)) ^ 2
        ≤ Real.exp T ^ 2 * Real.exp (C * c) ^ 2 * ‖Δ T‖ ^ 2 * Real.exp (-(C * c)) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 h5
      _ = (Real.exp T * ‖Δ T‖) ^ 2 * (Real.exp (-(C * c)) ^ 2 * Real.exp (C * c) ^ 2) := by
          ring
      _ = (Real.exp T * ‖Δ T‖) ^ 2 := by rw [e2, mul_one]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2

/-- **`f` is injective on `𝔹`.** -/
theorem injOn (hf : IsParametricRep f h v) : InjOn f (unitBall E) := by
  intro z₁ hz₁ z₂ hz₂ heq
  by_contra hne
  have hpos : 0 < ‖z₁ - z₂‖ * Real.exp (-(derivConst (max ‖z₁‖ ‖z₂‖) *
      (max ‖z₁‖ ‖z₂‖ / (1 - max ‖z₁‖ ‖z₂‖) ^ 2))) :=
    mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) (Real.exp_pos _)
  -- `eᵗ (v(z₁, t) - v(z₂, t)) → f z₁ - f z₂ = 0`
  have hlim : Tendsto (fun t => Real.exp t * ‖v t z₁ - v t z₂‖) atTop (𝓝 ‖f z₁ - f z₂‖) := by
    refine ((hf.tendsto z₁ hz₁).sub (hf.tendsto z₂ hz₂)).norm.congr' ?_
    filter_upwards with t
    rw [← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos t)]
  rw [heq, sub_self, norm_zero] at hlim
  have := ge_of_tendsto hlim (Eventually.mono (eventually_ge_atTop 0)
    fun T hT => hf.norm_sub_ge hz₁ hz₂ hT)
  linarith

/-- **Maps with parametric representation are univalent.** -/
theorem mem_classS (hf : IsParametricRep f h v) : f ∈ classS E :=
  ⟨hf.isNormalized, hf.injOn⟩

end IsParametricRep

/-- **`S⁰(𝔹) ⊆ S(𝔹)`** [GHK02]. -/
theorem mem_classS_of_mem_classS0 (hf : f ∈ classS0 E) : f ∈ classS E :=
  let ⟨_, _, hrep⟩ := hf
  hrep.mem_classS

end LoewnerS0
