import LoewnerS0.SCV
import LoewnerS0.TaylorRec
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Estimates for the Carathéodory class `M(𝔹)`

For `h ∈ M(𝔹)` on the unit ball of a complex inner product space:

* `IsCaratheodory.re_inner_ge`, `IsCaratheodory.re_inner_le`, `IsCaratheodory.norm_inner_le`
  (Pfaltzgraff): `‖z‖²(1-‖z‖)/(1+‖z‖) ≤ Re ⟨h(z), z⟩ ≤ ‖z‖²(1+‖z‖)/(1-‖z‖)` and
  `|⟨h(z), z⟩| ≤ ‖z‖²(1+‖z‖)/(1-‖z‖)`;
* `IsCaratheodory.norm_inner_homPart_le`: the homogeneous terms `P_m = D^m h(0)/m!` satisfy
  `|⟨P_m(x), x⟩| ≤ 2‖x‖^{m+1}` for `m ≥ 2`;
* `IsCaratheodory.norm_homPart_le`: `‖P_m(u)‖ ≤ 4m` for unit vectors `u`;
* `IsCaratheodory.norm_le`: the growth estimate `‖h(z)‖ ≤ 4‖z‖/(1-‖z‖)²` [GHK02, Theorem 1.2]
  (finite dimension);
* `IsCaratheodory.norm_sub_le`: `‖h(z) - z‖ ≤ 8‖z‖²/(1-‖z‖)²`;
* `IsCaratheodory.norm_fderiv_le`, `IsCaratheodory.lipschitzOnWith`: `‖Dh(z)‖ ≤ 32/(1-ρ)³` on
  `closedBall 0 ρ`, so `h` is Lipschitz there with a constant that depends only on `ρ`.

The one-variable input is the theory of Carathéodory functions `q` (holomorphic on the unit disc,
`q(0) = 1`, `Re q > 0`): the Schwarz lemma applied to `(q-1)/(q+1)` gives the two-sided bounds
(`caratheodory_bounds`), and the coefficient bound `|q^{(k)}(0)/k!| ≤ 2` follows from the circle
averages of `ζ^{-k}(q + q̄)` (`norm_coeff_le_two`). They are applied to the slices
`q(ζ) = ⟨h(ζu), u⟩/ζ`.

For the norm of `P_m(u)` we use that `⟨P_m(x), x⟩` is bounded on spheres and extract the
component of `P_m(u)` orthogonal to `u` by the maximum modulus principle applied to
`λ ↦ λ⟨P_m(u + λw), u⟩ + s²⟨P_m(u + λw), w⟩`, which equals `λ⟨P_m(x), x⟩` on `|λ| = s`
(`norm_le_of_norm_inner_le`). Summing `‖P_m(u)‖ r^m ≤ 4m r^m` gives the growth estimate.
-/

open Complex Metric Set Filter Real
open scoped InnerProductSpace Topology Real

noncomputable section

namespace LoewnerS0

/-! ### Carathéodory functions of one variable -/

section OneVariable

/-- **Bounds for Carathéodory functions**: if `q` is holomorphic on the unit disc with `q(0) = 1`
and `Re q > 0`, then `(1-|ζ|)/(1+|ζ|) ≤ Re q(ζ)` and `|q(ζ)| ≤ (1+|ζ|)/(1-|ζ|)`. -/
theorem caratheodory_bounds {q : ℂ → ℂ} (hd : DifferentiableOn ℂ q (ball 0 1)) (h0 : q 0 = 1)
    (hre : ∀ ζ ∈ ball (0 : ℂ) 1, 0 < (q ζ).re) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    (1 - ‖ζ‖) / (1 + ‖ζ‖) ≤ (q ζ).re ∧ ‖q ζ‖ ≤ (1 + ‖ζ‖) / (1 - ‖ζ‖) := by
  have hne : ∀ ξ ∈ ball (0 : ℂ) 1, q ξ + 1 ≠ 0 := by
    intro ξ hξ h
    have h1 := hre ξ hξ
    have h2 : (q ξ + 1).re = 0 := by rw [h, Complex.zero_re]
    rw [Complex.add_re, Complex.one_re] at h2
    linarith
  set ω : ℂ → ℂ := fun ξ => (q ξ - 1) / (q ξ + 1) with hω_def
  have hωd : DifferentiableOn ℂ ω (ball 0 1) := (hd.sub_const 1).div (hd.add_const 1) hne
  have hω0 : ω 0 = 0 := by simp [hω_def, h0]
  have hle : ∀ ξ ∈ ball (0 : ℂ) 1, ‖q ξ - 1‖ ≤ ‖q ξ + 1‖ := by
    intro ξ hξ
    have h1 := hre ξ hξ
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero,
      Complex.add_re, Complex.add_im, add_zero]
    nlinarith
  have hωmaps : MapsTo ω (ball 0 1) (closedBall 0 1) := by
    intro ξ hξ
    rw [mem_closedBall_zero_iff, hω_def]
    simp only
    rw [norm_div, div_le_one (norm_pos_iff.mpr (hne ξ hξ))]
    exact hle ξ hξ
  have hsch : ‖ω ζ‖ ≤ ‖ζ‖ := Complex.norm_le_norm_of_mapsTo_ball hωd hωmaps hω0 hζ
  have hζB : ζ ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hζ
  set w := ω ζ with hw
  have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hsch hζ
  have h1w : (1 : ℂ) - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hw1
    exact lt_irrefl _ hw1
  have hqw : q ζ = (1 + w) / (1 - w) := by
    have hq1 := hne ζ hζB
    rw [eq_div_iff h1w, hw, hω_def]
    simp only
    field_simp
    ring
  set t := ‖w‖ with ht
  set r := ‖ζ‖ with hr
  have ht0 : 0 ≤ t := norm_nonneg _
  have hr0 : 0 ≤ r := norm_nonneg _
  have htr : t ≤ r := hsch
  constructor
  · -- `Re q = (1 - |w|²)/|1 - w|²`
    have hD : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr h1w
    have hre_eq : (q ζ).re = (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
      rw [hqw, Complex.div_re]
      simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
        Complex.sub_im, zero_add, zero_sub, Complex.normSq_apply]
      field_simp
      ring
    have hnw : Complex.normSq w = t ^ 2 := by rw [ht, Complex.sq_norm]
    have hD' : Complex.normSq (1 - w) ≤ (1 + t) ^ 2 := by
      rw [← Complex.sq_norm]
      have : ‖(1 : ℂ) - w‖ ≤ 1 + t := by
        calc ‖(1 : ℂ) - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
          _ = 1 + t := by rw [norm_one]
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    rw [hre_eq, hnw, div_le_div_iff₀ (by linarith) hD]
    have h1 : (1 - r) * Complex.normSq (1 - w) ≤ (1 - r) * (1 + t) ^ 2 :=
      mul_le_mul_of_nonneg_left hD' (by linarith)
    have h2 : (1 - r) * (1 + t) ^ 2 ≤ (1 - t ^ 2) * (1 + r) := by nlinarith
    linarith
  · have h1 : ‖(1 : ℂ) + w‖ ≤ 1 + t := by
      calc ‖(1 : ℂ) + w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_add_le _ _
        _ = 1 + t := by rw [norm_one]
    have h2 : 1 - t ≤ ‖(1 : ℂ) - w‖ := by
      calc 1 - t = ‖(1 : ℂ)‖ - ‖w‖ := by rw [norm_one]
        _ ≤ ‖(1 : ℂ) - w‖ := norm_sub_norm_le _ _
    have ht1 : 0 < 1 - t := by linarith
    rw [hqw, norm_div, div_le_div_iff₀ (lt_of_lt_of_le ht1 h2) (by linarith)]
    calc ‖(1 : ℂ) + w‖ * (1 - r) ≤ (1 + t) * (1 - r) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ (1 + r) * (1 - t) := by nlinarith
      _ ≤ (1 + r) * ‖(1 : ℂ) - w‖ := mul_le_mul_of_nonneg_left h2 (by linarith)

lemma norm_circleAverage_le {g : ℂ → ℂ} {r : ℝ} :
    ‖circleAverage g 0 r‖ ≤ circleAverage (fun ζ => ‖g ζ‖) 0 r := by
  rw [circleAverage_def, circleAverage_def, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_integral_norm (by positivity)) (by positivity)

/-- The circle average of `ζ ↦ ζ^{-k} (ζ⁻¹ F(ζ))` is the coefficient `F^{(k+1)}(0)/(k+1)!`. -/
lemma circleAverage_coeff {F : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hF : DiffContOnCl ℂ F (ball 0 r))
    (k : ℕ) :
    circleAverage (fun ζ => (ζ ^ k)⁻¹ * (ζ⁻¹ * F ζ)) 0 r =
      iteratedDeriv (k + 1) F 0 / (k + 1).factorial := by
  rw [circleAverage_eq_circleIntegral hr.ne']
  have hcong : (∮ ζ in C(0, r), (ζ - 0)⁻¹ • ((ζ ^ k)⁻¹ * (ζ⁻¹ * F ζ))) =
      ∮ ζ in C(0, r), (1 / (ζ - 0) ^ (k + 1 + 1)) • F ζ := by
    apply circleIntegral.integral_congr hr.le
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := ne_of_mem_sphere hζ hr.ne'
    simp only [sub_zero, smul_eq_mul]
    field_simp
    ring
  rw [hcong, hF.circleIntegral_one_div_sub_center_pow_smul hr (k + 1), smul_smul, smul_eq_mul]
  have hpi : (2 * (π : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp

/-- **Carathéodory's coefficient bound**: if `F` is holomorphic on the unit disc, `F(0) = 0`,
`F'(0) = 1` and `Re (F(ζ)/ζ) > 0` for `0 < |ζ| < 1`, then `|F^{(k+1)}(0)/(k+1)!| ≤ 2` for
`k ≥ 1`. -/
theorem norm_coeff_le_two {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F (ball 0 1)) (h0 : F 0 = 0)
    (h1 : deriv F 0 = 1) (hre : ∀ ζ ∈ ball (0 : ℂ) 1, ζ ≠ 0 → 0 < (ζ⁻¹ * F ζ).re) {k : ℕ}
    (hk : 1 ≤ k) : ‖iteratedDeriv (k + 1) F 0 / (k + 1).factorial‖ ≤ 2 := by
  set c := iteratedDeriv (k + 1) F 0 / (k + 1).factorial with hc
  -- the estimate on the circle of radius `r`
  have key : ∀ r : ℝ, 0 < r → r < 1 → ‖c‖ * r ^ k ≤ 2 := by
    intro r hr hr1
    have hF : DiffContOnCl ℂ F (ball 0 r) := hd.diffContOnCl_ball (closedBall_subset_ball hr1)
    have hFc : ContinuousOn F (sphere (0 : ℂ) r) :=
      hd.continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hr1))
    have hsph : ∀ ζ ∈ sphere (0 : ℂ) r, ζ ≠ 0 := fun ζ hζ => ne_of_mem_sphere hζ hr.ne'
    have hsphB : ∀ ζ ∈ sphere (0 : ℂ) r, ζ ∈ ball (0 : ℂ) 1 := fun ζ hζ =>
      closedBall_subset_ball hr1 (sphere_subset_closedBall hζ)
    have hnorm : ∀ ζ ∈ sphere (0 : ℂ) r, ‖ζ‖ = r := fun ζ hζ => by simpa using hζ
    -- `Q = ζ⁻¹ F` on the circle
    set Q : ℂ → ℂ := fun ζ => ζ⁻¹ * F ζ with hQ
    have hQc : ContinuousOn Q (sphere (0 : ℂ) r) :=
      (continuousOn_inv₀.mono fun ζ hζ => hsph ζ hζ).mul hFc
    have habs : |r| = r := abs_of_pos hr
    -- (a) the coefficient
    have ha : circleAverage (fun ζ => (ζ ^ k)⁻¹ * Q ζ) 0 r = c := circleAverage_coeff hr hF k
    -- (b) the average of `Q` is `1`
    have hb : circleAverage Q 0 r = 1 := by
      have := circleAverage_coeff hr hF 0
      simp only [pow_zero, inv_one, one_mul, zero_add, Nat.factorial_one, Nat.cast_one,
        div_one, iteratedDeriv_one, h1] at this
      exact this
    -- (c) the average of `ζ^k Q` vanishes
    have hcc : circleAverage (fun ζ => ζ ^ k * Q ζ) 0 r = 0 := by
      have hG : DiffContOnCl ℂ (fun ζ => ζ ^ (k - 1) * F ζ) (ball 0 |r|) := by
        rw [habs]
        exact ((differentiable_id.pow (k - 1)).differentiableOn.mul hd).diffContOnCl_ball
          (closedBall_subset_ball hr1)
      rw [circleAverage_congr_sphere (f₂ := fun ζ => ζ ^ (k - 1) * F ζ), hG.circleAverage]
      · simp [h0]
      · intro ζ hζ
        rw [habs] at hζ
        have hζ0 := hsph ζ hζ
        simp only [hQ]
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        field_simp
        ring
    -- (d) the conjugate part
    have hcircle_int : ∀ g : ℂ → ℂ, ContinuousOn g (sphere (0 : ℂ) r) → CircleIntegrable g 0 r :=
      fun g hg => hg.circleIntegrable hr.le
    have hpowc : ContinuousOn (fun ζ : ℂ => (ζ ^ k)⁻¹) (sphere (0 : ℂ) r) :=
      (continuousOn_inv₀.comp (continuous_pow k).continuousOn fun ζ hζ =>
        pow_ne_zero k (hsph ζ hζ))
    have hd' : circleAverage (fun ζ => (ζ ^ k)⁻¹ * (starRingEnd ℂ) (Q ζ)) 0 r = 0 := by
      have h1' : circleAverage ((Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ fun ζ => ζ ^ k * Q ζ) 0 r = 0 := by
        rw [ContinuousLinearMap.circleAverage_comp_comm _
          (hcircle_int (fun ζ => ζ ^ k * Q ζ) ((continuous_pow k).continuousOn.mul hQc)), hcc,
          map_zero]
      have hcongr : circleAverage (fun ζ => (ζ ^ k)⁻¹ * (starRingEnd ℂ) (Q ζ)) 0 r =
          circleAverage (fun ζ => ((r ^ (2 * k) : ℝ)⁻¹ : ℂ) *
            ((Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ fun ζ => ζ ^ k * Q ζ) ζ) 0 r := by
        apply circleAverage_congr_sphere
        intro ζ hζ
        rw [habs] at hζ
        have hζ0 := hsph ζ hζ
        have hconj : (starRingEnd ℂ) ζ = (r ^ 2 : ℝ) / ζ := by
          rw [eq_div_iff hζ0, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm ζ hζ]
        simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
          map_mul, map_pow, hconj]
        have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
        push_cast
        rw [div_pow, ← pow_mul]
        field_simp
        try ring
      rw [hcongr]
      have : circleAverage (fun ζ => ((r ^ (2 * k) : ℝ)⁻¹ : ℂ) *
          ((Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ fun ζ => ζ ^ k * Q ζ) ζ) 0 r =
          ((r ^ (2 * k) : ℝ)⁻¹ : ℂ) • circleAverage
            ((Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ fun ζ => ζ ^ k * Q ζ) 0 r :=
        circleAverage_smul (a := ((r ^ (2 * k) : ℝ)⁻¹ : ℂ))
      rw [this, h1', smul_zero]
    -- (e) the average of `ζ^{-k} (Q + Q̄) = ζ^{-k} 2 Re Q`
    have he : circleAverage (fun ζ => (ζ ^ k)⁻¹ * ((2 * (Q ζ).re : ℝ) : ℂ)) 0 r = c := by
      have hsum : circleAverage (fun ζ => (ζ ^ k)⁻¹ * ((2 * (Q ζ).re : ℝ) : ℂ)) 0 r =
          circleAverage ((fun ζ => (ζ ^ k)⁻¹ * Q ζ) +
            fun ζ => (ζ ^ k)⁻¹ * (starRingEnd ℂ) (Q ζ)) 0 r := by
        apply circleAverage_congr_sphere
        intro ζ _
        simp only [Pi.add_apply, ← mul_add, Complex.add_conj]
        try push_cast
        try ring
      rw [hsum, circleAverage_add (hcircle_int (fun ζ => (ζ ^ k)⁻¹ * Q ζ) (hpowc.mul hQc))
        (hcircle_int (fun ζ => (ζ ^ k)⁻¹ * (starRingEnd ℂ) (Q ζ))
          (hpowc.mul (Complex.continuous_conj.comp_continuousOn hQc))), ha, hd', add_zero]
    -- (f) estimate
    have hRe : circleAverage (fun ζ => (Q ζ).re) 0 r = 1 := by
      have := ContinuousLinearMap.circleAverage_comp_comm (Complex.reCLM) (hcircle_int _ hQc)
      simp only [Complex.reCLM_apply] at this
      rw [show (fun ζ => (Q ζ).re) = (Complex.reCLM ∘ Q) from rfl, this, hb, Complex.one_re]
    have hpos : ∀ ζ ∈ sphere (0 : ℂ) r, 0 < (Q ζ).re := fun ζ hζ => hre ζ (hsphB ζ hζ) (hsph ζ hζ)
    calc ‖c‖ * r ^ k
        = ‖circleAverage (fun ζ => (ζ ^ k)⁻¹ * ((2 * (Q ζ).re : ℝ) : ℂ)) 0 r‖ * r ^ k := by rw [he]
      _ ≤ circleAverage (fun ζ => ‖(ζ ^ k)⁻¹ * ((2 * (Q ζ).re : ℝ) : ℂ)‖) 0 r * r ^ k :=
          mul_le_mul_of_nonneg_right norm_circleAverage_le (by positivity)
      _ = circleAverage (fun ζ => (r ^ k)⁻¹ * (2 * (Q ζ).re)) 0 r * r ^ k := by
          congr 1
          apply circleAverage_congr_sphere
          intro ζ hζ
          rw [habs] at hζ
          show ‖(ζ ^ k)⁻¹ * ((2 * (Q ζ).re : ℝ) : ℂ)‖ = (r ^ k)⁻¹ * (2 * (Q ζ).re)
          rw [norm_mul, norm_inv, norm_pow, hnorm ζ hζ, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith [hpos ζ hζ])]
      _ = (r ^ k)⁻¹ * 2 * circleAverage (fun ζ => (Q ζ).re) 0 r * r ^ k := by
          rw [show (fun ζ => (r ^ k)⁻¹ * (2 * (Q ζ).re)) = ((r ^ k)⁻¹ * 2) • fun ζ => (Q ζ).re by
            funext ζ; simp [smul_eq_mul]; ring]
          rw [circleAverage_smul, smul_eq_mul]
      _ = 2 := by
          rw [hRe]
          field_simp
  -- let `r → 1`
  have hlim : Tendsto (fun r : ℝ => ‖c‖ * r ^ k) (𝓝[<] 1) (𝓝 (‖c‖ * 1 ^ k)) :=
    ((continuous_const.mul (continuous_pow k)).tendsto 1).mono_left nhdsWithin_le_nhds
  rw [one_pow, mul_one] at hlim
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact key r hr.1 hr.2

end OneVariable

/-! ### Slices of `h ∈ M(𝔹)` -/

section Slice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {h : E → E}

/-- The slice function `ζ ↦ ⟪u, h(ζ u)⟫`. -/
def sliceF (h : E → E) (u : E) (ζ : ℂ) : ℂ := ⟪u, h (ζ • u)⟫_ℂ

lemma mapsTo_smul_unitBall {u : E} (hu : ‖u‖ ≤ 1) :
    MapsTo (fun ζ : ℂ => ζ • u) (ball 0 1) (unitBall E) := by
  intro ζ hζ
  rw [mem_ball_zero_iff] at hζ
  rw [mem_unitBall, norm_smul]
  calc ‖ζ‖ * ‖u‖ ≤ ‖ζ‖ * 1 := mul_le_mul_of_nonneg_left hu (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact hζ

lemma IsNormalized.differentiableOn_sliceF (hN : IsNormalized h) {u : E} (hu : ‖u‖ ≤ 1) :
    DifferentiableOn ℂ (sliceF h u) (ball 0 1) :=
  (innerSL ℂ u).differentiable.comp_differentiableOn
    (hN.differentiableOn.comp (differentiable_id.smul_const u).differentiableOn
      (mapsTo_smul_unitBall hu))

lemma IsNormalized.sliceF_zero (hN : IsNormalized h) (u : E) : sliceF h u 0 = 0 := by
  simp [sliceF, hN.map_zero]

lemma IsNormalized.hasDerivAt_sliceF_zero (hN : IsNormalized h) (u : E) :
    HasDerivAt (sliceF h u) ⟪u, u⟫_ℂ 0 := by
  have h1 : HasFDerivAt h (ContinuousLinearMap.id ℂ E) ((0 : ℂ) • u) := by
    simpa using hN.hasFDerivAt_zero
  have h2 : HasDerivAt (fun ζ : ℂ => ζ • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const u
  have h3 := (innerSL ℂ u).hasFDerivAt.comp_hasDerivAt (0 : ℂ) (h1.comp_hasDerivAt (0 : ℂ) h2)
  have h4 : (innerSL ℂ u) ((ContinuousLinearMap.id ℂ E) u) = ⟪u, u⟫_ℂ := by simp
  rw [h4] at h3
  exact h3

lemma IsCaratheodory.differentiableOn_sliceF (hh : IsCaratheodory h) {u : E} (hu : ‖u‖ ≤ 1) :
    DifferentiableOn ℂ (sliceF h u) (ball 0 1) :=
  hh.isNormalized.differentiableOn_sliceF hu

lemma IsCaratheodory.sliceF_zero (hh : IsCaratheodory h) (u : E) : sliceF h u 0 = 0 :=
  hh.isNormalized.sliceF_zero u

lemma IsCaratheodory.hasDerivAt_sliceF_zero (hh : IsCaratheodory h) (u : E) :
    HasDerivAt (sliceF h u) ⟪u, u⟫_ℂ 0 :=
  hh.isNormalized.hasDerivAt_sliceF_zero u

lemma IsCaratheodory.re_inv_mul_sliceF_pos (hh : IsCaratheodory h) {u : E} (hu : ‖u‖ ≤ 1)
    (hu0 : u ≠ 0) {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) (hζ0 : ζ ≠ 0) :
    0 < (ζ⁻¹ * sliceF h u ζ).re := by
  have hz : ζ • u ∈ unitBall E := mapsTo_smul_unitBall hu hζ
  have hz0 : ζ • u ≠ 0 := smul_ne_zero hζ0 hu0
  have hpos := hh.re_inner_pos _ hz hz0
  rw [inner_smul_left] at hpos
  have : ζ⁻¹ * sliceF h u ζ =
      (((Complex.normSq ζ)⁻¹ : ℝ) : ℂ) * ((starRingEnd ℂ) ζ * sliceF h u ζ) := by
    rw [Complex.inv_def]; ring
  rw [this, Complex.re_ofReal_mul]
  exact mul_pos (inv_pos.mpr (Complex.normSq_pos.mpr hζ0)) hpos

/-- For a unit vector `u`, `q(ζ) = ⟪u, h(ζ u)⟫/ζ` is a Carathéodory function. -/
lemma IsCaratheodory.caratheodory_slice (hh : IsCaratheodory h) {u : E} (hu : ‖u‖ = 1) :
    DifferentiableOn ℂ (dslope (sliceF h u) 0) (ball 0 1) ∧ dslope (sliceF h u) 0 0 = 1 ∧
      (∀ ζ ∈ ball (0 : ℂ) 1, 0 < (dslope (sliceF h u) 0 ζ).re) ∧
      ∀ ζ : ℂ, ζ ≠ 0 → dslope (sliceF h u) 0 ζ = ζ⁻¹ * sliceF h u ζ := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have huu : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; simp
  have hdiff := hh.differentiableOn_sliceF hu.le
  have heq : ∀ ζ : ℂ, ζ ≠ 0 → dslope (sliceF h u) 0 ζ = ζ⁻¹ * sliceF h u ζ := by
    intro ζ hζ
    rw [dslope_of_ne _ hζ, slope_def_field, hh.sliceF_zero, sub_zero, sub_zero, div_eq_inv_mul]
  have h0 : dslope (sliceF h u) 0 0 = 1 := by
    rw [dslope_same, (hh.hasDerivAt_sliceF_zero u).deriv, huu]
  refine ⟨(differentiableOn_dslope (ball_mem_nhds 0 one_pos)).mpr hdiff, h0, ?_, heq⟩
  intro ζ hζ
  rcases eq_or_ne ζ 0 with rfl | hζ0
  · rw [h0, Complex.one_re]; exact one_pos
  · rw [heq ζ hζ0]
    exact hh.re_inv_mul_sliceF_pos hu.le hu0 hζ hζ0

/-- **Minimum principle.** A normalized holomorphic map `h` with `Re ⟨h(z), z⟩ ≥ 0` on `𝔹` belongs
to `M(𝔹)`: the inequality is automatically strict for `z ≠ 0`. On the slice through `z = ρu`, the
function `q(ζ) = ⟪u, h(ζu)⟫/ζ` is holomorphic on the unit disc with `Re q ≥ 0` and `q(0) = 1`; if
`Re q(ρ) = 0`, then `|exp(-q)| ≤ 1` would attain its maximum at `ρ`, so `exp(-q)` would be
constant (maximum modulus principle), contradicting `|exp(-q(0))| = e⁻¹ < 1`. -/
theorem IsNormalized.isCaratheodory_of_re_inner_nonneg (hN : IsNormalized h)
    (hre : ∀ z ∈ unitBall E, 0 ≤ (⟪z, h z⟫_ℂ).re) : IsCaratheodory h := by
  refine ⟨hN, fun z hz hz0 => ?_⟩
  set ρ : ℝ := ‖z‖ with hρdef
  have hρ : 0 < ρ := norm_pos_iff.mpr hz0
  have hρ1 : ρ < 1 := by simpa using hz
  set u : E := ((ρ : ℂ)⁻¹) • z with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
      inv_mul_cancel₀ hρ.ne']
  have hzu : z = (ρ : ℂ) • u := by
    rw [hudef, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hρ.ne'), one_smul]
  have huu : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; simp
  set q := dslope (sliceF h u) 0 with hqdef
  have hdiff : DifferentiableOn ℂ q (ball 0 1) :=
    (differentiableOn_dslope (ball_mem_nhds 0 one_pos)).mpr (hN.differentiableOn_sliceF hu.le)
  have heq : ∀ ζ : ℂ, ζ ≠ 0 → q ζ = ζ⁻¹ * sliceF h u ζ := by
    intro ζ hζ
    rw [hqdef, dslope_of_ne _ hζ, slope_def_field, hN.sliceF_zero, sub_zero, sub_zero,
      div_eq_inv_mul]
  have h0 : q 0 = 1 := by
    rw [hqdef, dslope_same, (hN.hasDerivAt_sliceF_zero u).deriv, huu]
  -- `Re q ≥ 0` on the disc
  have hqre : ∀ ζ ∈ ball (0 : ℂ) 1, 0 ≤ (q ζ).re := by
    intro ζ hζ
    rcases eq_or_ne ζ 0 with rfl | hζ0
    · rw [h0, Complex.one_re]; exact zero_le_one
    · have hpos := hre _ (mapsTo_smul_unitBall hu.le hζ)
      rw [inner_smul_left] at hpos
      have : q ζ = (((Complex.normSq ζ)⁻¹ : ℝ) : ℂ) * ((starRingEnd ℂ) ζ * sliceF h u ζ) := by
        rw [heq ζ hζ0, Complex.inv_def]; ring
      rw [this, Complex.re_ofReal_mul]
      exact mul_nonneg (inv_nonneg.mpr (Complex.normSq_nonneg ζ)) hpos
  -- `⟪z, h z⟫ = ρ² q(ρ)`
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hzH : ⟪z, h z⟫_ℂ = ((ρ ^ 2 : ℝ) : ℂ) * q ρ := by
    rw [heq _ hρ0, sliceF, ← hzu]
    conv_lhs => rw [hzu]
    rw [inner_smul_left, Complex.conj_ofReal, ← hzu]
    push_cast
    field_simp
  rw [hzH, Complex.re_ofReal_mul]
  refine mul_pos (by positivity) ?_
  -- if `Re q(ρ) = 0`, then `|exp(-q)|` is maximal at `ρ`
  by_contra hle
  rw [not_lt] at hle
  have hρmem : (ρ : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]; exact hρ1
  have hqρ : (q ρ).re = 0 := le_antisymm hle (hqre _ hρmem)
  have hFd : DifferentiableOn ℂ (fun ζ => Complex.exp (-q ζ)) (ball 0 1) := hdiff.neg.cexp
  have hmax : IsMaxOn (norm ∘ fun ζ => Complex.exp (-q ζ)) (ball 0 1) (ρ : ℂ) := by
    rw [isMaxOn_iff]
    intro ζ hζ
    simp only [Function.comp_apply, Complex.norm_exp, Complex.neg_re, hqρ, neg_zero,
      Real.exp_zero]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hqre ζ hζ))
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (convex_ball (0 : ℂ) 1).isPreconnected isOpen_ball hFd hρmem hmax (mem_ball_self one_pos)
  have h1' : Complex.exp (-q 0) = Complex.exp (-q ρ) := hconst
  have h1 : ‖Complex.exp (-q 0)‖ = ‖Complex.exp (-q ρ)‖ := by rw [h1']
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re, Complex.neg_re, h0, hqρ,
    Complex.one_re, neg_zero, Real.exp_zero] at h1
  have h2 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

/-- **Pfaltzgraff's estimates** for `h ∈ M(𝔹)`:
`‖z‖²(1-‖z‖)/(1+‖z‖) ≤ Re ⟨h(z), z⟩` and `|⟨h(z), z⟩| ≤ ‖z‖²(1+‖z‖)/(1-‖z‖)`. -/
theorem IsCaratheodory.inner_bounds (hh : IsCaratheodory h) {z : E} (hz : z ∈ unitBall E) :
    ‖z‖ ^ 2 * (1 - ‖z‖) / (1 + ‖z‖) ≤ (⟪z, h z⟫_ℂ).re ∧
      ‖⟪z, h z⟫_ℂ‖ ≤ ‖z‖ ^ 2 * (1 + ‖z‖) / (1 - ‖z‖) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [hh.map_zero]
  set ρ : ℝ := ‖z‖ with hρdef
  have hρ : 0 < ρ := norm_pos_iff.mpr hz0
  have hρ1 : ρ < 1 := by simpa using hz
  set u : E := ((ρ : ℂ)⁻¹) • z with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
      inv_mul_cancel₀ hρ.ne']
  have hzu : z = (ρ : ℂ) • u := by
    rw [hudef, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hρ.ne'), one_smul]
  obtain ⟨hqd, hq0, hqre, hqeq⟩ := hh.caratheodory_slice hu
  have hb := caratheodory_bounds hqd hq0 hqre (ζ := (ρ : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]; exact hρ1)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at hb
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hzH : ⟪z, h z⟫_ℂ = ((ρ ^ 2 : ℝ) : ℂ) * dslope (sliceF h u) 0 ρ := by
    rw [hqeq _ hρ0, sliceF, ← hzu]
    conv_lhs => rw [hzu]
    rw [inner_smul_left, Complex.conj_ofReal, ← hzu]
    push_cast
    field_simp
  rw [hzH, Complex.re_ofReal_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  constructor
  · rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hb.1 (by positivity)
  · rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hb.2 (by positivity)

theorem IsCaratheodory.re_inner_ge (hh : IsCaratheodory h) {z : E} (hz : z ∈ unitBall E) :
    ‖z‖ ^ 2 * (1 - ‖z‖) / (1 + ‖z‖) ≤ (⟪z, h z⟫_ℂ).re :=
  (hh.inner_bounds hz).1

theorem IsCaratheodory.norm_inner_le (hh : IsCaratheodory h) {z : E} (hz : z ∈ unitBall E) :
    ‖⟪z, h z⟫_ℂ‖ ≤ ‖z‖ ^ 2 * (1 + ‖z‖) / (1 - ‖z‖) :=
  (hh.inner_bounds hz).2

theorem IsCaratheodory.re_inner_le (hh : IsCaratheodory h) {z : E} (hz : z ∈ unitBall E) :
    (⟪z, h z⟫_ℂ).re ≤ ‖z‖ ^ 2 * (1 + ‖z‖) / (1 - ‖z‖) :=
  (Complex.re_le_norm _).trans (hh.norm_inner_le hz)

end Slice

/-! ### The homogeneous expansion and the growth estimate -/

section Expansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {h : E → E}

/-- The `m`-th homogeneous term `P_m(x) = D^m h(0)(x, …, x)/m!` of `h` at `0`. -/
def homPart (h : E → E) (m : ℕ) (x : E) : E :=
  ((m.factorial : ℂ)⁻¹) • iteratedFDeriv ℂ m h 0 (fun _ => x)

lemma homPart_smul (h : E → E) (m : ℕ) (c : ℂ) (x : E) :
    homPart h m (c • x) = c ^ m • homPart h m x := by
  simp only [homPart]
  have := (iteratedFDeriv ℂ m h 0).map_smul_univ (fun _ => c) (fun _ => x)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  rw [this, smul_comm]

lemma homPart_zero_right (h : E → E) {m : ℕ} (hm : m ≠ 0) : homPart h m 0 = 0 := by
  have := homPart_smul h m 0 0
  rw [zero_smul, zero_pow hm, zero_smul] at this
  exact this

/-- **Extraction lemma.** If `P(x) = Φ(x, …, x)` is homogeneous of degree `m ≥ 2` and
`|⟨P(x), x⟩| ≤ 2‖x‖^{m+1}` for all `x`, then `‖P(u)‖ ≤ 4m` for unit vectors `u`. The component of
`P(u)` along a unit vector `w ⊥ u` is extracted by the maximum modulus principle, applied to
`λ ↦ λ⟪u, P(u + λw)⟫ + s²⟪w, P(u + λw)⟫`, which equals `λ⟨P(x), x⟩` (`x = u + λw`) on `|λ| = s`. -/
theorem norm_le_of_norm_inner_le {m : ℕ} (hm : 2 ≤ m)
    (Φ : ContinuousMultilinearMap ℂ (fun _ : Fin m => E) E)
    (hΦ : ∀ x : E, ‖⟪x, Φ (fun _ => x)⟫_ℂ‖ ≤ 2 * ‖x‖ ^ (m + 1)) {u : E} (hu : ‖u‖ = 1) :
    ‖Φ (fun _ => u)‖ ≤ 4 * m := by
  set P : E → E := fun x => Φ (fun _ => x) with hPdef
  have hPd : Differentiable ℂ P :=
    ((Φ.contDiff (n := 1)).differentiable one_ne_zero).comp
      (differentiable_pi.mpr fun _ => differentiable_id)
  set v := P u with hv
  set a := ⟪u, v⟫_ℂ with ha
  set y := v - a • u with hy
  have huu : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; simp
  have huy : ⟪u, y⟫_ℂ = 0 := by
    rw [hy, inner_sub_right, inner_smul_right, huu, mul_one, ha, sub_self]
  have hvy : v = a • u + y := by rw [hy]; abel
  have hpyth : ‖v‖ ^ 2 = ‖a‖ ^ 2 + ‖y‖ ^ 2 := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (a • u) y
      (by rw [inner_smul_left, huy, mul_zero])
    rw [hvy, sq, sq, sq, this, norm_smul, hu, mul_one]
  have ha2 : ‖a‖ ≤ 2 := by
    have := hΦ u
    rw [hu, one_pow, mul_one] at this
    exact this
  -- the component orthogonal to `u`
  have hy2 : ‖y‖ ^ 2 ≤ 12 * (m + 1) := by
    rcases eq_or_ne y 0 with hy0 | hy0
    · rw [hy0, norm_zero]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    set w : E := ((‖y‖ : ℂ)⁻¹) • y with hw
    have hw1 : ‖w‖ = 1 := by
      rw [hw, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hyn,
        inv_mul_cancel₀ hyn.ne']
    have huw : ⟪u, w⟫_ℂ = 0 := by rw [hw, inner_smul_right, huy, mul_zero]
    have hwu : ⟪w, u⟫_ℂ = 0 := by rw [← inner_conj_symm, huw, map_zero]
    have hwv : ⟪w, v⟫_ℂ = (‖y‖ : ℂ) := by
      rw [hvy, inner_add_right, inner_smul_right, hwu, mul_zero, zero_add, hw, inner_smul_left,
        inner_self_eq_norm_sq_to_K, map_inv₀, Complex.conj_ofReal]
      have : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast hyn.ne'
      field_simp
      rfl
    clear_value w
    -- the radius `s = (m + 1)^{-1/2}`
    set t : ℝ := 1 / (m + 1) with ht
    have ht0 : 0 < t := by positivity
    set s : ℝ := Real.sqrt t with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr ht0
    have hss : s ^ 2 = t := Real.sq_sqrt ht0.le
    set φ : ℂ → ℂ := fun l => l * ⟪u, P (u + l • w)⟫_ℂ + (t : ℂ) * ⟪w, P (u + l • w)⟫_ℂ
      with hφ
    have hφd : Differentiable ℂ φ := by
      have hx : Differentiable ℂ (fun l : ℂ => u + l • w) :=
        (differentiable_id.smul_const w).const_add u
      have hPx : Differentiable ℂ (fun l : ℂ => P (u + l • w)) := hPd.comp hx
      exact (differentiable_id.mul ((innerSL ℂ u).differentiable.comp hPx)).add
        ((differentiable_const _).mul ((innerSL ℂ w).differentiable.comp hPx))
    have hnormx : ∀ l : ℂ, ‖u + l • w‖ ^ 2 = 1 + ‖l‖ ^ 2 := by
      intro l
      have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) u (l • w)
        (by rw [inner_smul_right, huw, mul_zero])
      rw [sq, sq, this, hu, norm_smul, hw1]; ring
    set N : ℝ := Real.sqrt (1 + t) ^ (m + 1) with hN
    have hcircle : ∀ l ∈ sphere (0 : ℂ) s, ‖φ l‖ ≤ s * (2 * N) := by
      intro l hl
      have hl' : ‖l‖ = s := by simpa using hl
      have hφl : φ l = l * ⟪u + l • w, P (u + l • w)⟫_ℂ := by
        rw [hφ]
        simp only
        rw [inner_add_left, inner_smul_left, mul_add, ← mul_assoc, Complex.mul_conj,
          Complex.normSq_eq_norm_sq, hl', hss]
      rw [hφl, norm_mul, hl']
      refine mul_le_mul_of_nonneg_left ((hΦ _).trans (le_of_eq ?_)) hs0.le
      have hx : ‖u + l • w‖ = Real.sqrt (1 + t) := by
        rw [← Real.sqrt_sq (norm_nonneg _), hnormx, hl', hss]
      rw [hx]
    have hmax : ‖φ 0‖ ≤ s * (2 * N) :=
      Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hφd.diffContOnCl
        (fun l hl => hcircle l (by rwa [frontier_ball 0 hs0.ne'] at hl))
        (subset_closure (mem_ball_self hs0))
    have hφ0 : φ 0 = (t : ℂ) * (‖y‖ : ℂ) := by
      rw [hφ]
      simp only [zero_smul, add_zero, zero_mul, zero_add]
      rw [← hv, hwv]
    rw [hφ0, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos ht0, abs_of_pos hyn] at hmax
    have hN2 : N ^ 2 = (1 + t) ^ (m + 1) := by
      rw [hN, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by positivity)]
    have hsq : (t * ‖y‖) ^ 2 ≤ (s * (2 * N)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hmax 2
    have hsq' : t * ‖y‖ ^ 2 ≤ 4 * (1 + t) ^ (m + 1) := by
      have h1 : (s * (2 * N)) ^ 2 = t * (4 * (1 + t) ^ (m + 1)) := by
        rw [mul_pow, mul_pow, hss, hN2]; ring
      rw [h1] at hsq
      have h2 : t * (t * ‖y‖ ^ 2) ≤ t * (4 * (1 + t) ^ (m + 1)) := by nlinarith
      exact le_of_mul_le_mul_left h2 ht0
    have he : (1 + t) ^ (m + 1) ≤ Real.exp 1 := by
      calc (1 + t) ^ (m + 1) ≤ (Real.exp t) ^ (m + 1) :=
            pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp t]) _
        _ = Real.exp (((m + 1 : ℕ) : ℝ) * t) := (Real.exp_nat_mul t (m + 1)).symm
        _ = Real.exp 1 := by
            congr 1
            rw [ht]; push_cast; field_simp
    have he3 := Real.exp_one_lt_three
    have h12 : t * ‖y‖ ^ 2 ≤ 12 := by linarith
    rw [ht] at h12
    have hm1 : (0 : ℝ) < m + 1 := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hm1] at h12
    linarith
  -- conclusion: `‖v‖² ≤ 4 + 12(m + 1) ≤ 16 m²`
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hv2 : ‖v‖ ^ 2 ≤ (4 * m) ^ 2 := by
    rw [hpyth]
    have : ‖a‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg a]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hv2

variable [FiniteDimensional ℂ E]

/-- Derivatives along a complex line through `0`. -/
lemma iteratedDeriv_comp_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {f : E → F} {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U)
    (hf : DifferentiableOn ℂ f U) (x : E) (m : ℕ) :
    iteratedDeriv m (fun ζ : ℂ => f (ζ • x)) 0 = iteratedFDeriv ℂ m f 0 (fun _ => x) := by
  have hCm : ContDiffOn ℂ m f U := hf.contDiffOn_of_isOpen hU m
  obtain ⟨L, hL⟩ : ∃ L : ℂ →L[ℂ] E, ∀ ζ : ℂ, L ζ = ζ • x :=
    ⟨ContinuousLinearMap.toSpanSingleton ℂ x,
      fun ζ => ContinuousLinearMap.toSpanSingleton_apply _ _ _⟩
  have hL0 : L 0 = 0 := map_zero L
  have hL1 : L 1 = x := by rw [hL, one_smul]
  have hWo : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have h0W : (0 : ℂ) ∈ L ⁻¹' U := by simp [hL0, h0]
  have h1 := L.iteratedFDerivWithin_comp_right hCm hU.uniqueDiffOn hWo.uniqueDiffOn
    (x := 0) (by simp [hL0, h0]) (i := m) le_rfl
  rw [iteratedFDerivWithin_of_isOpen m hWo h0W, hL0,
    iteratedFDerivWithin_of_isOpen m hU h0] at h1
  have hfun : (fun ζ : ℂ => f (ζ • x)) = f ∘ L := by funext ζ; simp [hL]
  rw [hfun, iteratedDeriv_eq_iteratedFDeriv, h1]
  simp [hL1]

lemma IsCaratheodory.iteratedDeriv_sliceF (hh : IsCaratheodory h) (u : E) (m : ℕ) :
    iteratedDeriv m (sliceF h u) 0 = ⟪u, iteratedFDeriv ℂ m h 0 (fun _ => u)⟫_ℂ := by
  have hg : DifferentiableOn ℂ (fun y => ⟪u, h y⟫_ℂ) (unitBall E) :=
    (innerSL ℂ u).differentiable.comp_differentiableOn hh.isNormalized.differentiableOn
  have h1 := iteratedDeriv_comp_smul isOpen_unitBall zero_mem_unitBall hg u m
  have hC : ContDiffAt ℂ m h 0 :=
    (hh.isNormalized.differentiableOn.contDiffOn_of_isOpen isOpen_unitBall m).contDiffAt
      (unitBall_mem_nhds zero_mem_unitBall)
  have h2 := (innerSL ℂ u).iteratedFDeriv_comp_left hC (i := m) le_rfl
  have h3 : iteratedFDeriv ℂ m (fun y => ⟪u, h y⟫_ℂ) 0 (fun _ => u) =
      ⟪u, iteratedFDeriv ℂ m h 0 (fun _ => u)⟫_ℂ := by
    have : (fun y => ⟪u, h y⟫_ℂ) = (innerSL ℂ u) ∘ h := rfl
    rw [this, h2]
    simp
  exact h1.trans h3

/-- **Coefficient bound**: `|⟨P_m(x), x⟩| ≤ 2‖x‖^{m+1}` for `m ≥ 2`. -/
theorem IsCaratheodory.norm_inner_homPart_le (hh : IsCaratheodory h) {m : ℕ} (hm : 2 ≤ m)
    (x : E) : ‖⟪x, homPart h m x⟫_ℂ‖ ≤ 2 * ‖x‖ ^ (m + 1) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [homPart_zero_right h (by omega)]; simp
  set ρ : ℝ := ‖x‖ with hρdef
  have hρ : 0 < ρ := norm_pos_iff.mpr hx0
  set u : E := ((ρ : ℂ)⁻¹) • x with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
      inv_mul_cancel₀ hρ.ne']
  have hxu : x = (ρ : ℂ) • u := by
    rw [hudef, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hρ.ne'), one_smul]
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    exact zero_ne_one hu
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have hc := norm_coeff_le_two (hh.differentiableOn_sliceF hu.le) (hh.sliceF_zero u)
    (by rw [(hh.hasDerivAt_sliceF_zero u).deriv, inner_self_eq_norm_sq_to_K, hu]; simp)
    (fun ζ hζ hζ0 => hh.re_inv_mul_sliceF_pos hu.le hu0 hζ hζ0) hk
  rw [hh.iteratedDeriv_sliceF] at hc
  have hcu : ⟪u, homPart h (k + 1) u⟫_ℂ =
      ⟪u, iteratedFDeriv ℂ (k + 1) h 0 (fun _ => u)⟫_ℂ / ((k + 1).factorial : ℂ) := by
    rw [homPart, inner_smul_right, div_eq_inv_mul]
  rw [hxu, homPart_smul, inner_smul_left, inner_smul_right, hcu, Complex.conj_ofReal, norm_mul,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  calc ρ * (ρ ^ (k + 1) * ‖⟪u, iteratedFDeriv ℂ (k + 1) h 0 (fun _ => u)⟫_ℂ /
        ((k + 1).factorial : ℂ)‖) ≤ ρ * (ρ ^ (k + 1) * 2) := by gcongr
    _ = 2 * ρ ^ (k + 1 + 1) := by ring

/-- `‖P_m(u)‖ ≤ 4m` for unit vectors `u`. -/
theorem IsCaratheodory.norm_homPart_le (hh : IsCaratheodory h) (m : ℕ) {u : E} (hu : ‖u‖ = 1) :
    ‖homPart h m u‖ ≤ 4 * m := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · simp [homPart, iteratedFDeriv_zero_apply, hh.map_zero]
    · simp [homPart, iteratedFDeriv_one_apply, hh.isNormalized.fderiv_zero, hu]
  · have := norm_le_of_norm_inner_le hm (((m.factorial : ℂ)⁻¹) • iteratedFDeriv ℂ m h 0)
      (fun x => by simpa [homPart] using hh.norm_inner_homPart_le hm x) hu
    simpa [homPart] using this

/-- The Taylor expansion of `h` along the ray through a unit vector `u`. -/
lemma IsCaratheodory.hasSum_homPart (hh : IsCaratheodory h) {u : E} (hu : ‖u‖ = 1) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) :
    HasSum (fun n => (r : ℂ) ^ n • homPart h n u) (h ((r : ℂ) • u)) := by
  have := FiniteDimensional.complete ℂ E
  have hg : DifferentiableOn ℂ (fun ζ : ℂ => h (ζ • u)) (ball 0 1) :=
    hh.isNormalized.differentiableOn.comp (differentiable_id.smul_const u).differentiableOn
      (mapsTo_smul_unitBall hu.le)
  have hz : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr
  have := Complex.hasSum_taylorSeries_on_ball hg hz
  convert this using 1
  funext n
  rw [iteratedDeriv_comp_smul isOpen_unitBall zero_mem_unitBall
    hh.isNormalized.differentiableOn u n, homPart, sub_zero, smul_comm]

/-- **Growth estimate** `‖h(z)‖ ≤ 4‖z‖/(1-‖z‖)²` for `h ∈ M(𝔹)` [GHK02, Theorem 1.2]. -/
theorem IsCaratheodory.norm_le (hh : IsCaratheodory h) {z : E} (hz : z ∈ unitBall E) :
    ‖h z‖ ≤ 4 * ‖z‖ / (1 - ‖z‖) ^ 2 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [hh.map_zero]; simp
  obtain ⟨r, u, hr, hr1, hu, hzu, hrz⟩ : ∃ (r : ℝ) (u : E), 0 < r ∧ r < 1 ∧ ‖u‖ = 1 ∧
      z = (r : ℂ) • u ∧ ‖z‖ = r := by
    refine ⟨‖z‖, ((‖z‖ : ℂ)⁻¹) • z, norm_pos_iff.mpr hz0, by simpa using hz, ?_, ?_, rfl⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_pos_iff.mpr hz0).ne']
    · rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast (norm_pos_iff.mpr hz0).ne'), one_smul]
  rw [hrz]
  have hs : HasSum (fun n => (r : ℂ) ^ n • homPart h n u) (h z) := by
    rw [hzu]; exact hh.hasSum_homPart hu hr.le hr1
  have hg : HasSum (fun n : ℕ => 4 * ((n : ℝ) * r ^ n)) (4 * (r / (1 - r) ^ 2)) := by
    have hn : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr]; exact hr1
    exact (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hn).mul_left 4
  have hbound : ∀ n : ℕ, ‖(r : ℂ) ^ n • homPart h n u‖ ≤ 4 * ((n : ℝ) * r ^ n) := by
    intro n
    rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    calc r ^ n * ‖homPart h n u‖ ≤ r ^ n * (4 * n) :=
          mul_le_mul_of_nonneg_left (hh.norm_homPart_le n hu) (by positivity)
      _ = 4 * (n * r ^ n) := by ring
  calc ‖h z‖ ≤ 4 * (r / (1 - r) ^ 2) := hs.norm_le_of_bounded hg hbound
    _ = 4 * r / (1 - r) ^ 2 := by ring

/-- `h(z) = z + O(‖z‖²)` uniformly on `M(𝔹)`: `‖h(z) - z‖ ≤ 8‖z‖²/(1-‖z‖)²`. -/
theorem IsCaratheodory.norm_sub_le (hh : IsCaratheodory h) {z : E} (hz : z ∈ unitBall E) :
    ‖h z - z‖ ≤ 8 * ‖z‖ ^ 2 / (1 - ‖z‖) ^ 2 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [hh.map_zero]; simp
  obtain ⟨r, u, hr, hr1, hu, hzu, hrz⟩ : ∃ (r : ℝ) (u : E), 0 < r ∧ r < 1 ∧ ‖u‖ = 1 ∧
      z = (r : ℂ) • u ∧ ‖z‖ = r := by
    refine ⟨‖z‖, ((‖z‖ : ℂ)⁻¹) • z, norm_pos_iff.mpr hz0, by simpa using hz, ?_, ?_, rfl⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_pos_iff.mpr hz0).ne']
    · rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast (norm_pos_iff.mpr hz0).ne'), one_smul]
  rw [hrz]
  have hs : HasSum (fun n => (r : ℂ) ^ n • homPart h n u) (h z) := by
    rw [hzu]; exact hh.hasSum_homPart hu hr.le hr1
  have h1 : homPart h 1 u = u := by
    simp [homPart, iteratedFDeriv_one_apply, hh.isNormalized.fderiv_zero]
  -- remove the linear term
  have hs' : HasSum (fun n => if n = 1 then 0 else (r : ℂ) ^ n • homPart h n u) (h z - z) := by
    have := hs.sub (hasSum_ite_eq 1 z)
    convert this using 1
    funext n
    by_cases hn : n = 1
    · subst hn
      simp only [↓reduceIte, pow_one, h1]
      rw [← hzu, sub_self]
    · simp only [hn, ↓reduceIte, sub_zero]
  have hg0 : HasSum (fun n : ℕ => 4 * ((n : ℝ) * r ^ n)) (4 * (r / (1 - r) ^ 2)) := by
    have hn : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr]; exact hr1
    exact (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hn).mul_left 4
  have hg : HasSum (fun n : ℕ => if n = 1 then 0 else 4 * ((n : ℝ) * r ^ n))
      (4 * (r / (1 - r) ^ 2) - 4 * r) := by
    have := hg0.sub (hasSum_ite_eq 1 (4 * r))
    convert this using 1
    funext n
    by_cases hn : n = 1
    · subst hn
      simp only [↓reduceIte, Nat.cast_one, one_mul, pow_one, sub_self]
    · simp only [hn, ↓reduceIte, sub_zero]
  have hbound : ∀ n : ℕ, ‖(if n = 1 then 0 else (r : ℂ) ^ n • homPart h n u)‖ ≤
      (if n = 1 then 0 else 4 * ((n : ℝ) * r ^ n)) := by
    intro n
    by_cases hn : n = 1
    · simp only [hn, ↓reduceIte, norm_zero, le_refl]
    · simp only [hn, ↓reduceIte]
      rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      calc r ^ n * ‖homPart h n u‖ ≤ r ^ n * (4 * n) :=
            mul_le_mul_of_nonneg_left (hh.norm_homPart_le n hu) (by positivity)
        _ = 4 * (n * r ^ n) := by ring
  have hd : 0 < (1 - r) ^ 2 := by nlinarith
  have h1r : 1 - r ≠ 0 := (sub_pos.mpr hr1).ne'
  calc ‖h z - z‖ ≤ 4 * (r / (1 - r) ^ 2) - 4 * r := hs'.norm_le_of_bounded hg hbound
    _ = 4 * r ^ 2 * (2 - r) / (1 - r) ^ 2 := by field_simp; ring
    _ ≤ 8 * r ^ 2 / (1 - r) ^ 2 := by
        apply div_le_div_of_nonneg_right _ hd.le
        nlinarith

/-- The growth estimate on closed balls. -/
theorem IsCaratheodory.norm_le_of_norm_le (hh : IsCaratheodory h) {ρ : ℝ} (hρ : ρ < 1) {z : E}
    (hz : ‖z‖ ≤ ρ) : ‖h z‖ ≤ 4 * ρ / (1 - ρ) ^ 2 := by
  have hz1 : z ∈ unitBall E := by rw [mem_unitBall]; linarith
  refine (hh.norm_le hz1).trans ?_
  have h1 : 0 < 1 - ρ := by linarith
  gcongr
  · linarith [norm_nonneg z]

/-- A bound for `Dh` on closed balls, uniform on `M(𝔹)`. -/
theorem IsCaratheodory.norm_fderiv_le (hh : IsCaratheodory h) {ρ : ℝ} (hρ : ρ < 1)
    {z : E} (hz : ‖z‖ ≤ ρ) : ‖fderiv ℂ h z‖ ≤ 32 / (1 - ρ) ^ 3 := by
  set r := (1 - ρ) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hsub : closedBall z r ⊆ closedBall 0 ((1 + ρ) / 2) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_closedBall_zero_iff]
    calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ r + ρ := add_le_add hw hz
      _ = (1 + ρ) / 2 := by rw [hr]; ring
  have hρ' : (1 + ρ) / 2 < 1 := by linarith
  have hM : ∀ w ∈ closedBall z r, ‖h w‖ ≤ 16 / (1 - ρ) ^ 2 := by
    intro w hw
    have hw' : ‖w‖ ≤ (1 + ρ) / 2 := by simpa using hsub hw
    refine (hh.norm_le_of_norm_le hρ' hw').trans ?_
    have : (1 : ℝ) - (1 + ρ) / 2 = (1 - ρ) / 2 := by ring
    rw [this, div_le_div_iff₀ (by nlinarith) (by nlinarith)]
    have h1 : 0 < (1 - ρ) ^ 2 := by nlinarith
    nlinarith
  have := SCV.norm_fderiv_le_of_forall_mem_closedBall_norm_le hr0
    hh.isNormalized.differentiableOn isOpen_unitBall
    (hsub.trans (closedBall_subset_ball hρ')) hM
  refine this.trans (le_of_eq ?_)
  rw [hr]
  have : (1 - ρ) ≠ 0 := by linarith
  field_simp
  ring

/-- `h ∈ M(𝔹)` is Lipschitz on `closedBall 0 ρ` with a constant depending only on `ρ`. -/
theorem IsCaratheodory.lipschitzOnWith (hh : IsCaratheodory h) {ρ : ℝ} (hρ : ρ < 1) :
    LipschitzOnWith (32 / (1 - ρ) ^ 3).toNNReal h (closedBall 0 ρ) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℂ)
  · intro x hx
    exact hh.isNormalized.differentiableAt (closedBall_subset_ball hρ hx)
  · intro x hx
    rw [← norm_toNNReal]
    exact Real.toNNReal_le_toNNReal (hh.norm_fderiv_le hρ (by simpa using hx))
  · exact convex_closedBall 0 ρ

end Expansion

end LoewnerS0
