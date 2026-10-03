import LoewnerS0.Prelude
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# A small toolkit of several complex variables

Mathlib's complex analysis is mostly about functions of one complex variable. This file derives
the few facts about holomorphic maps `f : E → F` between complex normed spaces (holomorphic =
complex Fréchet differentiable) that the project needs, by restricting to complex lines
`ζ ↦ z + ζ • v` and using the one-variable Cauchy estimates.

## Main results

* `norm_fderiv_le_of_forall_mem_closedBall_norm_le`: the Cauchy estimate
  `‖Df(z)‖ ≤ M / r` if `‖f‖ ≤ M` on `closedBall z r`.
* `differentiableOn_of_tendstoUniformlyOn`: a uniform limit of holomorphic maps on an open set
  is holomorphic (Weierstrass).
* `DifferentiableOn.differentiableOn_fderiv_apply`: if `f` is holomorphic on an open set, so is
  `z ↦ Df(z) v`.
* `DifferentiableOn.contDiffOn_of_isOpen`: on a finite-dimensional space, a holomorphic map on an
  open set is `C^n` for every `n`.
-/

open Complex Metric Set Filter
open scoped Topology

noncomputable section

namespace LoewnerS0.SCV

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### Complex lines -/

lemma differentiableOn_line {f : E → F} {U : Set E} (hf : DifferentiableOn ℂ f U) (z v : E) :
    DifferentiableOn ℂ (fun ζ : ℂ => f (z + ζ • v)) ((fun ζ : ℂ => z + ζ • v) ⁻¹' U) := by
  have hl : Differentiable ℂ (fun ζ : ℂ => z + ζ • v) :=
    (differentiable_id.smul_const v).const_add z
  exact hf.comp hl.differentiableOn (fun ζ hζ => hζ)

lemma hasDerivAt_line {f : E → F} {z v : E} (ζ : ℂ) (hf : DifferentiableAt ℂ f (z + ζ • v)) :
    HasDerivAt (fun ζ : ℂ => f (z + ζ • v)) (fderiv ℂ f (z + ζ • v) v) ζ := by
  have hl : HasDerivAt (fun ζ : ℂ => z + ζ • v) v ζ := by
    simpa using ((hasDerivAt_id ζ).smul_const v).const_add z
  exact hf.hasFDerivAt.comp_hasDerivAt ζ hl

/-! ### The Cauchy estimate -/

/-- **Cauchy estimate** for the derivative of a holomorphic map of several variables. -/
theorem norm_fderiv_le_of_forall_mem_closedBall_norm_le {f : E → F} {U : Set E} {z : E}
    {r M : ℝ} (hr : 0 < r) (hf : DifferentiableOn ℂ f U) (hU : IsOpen U)
    (hsub : closedBall z r ⊆ U) (hM : ∀ w ∈ closedBall z r, ‖f w‖ ≤ M) :
    ‖fderiv ℂ f z‖ ≤ M / r := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z (mem_closedBall_self hr.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hr.le) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨u, hu, hvu⟩ : ∃ u : E, ‖u‖ = 1 ∧ v = ((‖v‖ : ℝ) : ℂ) • u := by
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ hv'.ne']
    · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hv'.ne', Complex.ofReal_one,
        one_smul]
  have hmaps : ∀ ζ ∈ closedBall (0 : ℂ) r, z + ζ • u ∈ closedBall z r := by
    intro ζ hζ
    rw [mem_closedBall, dist_self_add_left, norm_smul, hu, mul_one]
    simpa using hζ
  have hdiff : DiffContOnCl ℂ (fun ζ : ℂ => f (z + ζ • u)) (ball 0 r) :=
    (differentiableOn_line hf z u).diffContOnCl_ball (fun ζ hζ => hsub (hmaps ζ hζ))
  have hzU : z ∈ U := hsub (mem_closedBall_self hr.le)
  have hderiv : deriv (fun ζ : ℂ => f (z + ζ • u)) 0 = fderiv ℂ f z u := by
    have := hasDerivAt_line (f := f) (z := z) (v := u) 0
      (by simpa using hf.differentiableAt (hU.mem_nhds hzU))
    simpa using this.deriv
  have hbound : ‖fderiv ℂ f z u‖ ≤ M / r := by
    rw [← hderiv]
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdiff
      fun ζ hζ => hM _ (hmaps ζ (sphere_subset_closedBall hζ))
  have hval : ‖fderiv ℂ f z v‖ = ‖v‖ * ‖fderiv ℂ f z u‖ := by
    conv_lhs => rw [hvu]
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  rw [hval, mul_comm]
  exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

/-! ### Uniform limits -/

/-- **Weierstrass' theorem** in several variables: a uniform limit of holomorphic maps on an open
set is holomorphic. -/
theorem differentiableOn_of_tendstoUniformlyOn [CompleteSpace F] {G : ℕ → E → F} {g : E → F}
    {V : Set E} (hV : IsOpen V) (hG : ∀ n, DifferentiableOn ℂ (G n) V)
    (hconv : TendstoUniformlyOn G g atTop V) : DifferentiableOn ℂ g V := by
  intro x hx
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV x hx
  set r := ε / 3 with hr_def
  have hr : 0 < r := by positivity
  have hsub : ∀ y ∈ ball x r, closedBall y r ⊆ V := by
    intro y hy w hw
    apply hεV
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hw
    calc dist w x ≤ dist w y + dist y x := dist_triangle _ _ _
      _ < r + r := by linarith
      _ < ε := by linarith
  have hyV : ∀ y ∈ ball x r, y ∈ V := fun y hy => hsub y hy (mem_closedBall_self hr.le)
  have hdG : ∀ n, ∀ y ∈ V, DifferentiableAt ℂ (G n) y := fun n y hy =>
    (hG n y hy).differentiableAt (hV.mem_nhds hy)
  -- the derivatives form a uniform Cauchy sequence on `ball x r`
  have hcauchy : UniformCauchySeqOn (fun n => fderiv ℂ (G n)) atTop (ball x r) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (Metric.tendstoUniformlyOn_iff.mp hconv (δ * r / 4) (by positivity))
    refine ⟨N, fun m hm n hn y hy => ?_⟩
    rw [dist_eq_norm]
    have hsubd : fderiv ℂ (G m) y - fderiv ℂ (G n) y = fderiv ℂ (fun w => G m w - G n w) y :=
      (fderiv_sub (hdG m y (hyV y hy)) (hdG n y (hyV y hy))).symm
    rw [hsubd]
    have hb : ‖fderiv ℂ (fun w => G m w - G n w) y‖ ≤ (δ * r / 2) / r := by
      apply norm_fderiv_le_of_forall_mem_closedBall_norm_le hr ((hG m).sub (hG n)) hV (hsub y hy)
      intro w hw
      have h1 := hN m hm w (hsub y hy hw)
      have h2 := hN n hn w (hsub y hy hw)
      rw [dist_eq_norm] at h1 h2
      calc ‖G m w - G n w‖ = ‖(g w - G n w) - (g w - G m w)‖ := by congr 1; abel
        _ ≤ ‖g w - G n w‖ + ‖g w - G m w‖ := norm_sub_le _ _
        _ ≤ δ * r / 2 := by linarith
    calc _ ≤ (δ * r / 2) / r := hb
      _ = δ / 2 := by field_simp
      _ < δ := by linarith
  have hlim : ∀ y ∈ ball x r, ∃ L, Tendsto (fun n => fderiv ℂ (G n) y) atTop (𝓝 L) :=
    fun y hy => cauchySeq_tendsto_of_complete (hcauchy.cauchySeq hy)
  choose! g' hg' using hlim
  have hunif : TendstoUniformlyOn (fun n => fderiv ℂ (G n)) g' atTop (ball x r) :=
    hcauchy.tendstoUniformlyOn_of_tendsto hg'
  have := hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hunif
    (fun n y hy => (hdG n y (hyV y hy)).hasFDerivAt)
    (fun y hy => hconv.tendsto_at (hyV y hy)) (mem_ball_self hr)
  exact this.differentiableAt.differentiableWithinAt

/-! ### Derivatives of holomorphic maps are holomorphic -/

/-- Second-order Taylor estimate for a holomorphic function of one variable, from the Cauchy
estimate for the second derivative. -/
lemma norm_sub_sub_smul_deriv_le [CompleteSpace F] {φ : ℂ → F} {ρ M : ℝ} (hρ : 0 < ρ)
    (hφ : DifferentiableOn ℂ φ (ball 0 (3 * ρ))) (hM : ∀ ζ ∈ ball (0 : ℂ) (3 * ρ), ‖φ ζ‖ ≤ M)
    {s : ℂ} (hs : ‖s‖ ≤ ρ) :
    ‖φ s - φ 0 - s • deriv φ 0‖ ≤ 2 * M / ρ ^ 2 * ‖s‖ ^ 2 := by
  have hopen : IsOpen (ball (0 : ℂ) (3 * ρ)) := isOpen_ball
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_ball_self (by positivity)))
  have hK0 : 0 ≤ 2 * M / ρ ^ 2 := div_nonneg (mul_nonneg zero_le_two hM0) (pow_nonneg hρ.le 2)
  have hφ' : DifferentiableOn ℂ (deriv φ) (ball 0 (3 * ρ)) := hφ.deriv hopen
  have hsub0 : closedBall (0 : ℂ) ρ ⊆ ball 0 (3 * ρ) :=
    closedBall_subset_ball (by linarith)
  -- Cauchy estimate for the second derivative on `closedBall 0 ρ`
  have hC : ∀ ζ ∈ closedBall (0 : ℂ) ρ, ‖deriv (deriv φ) ζ‖ ≤ 2 * M / ρ ^ 2 := by
    intro ζ hζ
    have hsub : closedBall ζ ρ ⊆ ball 0 (3 * ρ) := by
      intro w hw
      rw [mem_closedBall] at hw hζ
      rw [mem_ball]
      calc dist w 0 ≤ dist w ζ + dist ζ 0 := dist_triangle _ _ _
        _ ≤ ρ + ρ := add_le_add hw hζ
        _ < 3 * ρ := by linarith
    have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hρ
      (hφ.diffContOnCl_ball hsub) (fun w hw => hM w (hsub (sphere_subset_closedBall hw)))
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at this
    simpa using this
  -- the derivative is Lipschitz on `closedBall 0 ρ`
  have hd1 : ∀ ζ ∈ closedBall (0 : ℂ) ρ, ‖deriv φ ζ - deriv φ 0‖ ≤ 2 * M / ρ ^ 2 * ‖ζ‖ := by
    intro ζ hζ
    have := (convex_closedBall (0 : ℂ) ρ).norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hφ' w (hsub0 hw)).differentiableAt (hopen.mem_nhds (hsub0 hw))) hC
      (mem_closedBall_self hρ.le) hζ
    simpa using this
  -- the remainder `φ ζ - ζ • φ'(0)`
  have hs' : s ∈ closedBall (0 : ℂ) ‖s‖ := by simp
  have hsubs : closedBall (0 : ℂ) ‖s‖ ⊆ closedBall 0 ρ := closedBall_subset_closedBall hs
  have hψ : ∀ ζ ∈ closedBall (0 : ℂ) ‖s‖,
      HasDerivAt (fun ζ => φ ζ - ζ • deriv φ 0) (deriv φ ζ - deriv φ 0) ζ := by
    intro ζ hζ
    have h1 := ((hφ ζ (hsub0 (hsubs hζ))).differentiableAt
      (hopen.mem_nhds (hsub0 (hsubs hζ)))).hasDerivAt
    have h2 := h1.sub ((hasDerivAt_id ζ).smul_const (deriv φ 0))
    rw [one_smul] at h2
    exact h2
  have := (convex_closedBall (0 : ℂ) ‖s‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun ζ hζ => (hψ ζ hζ).hasDerivWithinAt)
    (fun ζ hζ => (hd1 ζ (hsubs hζ)).trans
      (mul_le_mul_of_nonneg_left (by simpa using hζ) hK0))
    (mem_closedBall_self (norm_nonneg s)) hs'
  calc ‖φ s - φ 0 - s • deriv φ 0‖ = ‖(φ s - s • deriv φ 0) - (φ 0 - (0 : ℂ) • deriv φ 0)‖ := by
        congr 1; simp only [zero_smul, sub_zero]; abel
    _ ≤ 2 * M / ρ ^ 2 * ‖s‖ * ‖s - 0‖ := this
    _ = 2 * M / ρ ^ 2 * ‖s‖ ^ 2 := by rw [sub_zero]; ring

/-- If `f` is holomorphic on an open set `U`, then so is `z ↦ Df(z) v` for every vector `v`. -/
theorem _root_.DifferentiableOn.differentiableOn_fderiv_apply [CompleteSpace F] {f : E → F}
    {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (v : E) :
    DifferentiableOn ℂ (fun z => fderiv ℂ f z v) U := by
  intro x hx
  -- a ball around `x` on which `f` is bounded
  obtain ⟨ε₁, hε₁, hε₁U⟩ := Metric.isOpen_iff.mp hU x hx
  have hcont : ContinuousAt f x := (hf.differentiableAt (hU.mem_nhds hx)).continuousAt
  obtain ⟨ε₂, hε₂, hε₂f⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
  set ε := min ε₁ ε₂ with hε_def
  have hε : 0 < ε := lt_min hε₁ hε₂
  set M := ‖f x‖ + 1 with hM_def
  have hfM : ∀ w ∈ ball x ε, ‖f w‖ ≤ M := by
    intro w hw
    have h1 := hε₂f (lt_of_lt_of_le (mem_ball.mp hw) (min_le_right _ _))
    rw [dist_eq_norm] at h1
    calc ‖f w‖ = ‖(f w - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖f w - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ M := by rw [hM_def]; linarith
  have hεU : ball x ε ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hε₁U
  set r := ε / 4 with hr_def
  have hr : 0 < r := by positivity
  set c := ‖v‖ + 1 with hc_def
  have hc : 0 < c := by positivity
  set ρ := r / c with hρ_def
  have hρ : 0 < ρ := by positivity
  -- the lines through points of `ball x r` stay in `ball x ε` for `|ζ| < 3ρ`
  have hline : ∀ z ∈ ball x r, ∀ ζ ∈ ball (0 : ℂ) (3 * ρ), z + ζ • v ∈ ball x ε := by
    intro z hz ζ hζ
    rw [mem_ball_zero_iff] at hζ
    rw [mem_ball] at hz ⊢
    have h1 : ‖ζ‖ * ‖v‖ ≤ ‖ζ‖ * c := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    have h2 : ‖ζ‖ * c < 3 * ρ * c := mul_lt_mul_of_pos_right hζ hc
    have h3 : 3 * ρ * c = 3 * r := by rw [hρ_def]; field_simp
    calc dist (z + ζ • v) x ≤ dist z x + ‖ζ • v‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]; exact norm_add_le _ _
      _ = dist z x + ‖ζ‖ * ‖v‖ := by rw [norm_smul]
      _ < r + 3 * r := by linarith
      _ = ε := by rw [hr_def]; ring
  -- step sizes and difference quotients
  set s : ℕ → ℂ := fun n => ((ρ / (n + 1) : ℝ) : ℂ) with hs_def
  have hs_pos : ∀ n : ℕ, 0 < ρ / ((n : ℝ) + 1) := fun n => by positivity
  have hs_norm : ∀ n, ‖s n‖ = ρ / (n + 1) := fun n => by
    simp only [hs_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs_pos n)]
  have hs_ne : ∀ n, s n ≠ 0 := fun n => by
    rw [← norm_ne_zero_iff, hs_norm]; exact (hs_pos n).ne'
  set q : ℕ → E → F := fun n z => (s n)⁻¹ • (f (z + s n • v) - f z) with hq_def
  have hq : ∀ n, DifferentiableOn ℂ (q n) (ball x r) := by
    intro n
    have h1 : DifferentiableOn ℂ (fun z => f (z + s n • v)) (ball x r) := by
      refine hf.comp (differentiableOn_id.add_const _) (fun z hz => hεU (hline z hz _ ?_))
      rw [mem_ball_zero_iff, hs_norm]
      calc ρ / (n + 1) ≤ ρ := div_le_self hρ.le (by linarith [n.cast_nonneg (α := ℝ)])
        _ < 3 * ρ := by linarith
    have h2 : DifferentiableOn ℂ f (ball x r) :=
      hf.mono ((ball_subset_ball (by linarith)).trans hεU)
    exact (h1.sub h2).const_smul _
  have hconv : TendstoUniformlyOn q (fun z => fderiv ℂ f z v) atTop (ball x r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * M / ρ / η)
    refine eventually_atTop.mpr ⟨N, fun n hn z hz => ?_⟩
    set φ : ℂ → F := fun ζ => f (z + ζ • v) with hφ_def
    have hφd : DifferentiableOn ℂ φ (ball 0 (3 * ρ)) :=
      (differentiableOn_line hf z v).mono fun ζ hζ => hεU (hline z hz ζ hζ)
    have hφM : ∀ ζ ∈ ball (0 : ℂ) (3 * ρ), ‖φ ζ‖ ≤ M := fun ζ hζ => hfM _ (hline z hz ζ hζ)
    have hzU : z ∈ U := hεU (by simpa using hline z hz 0 (by simp; positivity))
    have hφ0 : deriv φ 0 = fderiv ℂ f z v := by
      have := hasDerivAt_line (f := f) (z := z) (v := v) 0
        (by simpa using hf.differentiableAt (hU.mem_nhds hzU))
      simpa using this.deriv
    have key := norm_sub_sub_smul_deriv_le hρ hφd hφM (s := s n)
      (by rw [hs_norm]; exact div_le_self hρ.le (by linarith [n.cast_nonneg (α := ℝ)]))
    rw [hφ0] at key
    have hφz : φ 0 = f z := by simp [hφ_def]
    rw [hφz] at key
    have hdiff : fderiv ℂ f z v - q n z =
        -((s n)⁻¹ • (f (z + s n • v) - f z - s n • fderiv ℂ f z v)) := by
      rw [hq_def, smul_sub (s n)⁻¹ (f (z + s n • v) - f z), smul_smul, inv_mul_cancel₀ (hs_ne n),
        one_smul]
      abel
    rw [dist_eq_norm, hdiff, norm_neg, norm_smul, norm_inv]
    have hsn : ‖s n‖ ≠ 0 := norm_ne_zero_iff.mpr (hs_ne n)
    calc ‖s n‖⁻¹ * ‖f (z + s n • v) - f z - s n • fderiv ℂ f z v‖
        ≤ ‖s n‖⁻¹ * (2 * M / ρ ^ 2 * ‖s n‖ ^ 2) :=
          mul_le_mul_of_nonneg_left key (inv_nonneg.mpr (norm_nonneg _))
      _ = 2 * M / ρ ^ 2 * ‖s n‖ := by field_simp
      _ = 2 * M / ρ / (n + 1) := by rw [hs_norm]; field_simp
      _ < η := by
          have hM0 : 0 ≤ M := by rw [hM_def]; positivity
          have hn' : (2 * M / ρ / η : ℝ) < n + 1 := by
            have : (N : ℝ) ≤ n := by exact_mod_cast hn
            linarith
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hη] at hn'
          linarith
  have hdiffOn := differentiableOn_of_tendstoUniformlyOn isOpen_ball hq hconv
  exact (hdiffOn x (mem_ball_self hr)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))
    |>.differentiableWithinAt

/-- On a finite-dimensional space, a holomorphic map on an open set is `C^n` for every `n`. -/
theorem _root_.DifferentiableOn.contDiffOn_of_isOpen [FiniteDimensional ℂ E] [CompleteSpace F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    ContDiffOn ℂ n f U := by
  induction n generalizing f with
  | zero => exact contDiffOn_zero.mpr hf.continuousOn
  | succ n ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨hf, fun h => absurd h (by simp), ?_⟩
    rw [contDiffOn_clm_apply]
    exact fun v => ih (hf.differentiableOn_fderiv_apply hU v)

end LoewnerS0.SCV
