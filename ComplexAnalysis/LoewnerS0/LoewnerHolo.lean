import LoewnerS0.LoewnerExist
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Holomorphic dependence of solutions of the Loewner ODE on the initial value

Let `h` be a Herglotz vector field and `v` a solution of the Loewner ODE. We show that
`z ↦ v(z, t)` is holomorphic on `𝔹` for every `t ≥ 0`.

* An integral `x ↦ ∫ₐᵇ G(x, σ) dσ` of maps `G(·, σ)` that are holomorphic on an open set, uniformly
  bounded and measurable in `σ`, is holomorphic (`differentiableOn_intervalIntegral`; the
  measurability of `σ ↦ D_x G(x, σ)` is obtained from difference quotients and a basis).
* On a short time interval `[0, T₀]`, the Picard iterates for the retracted field stay in the ball
  where the retraction is the identity, so they are holomorphic in the initial value, and they
  converge uniformly; hence the solution is holomorphic in the initial value (Weierstrass).
* For general `t`, the solution is a composition of such short-time solution maps of the
  time-shifted fields `h(· + s)` (by uniqueness).
-/

open Complex Metric Set Filter MeasureTheory
open scoped InnerProductSpace Topology NNReal Interval Nat

noncomputable section

namespace LoewnerS0

/-! ### Holomorphic dependence of integrals on parameters -/

section ParamIntegral

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- In finite dimension, an operator-valued function is a.e. strongly measurable if it is so
after evaluation at every vector. -/
lemma aestronglyMeasurable_clm_of_forall {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {T : α → H →L[ℂ] F} (hT : ∀ v, AEStronglyMeasurable (fun a => T a v) μ) :
    AEStronglyMeasurable T μ := by
  set b := Module.finBasis ℂ H
  have heq : T = fun a => ∑ i, (ContinuousLinearMap.smulRightL ℂ H F
      (LinearMap.toContinuousLinearMap (b.coord i))) (T a (b i)) := by
    funext a
    ext x
    simp
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    simp only [map_smul]
  rw [heq]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    (ContinuousLinearMap.smulRightL ℂ H F
      (LinearMap.toContinuousLinearMap (b.coord i))).continuous.comp_aestronglyMeasurable (hT (b i))

/-- **Holomorphic dependence of integrals on parameters.** -/
theorem differentiableOn_intervalIntegral {G : H → ℝ → F} {U : Set H} (hU : IsOpen U)
    {a b : ℝ} (hab : a ≤ b)
    (hmeas : ∀ x ∈ U, AEStronglyMeasurable (G x) (volume.restrict (Ioc a b)))
    (hdiff : ∀ σ ∈ Ioc a b, DifferentiableOn ℂ (G · σ) U) {B : ℝ}
    (hbd : ∀ x ∈ U, ∀ σ ∈ Ioc a b, ‖G x σ‖ ≤ B) :
    DifferentiableOn ℂ (fun x => ∫ σ in a..b, G x σ) U := by
  intro x₀ hx₀
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  set r := ε / 3 with hrdef
  have hr : 0 < r := by positivity
  have hsub : ∀ x ∈ ball x₀ r, closedBall x r ⊆ U := by
    intro x hx w hw
    apply hεU
    rw [mem_ball] at hx ⊢
    rw [mem_closedBall] at hw
    calc dist w x₀ ≤ dist w x + dist x x₀ := dist_triangle _ _ _
      _ < r + r + r := by linarith
      _ = ε := by rw [hrdef]; ring
  set μ := volume.restrict (Ioc a b) with hμ
  have hfun : (fun x => ∫ σ in a..b, G x σ) = fun x => ∫ σ, G x σ ∂μ :=
    funext fun x => intervalIntegral.integral_of_le hab
  rw [hfun]
  have hfin : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hσ : ∀ᵐ σ ∂μ, σ ∈ Ioc a b := ae_restrict_mem measurableSet_Ioc
  have hderiv_bd : ∀ σ ∈ Ioc a b, ∀ x ∈ ball x₀ r, ‖fderiv ℂ (G · σ) x‖ ≤ B / r :=
    fun σ hσ x hx => SCV.norm_fderiv_le_of_forall_mem_closedBall_norm_le hr (hdiff σ hσ) hU
      (hsub x hx) (fun w hw => hbd w (hsub x hx hw) σ hσ)
  -- measurability of the derivative at `x₀`, from difference quotients
  have hF'meas : AEStronglyMeasurable (fun σ => fderiv ℂ (G · σ) x₀) μ := by
    apply aestronglyMeasurable_clm_of_forall
    intro v
    obtain ⟨N, hN⟩ := exists_nat_gt (‖v‖ / r)
    set c : ℕ → ℂ := fun n => ((n + N + 1 : ℕ) : ℂ) with hc
    have hcpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + N + 1 := fun n => by positivity
    have hmem : ∀ n, x₀ + (c n)⁻¹ • v ∈ U := by
      intro n
      apply hsub x₀ (mem_ball_self hr)
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_inv, hc]
      simp only [Complex.norm_natCast]
      push_cast
      rw [inv_mul_le_iff₀ (hcpos n)]
      rw [div_lt_iff₀ hr] at hN
      nlinarith [norm_nonneg v, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n σ => c n • (G (x₀ + (c n)⁻¹ • v) σ - G x₀ σ)) (fun n => ?_) ?_
    · exact ((hmeas _ (hmem n)).sub (hmeas x₀ hx₀)).const_smul (c n)
    · filter_upwards [hσ] with σ hσ'
      have hD : HasFDerivAt (G · σ) (fderiv ℂ (G · σ) x₀) x₀ :=
        ((hdiff σ hσ') x₀ hx₀).differentiableAt (hU.mem_nhds hx₀) |>.hasFDerivAt
      refine hD.lim v ?_
      simp only [hc, Complex.norm_natCast]
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat (N + 1))
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (μ := μ)
    (F := fun x σ => G x σ) (F' := fun x σ => fderiv ℂ (G · σ) x) (x₀ := x₀)
    (bound := fun _ => B / r) (ball_mem_nhds x₀ hr)
    (Filter.eventually_of_mem (hU.mem_nhds hx₀) fun x hx => hmeas x hx)
    (Integrable.of_bound (hmeas x₀ hx₀) B (hσ.mono fun σ hσ => hbd x₀ hx₀ σ hσ)) hF'meas
    (hσ.mono fun σ hσ x hx => hderiv_bd σ hσ x hx) (integrable_const _)
    (hσ.mono fun σ hσ x hx => ((hdiff σ hσ) x (hsub x hx (mem_closedBall_self hr.le))
      |>.differentiableAt (hU.mem_nhds (hsub x hx (mem_closedBall_self hr.le)))).hasFDerivAt)
  exact key.differentiableAt.differentiableWithinAt

end ParamIntegral

/-! ### Short-time holomorphy of the Picard solution -/

section ShortTimeLoewner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] {h : ℝ → E → E}

omit [CompleteSpace E] in
/-- **Short-time holomorphy of the Picard iterates.** If `M T₀ ≤ ρ - r` (`M = 4ρ/(1-ρ)²`), the
iterates for the field retracted to `closedBall 0 ρ` are holomorphic in the initial value on
`ball 0 r`, for times in `[0, T₀]`. -/
theorem differentiableOn_iter (hh : IsHerglotzVF h) {ρ r T₀ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hT₀ : 4 * ρ / (1 - ρ) ^ 2 * T₀ ≤ ρ - r) (n : ℕ) :
    ∀ τ ∈ Icc 0 T₀,
      DifferentiableOn ℂ (fun x => Picard.iter (retractedField h ρ) x n τ) (ball 0 r) := by
  set G := retractedField h ρ with hG
  set M := 4 * ρ / (1 - ρ) ^ 2 with hM
  have hlip := lipschitzWith_retractedField hh hρ hρ1
  have hbd := norm_retractedField_le hh hρ hρ1
  have hmeas := aestronglyMeasurable_retractedField hh hρ hρ1
  have hstay : ∀ m, ∀ x ∈ ball (0 : E) r, ∀ σ ∈ Icc 0 T₀, ‖Picard.iter G x m σ‖ ≤ ρ := by
    intro m x hx σ hσ
    have h1 := Picard.norm_iter_sub_le hbd x m hσ.1
    have hx' : ‖x‖ < r := mem_ball_zero_iff.mp hx
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hbd 0 0)
    calc ‖Picard.iter G x m σ‖ = ‖(Picard.iter G x m σ - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖Picard.iter G x m σ - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ M * T₀ + r := by
          have : M * σ ≤ M * T₀ := mul_le_mul_of_nonneg_left hσ.2 hM0
          linarith
      _ ≤ ρ := by linarith
  induction n with
  | zero => intro τ _; exact differentiableOn_id
  | succ n ih =>
    intro τ hτ
    show DifferentiableOn ℂ (fun x => x - ∫ s in (0)..τ, G s (Picard.iter G x n s)) (ball 0 r)
    refine differentiableOn_id.sub
      (differentiableOn_intervalIntegral isOpen_ball hτ.1 ?_ ?_ (B := M) ?_)
    · intro x _
      exact (Picard.aestronglyMeasurable_comp (fun s => (hlip s).continuous) hmeas
        (Picard.continuous_iter hlip hbd hmeas x n).stronglyMeasurable).restrict
    · intro σ hσ
      have hσ' : σ ∈ Icc 0 T₀ := ⟨hσ.1.le, hσ.2.trans hτ.2⟩
      have hcomp : DifferentiableOn ℂ (fun x => h σ (Picard.iter G x n σ)) (ball 0 r) :=
        (hh.isCaratheodory σ hσ'.1).isNormalized.differentiableOn.comp (ih σ hσ')
          (fun x hx => mem_unitBall.mpr ((hstay n x hx σ hσ').trans_lt hρ1))
      refine hcomp.congr fun x hx => ?_
      show G σ (Picard.iter G x n σ) = h σ (Picard.iter G x n σ)
      rw [hG, retractedField_of_nonneg hσ'.1, radialRetraction_of_norm_le hρ (hstay n x hx σ hσ')]
    · intro x _ σ _
      exact hbd σ _

/-- **Short-time holomorphy of the solution** of the retracted equation (Weierstrass). -/
theorem differentiableOn_sol (hh : IsHerglotzVF h) {ρ r T₀ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hT₀ : 4 * ρ / (1 - ρ) ^ 2 * T₀ ≤ ρ - r) {τ : ℝ} (hτ : τ ∈ Icc 0 T₀) :
    DifferentiableOn ℂ (fun x => Picard.sol (retractedField h ρ) x τ) (ball 0 r) := by
  set G := retractedField h ρ with hG
  have hlip := lipschitzWith_retractedField hh hρ hρ1
  have hbd := norm_retractedField_le hh hρ hρ1
  have hmeas := aestronglyMeasurable_retractedField hh hρ hρ1
  refine SCV.differentiableOn_of_tendstoUniformlyOn isOpen_ball
    (G := fun n x => Picard.iter G x n τ) (fun n => differentiableOn_iter hh hρ hρ1 hT₀ n τ hτ) ?_
  have hT := tendstoUniformlyOn_tsum_nat (Picard.summable_majorant τ) (s := ball (0 : E) r)
    (f := fun n x => Picard.iter G x (n + 1) τ - Picard.iter G x n τ)
    (fun n x _ => Picard.norm_iter_succ_sub_le' hlip hbd hmeas x n hτ.1)
  rw [Metric.tendstoUniformlyOn_iff] at hT ⊢
  intro ε hε
  filter_upwards [hT ε hε] with N hN x hx
  have h1 : Picard.iter G x N τ =
      x + ∑ n ∈ Finset.range N, (Picard.iter G x (n + 1) τ - Picard.iter G x n τ) := by
    rw [Finset.sum_range_sub (fun i => Picard.iter G x i τ)]
    show _ = x + (_ - x)
    abel
  have h2 : Picard.sol G x τ = x + ∑' n, (Picard.iter G x (n + 1) τ - Picard.iter G x n τ) := rfl
  rw [h1, h2, dist_add_left]
  exact hN x hx

end ShortTimeLoewner

/-! ### Time shifts -/

section Shift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {h v : ℝ → E → E}

omit [CompleteSpace E] in
/-- The time-shifted field `σ ↦ h(s + σ)` is again a Herglotz vector field. -/
lemma IsHerglotzVF.shift (hh : IsHerglotzVF h) {s : ℝ} (hs : 0 ≤ s) :
    IsHerglotzVF (fun σ => h (s + σ)) where
  isCaratheodory t ht := hh.isCaratheodory (s + t) (by linarith)
  aestronglyMeasurable z hz := by
    have hqmp : Measure.QuasiMeasurePreserving (fun σ : ℝ => s + σ)
        (volume.restrict (Ici 0)) (volume.restrict (Ici 0)) :=
      (measurePreserving_add_left volume s).quasiMeasurePreserving.restrict
        (fun σ hσ => by simp only [mem_Ici] at hσ ⊢; linarith)
    exact (hh.aestronglyMeasurable z hz).comp_quasiMeasurePreserving hqmp

omit [CompleteSpace E] in
/-- A solution of the Loewner ODE, restarted at time `s`, solves the shifted equation. -/
lemma IsLoewnerSolution.isLoewnerCurve_shift (hv : IsLoewnerSolution h v) {z : E}
    (hz : z ∈ unitBall E) {s : ℝ} (hs : 0 ≤ s) :
    IsLoewnerCurve (fun σ => h (s + σ)) (v s z) (fun τ => v (s + τ) z) := by
  intro τ hτ
  have hint := hv.intervalIntegrable_of_le hz hs (le_add_of_nonneg_right hτ)
  have hint' : IntervalIntegrable (fun σ => h (s + σ) (v (s + σ) z)) volume 0 τ := by
    have := hint.comp_add_left s
    simpa using this
  refine ⟨hv.mem_unitBall hz (by linarith), hint', ?_⟩
  show v (s + τ) z = v s z - ∫ σ in (0)..τ, h (s + σ) (v (s + σ) z)
  rw [hv.eq_integral hz (by linarith : 0 ≤ s + τ), hv.eq_integral hz hs]
  have h1 := intervalIntegral.integral_interval_sub_left
    (hv z hz (s + τ) (by linarith)).2.1 (hv z hz s hs).2.1
  have h2 : ∫ σ in (0)..τ, h (s + σ) (v (s + σ) z) = ∫ σ in s..(s + τ), h σ (v σ z) := by
    have := intervalIntegral.integral_comp_add_left (fun σ => h σ (v σ z)) (a := 0) (b := τ) s
    simpa using this
  rw [h2, ← h1]
  abel

end Shift

/-! ### Holomorphy of `z ↦ v(z, t)` -/

section Holo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] {h v : ℝ → E → E}

/-- **The solution of the Loewner ODE depends holomorphically on the initial value.** -/
theorem IsLoewnerSolution.differentiableOn (hh : IsHerglotzVF h) (hv : IsLoewnerSolution h v)
    {t : ℝ} (ht : 0 ≤ t) : DifferentiableOn ℂ (v t) (unitBall E) := by
  -- it suffices to prove holomorphy on `ball 0 r` for every `r < 1`
  suffices H : ∀ r : ℝ, 0 < r → r < 1 → DifferentiableOn ℂ (v t) (ball 0 r) by
    intro z hz
    have hz1 : ‖z‖ < 1 := LoewnerS0.mem_unitBall.mp hz
    have hr := H ((1 + ‖z‖) / 2) (by positivity) (by linarith)
    have hzr : z ∈ ball (0 : E) ((1 + ‖z‖) / 2) := by
      rw [mem_ball_zero_iff]; linarith
    exact ((hr z hzr).differentiableAt (isOpen_ball.mem_nhds hzr)).differentiableWithinAt
  intro r hr0 hr1
  set ρ := (1 + r) / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith
  have hrρ : r < ρ := by rw [hρdef]; linarith
  set M := 4 * ρ / (1 - ρ) ^ 2 with hM
  have hM0 : 0 < M := by
    have : 0 < 1 - ρ := by linarith
    positivity
  set T₀ := (ρ - r) / M with hT₀def
  have hT₀ : 0 < T₀ := div_pos (by linarith) hM0
  have hMT : M * T₀ ≤ ρ - r := by rw [hT₀def, mul_div_cancel₀ _ hM0.ne']
  -- the norm decreases, so `v s` maps `ball 0 r` into itself
  have hmaps : ∀ s, 0 ≤ s → MapsTo (v s) (ball (0 : E) r) (ball 0 r) := by
    intro s hs x hx
    have hx1 : x ∈ unitBall E := LoewnerS0.mem_unitBall.mpr ((mem_ball_zero_iff.mp hx).trans hr1)
    rw [mem_ball_zero_iff] at hx ⊢
    exact (hv.norm_le hh hx1 hs).trans_lt hx
  -- induction on the number of steps of length `T₀`
  have step : ∀ n : ℕ, ∀ t ∈ Icc 0 (n * T₀), DifferentiableOn ℂ (v t) (ball 0 r) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have ht0 : t = 0 := le_antisymm (by simpa using ht.2) ht.1
      subst ht0
      refine differentiableOn_id.congr fun x hx => ?_
      exact hv.apply_zero (LoewnerS0.mem_unitBall.mpr ((mem_ball_zero_iff.mp hx).trans hr1))
    | succ n ih =>
      intro t ht
      set s := max 0 (t - T₀) with hsdef
      have hs0 : 0 ≤ s := le_max_left _ _
      have hsn : s ∈ Icc 0 (n * T₀) := by
        refine ⟨hs0, max_le (by positivity) ?_⟩
        have := ht.2
        push_cast at this
        linarith
      set τ := t - s with hτdef
      have hτ : τ ∈ Icc 0 T₀ := by
        constructor
        · rw [hτdef]; linarith [le_max_right 0 (t - T₀), ht.1, show s ≤ t from
            max_le ht.1 (by linarith)]
        · rw [hτdef]; linarith [le_max_right 0 (t - T₀)]
      have hts : t = s + τ := by rw [hτdef]; ring
      -- `v t = Φ ∘ v s` on `ball 0 r`, with `Φ` the short-time solution map of the shifted field
      have hhs := hh.shift hs0
      have hΦ := differentiableOn_sol hhs hρ hρ1 hMT hτ
      have heq : EqOn (v t)
          ((fun y => Picard.sol (retractedField (fun σ => h (s + σ)) ρ) y τ) ∘ v s)
          (ball 0 r) := by
        intro x hx
        have hx1 : x ∈ unitBall E :=
          LoewnerS0.mem_unitBall.mpr ((mem_ball_zero_iff.mp hx).trans hr1)
        have hy : ‖v s x‖ ≤ ρ := (mem_ball_zero_iff.mp (hmaps s hs0 hx)).le.trans hrρ.le
        have hc1 := hv.isLoewnerCurve_shift hx1 hs0
        have hc2 := isLoewnerCurve_sol hhs hρ hρ1 hy
        have := IsLoewnerCurve.eq hhs (hv.mem_unitBall hx1 hs0) hc1 hc2 hτ.1
        simp only [Function.comp_apply]
        rw [hts]
        exact this
      exact (hΦ.comp (ih s hsn) (hmaps s hs0)).congr heq
  obtain ⟨n, hn⟩ := exists_nat_ge (t / T₀)
  refine step n t ⟨ht, ?_⟩
  rwa [div_le_iff₀ hT₀] at hn

end Holo

end LoewnerS0
