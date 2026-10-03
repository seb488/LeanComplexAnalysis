import LoewnerS0.ClassM
import LoewnerS0.Flow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The Loewner ODE: uniqueness, decay and the parametric representation

Let `h` be a Herglotz vector field on the unit ball `𝔹` of a finite-dimensional complex inner
product space and `v` a solution of the Loewner ODE `∂ₜ v = -h(v, t)`, `v(z, 0) = z`, in the
integral (Carathéodory) sense of `LoewnerS0.IsLoewnerSolution`. Since `t ↦ h(·, t)` is only
measurable, `t ↦ v(z, t)` is only absolutely continuous; we use mathlib's fundamental theorem of
calculus for absolutely continuous functions and the Lebesgue differentiation theorem.

## Main results

* `IsLoewnerSolution.norm_le_norm`: `t ↦ ‖v(z, t)‖` is nonincreasing.
* `IsLoewnerSolution.eqOn_of_isHerglotzVF`: **uniqueness** of solutions (Gronwall).
* `IsLoewnerSolution.growth_upper`, `IsLoewnerSolution.growth_lower`: along a solution,
  `eᵗ r/(1-r)²` is nonincreasing and `eᵗ r/(1+r)²` is nondecreasing (`r = ‖v(z, t)‖`), by the
  Pfaltzgraff estimates for `M(𝔹)`.
* `IsLoewnerSolution.exists_isParametricRep`: the limit `f(z) = lim_{t → ∞} eᵗ v(z, t)` exists,
  so every solution of the Loewner ODE defines an element of `S⁰(𝔹)`.
* `classS0_norm_bounds`: the **growth theorem** `‖z‖/(1+‖z‖)² ≤ ‖f(z)‖ ≤ ‖z‖/(1-‖z‖)²` on `S⁰(𝔹)`.
-/

open Complex Metric Set Filter MeasureTheory
open scoped InnerProductSpace Topology NNReal

noncomputable section

namespace LoewnerS0

/-! ### Absolutely continuous functions -/

section AC

/-- An absolutely continuous function whose derivative is a.e. nonnegative is monotone. -/
theorem AbsolutelyContinuousOnInterval.le_of_ae_deriv_nonneg {F F' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : AbsolutelyContinuousOnInterval F a b)
    (hd : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt F (F' x) x ∧ 0 ≤ F' x) : F a ≤ F b := by
  have h1 := hF.integral_deriv_eq_sub
  have ha : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff, measure_singleton]
  have hb : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
  have h2 : 0 ≤ ∫ x in a..b, deriv F x := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hab
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hd, ha, hb] with x hx hxa hxb hxI
    have hx' : x ∈ Ioo a b := ⟨lt_of_le_of_ne hxI.1 (Ne.symm hxa), lt_of_le_of_ne hxI.2 hxb⟩
    obtain ⟨hD, hpos⟩ := hx hx'
    show 0 ≤ deriv F x
    rw [hD.deriv]
    exact hpos
  linarith

/-- **Gronwall's inequality** for absolutely continuous functions. -/
theorem AbsolutelyContinuousOnInterval.le_mul_exp {ψ ψ' : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hd : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt ψ (ψ' x) x ∧ ψ' x ≤ K * ψ x) :
    ψ b ≤ ψ a * Real.exp (K * (b - a)) := by
  have hexp : AbsolutelyContinuousOnInterval (fun x => Real.exp (-(K * x))) a b :=
    ContDiffOn.absolutelyContinuousOnInterval
      (ContDiff.exp ((contDiff_const.mul contDiff_id).neg)).contDiffOn
  have hFac : AbsolutelyContinuousOnInterval (fun x => -(Real.exp (-(K * x)) * ψ x)) a b :=
    (hexp.fun_mul hψ).fun_neg
  have hmono := AbsolutelyContinuousOnInterval.le_of_ae_deriv_nonneg hab hFac
    (F' := fun x => -(Real.exp (-(K * x)) * (ψ' x - K * ψ x))) (by
      filter_upwards [hd] with x hx hxI
      obtain ⟨hD, hle⟩ := hx hxI
      refine ⟨?_, ?_⟩
      · have he : HasDerivAt (fun x => Real.exp (-(K * x))) (Real.exp (-(K * x)) * -(K * 1)) x :=
          (((hasDerivAt_id x).const_mul K).neg).exp
        convert (he.mul hD).neg using 1
        ring
      · have : 0 ≤ Real.exp (-(K * x)) * (K * ψ x - ψ' x) :=
          mul_nonneg (Real.exp_pos _).le (by linarith)
        linarith)
  have h2 : Real.exp (-(K * b)) * ψ b ≤ Real.exp (-(K * a)) * ψ a := by
    linarith
  have h3 : ψ b = Real.exp (K * b) * (Real.exp (-(K * b)) * ψ b) := by
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [h3]
  calc Real.exp (K * b) * (Real.exp (-(K * b)) * ψ b)
      ≤ Real.exp (K * b) * (Real.exp (-(K * a)) * ψ a) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = ψ a * Real.exp (K * (b - a)) := by
        rw [mul_comm (Real.exp (-(K * a))), ← mul_assoc, mul_comm (Real.exp (K * b)), mul_assoc,
          ← Real.exp_add]
        ring_nf

end AC

/-! ### Norm squares of Lipschitz curves -/

section NormSq

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [InnerProductSpace ℂ E] in
lemma lipschitzOnWith_norm_sq {R : ℝ} (hR : 0 ≤ R) :
    LipschitzOnWith (2 * R).toNNReal (fun x : E => ‖x‖ ^ 2) (closedBall 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hy' : ‖y‖ ≤ R := by simpa using hy
  have hd := abs_le.mp (abs_norm_sub_norm_le x y)
  have hxy : 0 ≤ ‖x‖ + ‖y‖ := by positivity
  rw [abs_le]
  constructor <;> nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x - y)]

omit [InnerProductSpace ℂ E] in
lemma absolutelyContinuousOnInterval_norm_sq {γ : ℝ → E} {a b R : ℝ} {K : ℝ≥0} (hR : 0 ≤ R)
    (hγ : LipschitzOnWith K γ (uIcc a b)) (hbd : ∀ τ ∈ uIcc a b, ‖γ τ‖ ≤ R) :
    AbsolutelyContinuousOnInterval (fun τ => ‖γ τ‖ ^ 2) a b :=
  ((lipschitzOnWith_norm_sq hR).comp hγ
    (fun τ hτ => mem_closedBall_zero_iff.mpr (hbd τ hτ))).absolutelyContinuousOnInterval

lemma hasDerivAt_norm_sq {γ : ℝ → E} {γ' : E} {t : ℝ} (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun τ => ‖γ τ‖ ^ 2) (2 * (⟪γ t, γ'⟫_ℂ).re) t :=
  hasDerivWithinAt_univ.mp (hasDerivWithinAt_norm_sq hγ.hasDerivWithinAt)

end NormSq

/-! ### Basic properties of solutions -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {h v w : ℝ → E → E}

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
lemma growthBound_nonneg {z : E} (hz : z ∈ unitBall E) : 0 ≤ 4 * ‖z‖ / (1 - ‖z‖) ^ 2 := by
  have : 0 < 1 - ‖z‖ := by linarith [mem_unitBall.mp hz]
  positivity

namespace IsLoewnerSolution

section Basic

variable (hv : IsLoewnerSolution h v) {z : E} (hz : z ∈ unitBall E)
include hv hz

omit [CompleteSpace E] in
lemma intervalIntegrable_of_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    IntervalIntegrable (fun τ => h τ (v τ z)) volume s t := by
  have h1 := (hv z hz t (hs.trans hst)).2.1
  refine h1.mono_set ?_
  rw [uIcc_of_le (hs.trans hst), uIcc_of_le hst]
  exact Icc_subset_Icc hs le_rfl

omit [CompleteSpace E] in
lemma continuousOn {T : ℝ} (hT : 0 ≤ T) : ContinuousOn (fun t => v t z) (Icc 0 T) := by
  have hint := (hv z hz T hT).2.1
  have h1 := intervalIntegral.continuousOn_primitive_interval' hint (a := 0) left_mem_uIcc
  rw [uIcc_of_le hT] at h1
  exact ((continuousOn_const (c := z)).sub h1).congr fun t ht => hv.eq_integral hz ht.1

omit [CompleteSpace E] in
/-- On a compact time interval a solution stays in a closed ball of radius `< 1`. -/
lemma exists_radius {T : ℝ} (hT : 0 ≤ T) :
    ∃ ρ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ t ∈ Icc 0 T, ‖v t z‖ ≤ ρ := by
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
    (hv.continuousOn hz hT).norm
  exact ⟨‖v t₀ z‖, norm_nonneg _, LoewnerS0.mem_unitBall.mp (hv.mem_unitBall hz ht₀.1),
    fun t ht => hmax ht⟩

omit [CompleteSpace E] in
/-- A solution is Lipschitz on `[0, T]` if its velocity is bounded there. -/
lemma lipschitzOnWith {T M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ t ∈ Icc 0 T, ‖h t (v t z)‖ ≤ M) :
    LipschitzOnWith M.toNNReal (fun t => v t z) (Icc 0 T) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [dist_eq_norm, hv.eq_integral hz hs.1, hv.eq_integral hz ht.1, sub_sub_sub_cancel_left,
    intervalIntegral.integral_interval_sub_left (hv z hz t ht.1).2.1 (hv z hz s hs.1).2.1,
    Real.coe_toNNReal _ hM0]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := M) fun x hx => ?_).trans ?_
  · refine hM x ⟨?_, ?_⟩
    · exact (le_min hs.1 ht.1).trans hx.1.le
    · exact hx.2.trans (max_le hs.2 ht.2)
  · rw [Real.dist_eq, abs_sub_comm]

/-- The Loewner ODE holds almost everywhere. -/
lemma ae_hasDerivAt {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt (fun τ => v τ z) (-h t (v t z)) t := by
  have hint := (hv z hz T hT).2.1
  filter_upwards [hint.ae_hasDerivAt_integral] with t ht htI
  have htI' : t ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact Ioo_subset_Icc_self htI
  have hD := (ht htI' 0 left_mem_uIcc).const_sub z
  apply hD.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds htI.1] with τ hτ
  exact hv.eq_integral hz (le_of_lt hτ)

end Basic

variable [FiniteDimensional ℂ E]

section Decay

variable (hh : IsHerglotzVF h) (hv : IsLoewnerSolution h v) {z : E} (hz : z ∈ unitBall E)
include hh hv hz

/-- **The norm of a solution is nonincreasing.** -/
theorem norm_le_norm {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : ‖v t z‖ ≤ ‖v s z‖ := by
  have ht : 0 ≤ t := hs.trans hst
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := hv.exists_radius hz ht
  have hM0 : 0 ≤ 4 * ρ / (1 - ρ) ^ 2 := by
    have : 0 < 1 - ρ := by linarith
    positivity
  have hM : ∀ τ ∈ Icc 0 t, ‖h τ (v τ z)‖ ≤ 4 * ρ / (1 - ρ) ^ 2 := fun τ hτ =>
    (hh.isCaratheodory τ hτ.1).norm_le_of_norm_le hρ1 (hρ τ hτ)
  have hsub : uIcc s t ⊆ Icc 0 t := by rw [uIcc_of_le hst]; exact Icc_subset_Icc hs le_rfl
  have hlip := (hv.lipschitzOnWith hz hM0 hM).mono hsub
  have hac : AbsolutelyContinuousOnInterval (fun τ => -‖v τ z‖ ^ 2) s t :=
    (absolutelyContinuousOnInterval_norm_sq (R := 1) zero_le_one hlip
      (fun τ hτ => (hρ τ (hsub hτ)).trans hρ1.le)).fun_neg
  have hmono := AbsolutelyContinuousOnInterval.le_of_ae_deriv_nonneg hst hac
    (F' := fun τ => 2 * (⟪v τ z, h τ (v τ z)⟫_ℂ).re) (by
      filter_upwards [hv.ae_hasDerivAt hz ht] with τ hτ hτI
      have hτI' : τ ∈ Ioo 0 t := ⟨lt_of_le_of_lt hs hτI.1, hτI.2⟩
      refine ⟨?_, ?_⟩
      · convert (hasDerivAt_norm_sq (hτ hτI')).neg using 1
        rw [inner_neg_right, Complex.neg_re]
        ring
      · have := (hh.isCaratheodory τ hτI'.1.le).re_inner_nonneg
          (hv.mem_unitBall hz hτI'.1.le)
        linarith)
  have : ‖v t z‖ ^ 2 ≤ ‖v s z‖ ^ 2 := by linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

theorem norm_le {t : ℝ} (ht : 0 ≤ t) : ‖v t z‖ ≤ ‖z‖ := by
  have := hv.norm_le_norm hh hz le_rfl ht
  rwa [hv.apply_zero hz] at this

/-- The velocity of a solution is bounded by `4‖z‖/(1-‖z‖)²`. -/
theorem norm_velocity_le {t : ℝ} (ht : 0 ≤ t) :
    ‖h t (v t z)‖ ≤ 4 * ‖z‖ / (1 - ‖z‖) ^ 2 :=
  (hh.isCaratheodory t ht).norm_le_of_norm_le (LoewnerS0.mem_unitBall.mp hz)
    (hv.norm_le hh hz ht)

/-- A solution is Lipschitz in time, uniformly on `[0, ∞)`. -/
theorem lipschitzOnWith_Ici :
    LipschitzOnWith (4 * ‖z‖ / (1 - ‖z‖) ^ 2).toNNReal (fun t => v t z) (Ici 0) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  have hT : 0 ≤ max s t := le_max_of_le_left hs
  have := hv.lipschitzOnWith hz (T := max s t) (growthBound_nonneg hz)
    (fun τ hτ => hv.norm_velocity_le hh hz hτ.1)
  exact this.dist_le_mul s ⟨hs, le_max_left _ _⟩ t ⟨ht, le_max_right _ _⟩

end Decay

/-- **Uniqueness of solutions of the Loewner ODE** [GHK02]. -/
theorem eqOn_of_isHerglotzVF (hh : IsHerglotzVF h) (hv : IsLoewnerSolution h v)
    (hw : IsLoewnerSolution h w) {t : ℝ} (ht : 0 ≤ t) : EqOn (v t) (w t) (unitBall E) := by
  intro z hz
  set ρ := ‖z‖ with hρdef
  have hρ1 : ρ < 1 := LoewnerS0.mem_unitBall.mp hz
  have hρ0 : 0 ≤ ρ := norm_nonneg z
  set L : ℝ := 32 / (1 - ρ) ^ 3 with hLdef
  have hL0 : 0 ≤ L := by
    have : 0 < 1 - ρ := by linarith
    positivity
  set M : ℝ := 4 * ρ / (1 - ρ) ^ 2 with hMdef
  have hM0 : 0 ≤ M := growthBound_nonneg hz
  have hvlip := (hv.lipschitzOnWith_Ici hh hz).mono
    (show uIcc 0 t ⊆ Ici 0 by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)
  have hwlip := (hw.lipschitzOnWith_Ici hh hz).mono
    (show uIcc 0 t ⊆ Ici 0 by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)
  -- the difference
  set Δ : ℝ → E := fun τ => v τ z - w τ z with hΔ
  have hΔlip : LipschitzOnWith (M.toNNReal + M.toNNReal) Δ (uIcc 0 t) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    have h1 := hvlip.dist_le_mul a ha b hb
    have h2 := hwlip.dist_le_mul a ha b hb
    calc dist (Δ a) (Δ b) ≤ dist (v a z) (v b z) + dist (w a z) (w b z) := by
          simp only [hΔ]
          rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
          calc ‖v a z - w a z - (v b z - w b z)‖ = ‖(v a z - v b z) - (w a z - w b z)‖ := by
                congr 1; abel
            _ ≤ ‖v a z - v b z‖ + ‖w a z - w b z‖ := norm_sub_le _ _
      _ ≤ _ := by push_cast; nlinarith
  have hΔbd : ∀ τ ∈ uIcc 0 t, ‖Δ τ‖ ≤ 2 := by
    intro τ hτ
    rw [uIcc_of_le ht] at hτ
    calc ‖Δ τ‖ ≤ ‖v τ z‖ + ‖w τ z‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add ((hv.norm_le hh hz hτ.1).trans hρ1.le)
          ((hw.norm_le hh hz hτ.1).trans hρ1.le)
      _ = 2 := by norm_num
  have hac := absolutelyContinuousOnInterval_norm_sq (by norm_num) hΔlip hΔbd
  have hgr := AbsolutelyContinuousOnInterval.le_mul_exp ht hac (K := 2 * L)
    (ψ' := fun τ => 2 * (⟪Δ τ, -h τ (v τ z) - -h τ (w τ z)⟫_ℂ).re) (by
      filter_upwards [hv.ae_hasDerivAt hz ht, hw.ae_hasDerivAt hz ht] with τ hτv hτw hτI
      refine ⟨hasDerivAt_norm_sq ((hτv hτI).sub (hτw hτI)), ?_⟩
      have hτ0 : 0 ≤ τ := hτI.1.le
      have hlipτ := (hh.isCaratheodory τ hτ0).lipschitzOnWith hρ1
      have hdist := hlipτ.dist_le_mul (v τ z)
        (mem_closedBall_zero_iff.mpr (hv.norm_le hh hz hτ0)) (w τ z)
        (mem_closedBall_zero_iff.mpr (hw.norm_le hh hz hτ0))
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0] at hdist
      have hre : (⟪Δ τ, -h τ (v τ z) - -h τ (w τ z)⟫_ℂ).re ≤
          ‖Δ τ‖ * ‖h τ (v τ z) - h τ (w τ z)‖ := by
        refine (Complex.re_le_norm _).trans ?_
        refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
        congr 1
        rw [← norm_neg]
        congr 1
        abel
      have : ‖Δ τ‖ * ‖h τ (v τ z) - h τ (w τ z)‖ ≤ ‖Δ τ‖ * (L * ‖Δ τ‖) :=
        mul_le_mul_of_nonneg_left hdist (norm_nonneg _)
      nlinarith)
  have h0 : ‖Δ 0‖ ^ 2 = 0 := by
    simp only [hΔ, hv.apply_zero hz, hw.apply_zero hz, sub_self, norm_zero]
    norm_num
  rw [h0, zero_mul] at hgr
  have : ‖Δ t‖ = 0 := by nlinarith [norm_nonneg (Δ t)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- `r/(1-r)²` has derivative `(1+r)/(1-r)³`. -/
lemma hasDerivAt_koebe_minus {r : ℝ} (hr : r < 1) :
    HasDerivAt (fun r : ℝ => r / (1 - r) ^ 2) ((1 + r) / (1 - r) ^ 3) r := by
  have h1 : (1 - r) ^ 2 ≠ 0 := by have : 0 < 1 - r := by linarith
                                  positivity
  have hd := (hasDerivAt_id r).div (((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).pow 2) h1
  have : 1 - r ≠ 0 := by linarith
  convert hd using 1
  · rfl
  · simp only [Pi.sub_apply, Pi.pow_apply, id]
    field_simp
    ring

/-- `r/(1+r)²` has derivative `(1-r)/(1+r)³`. -/
lemma hasDerivAt_koebe_plus {r : ℝ} (hr : -1 < r) :
    HasDerivAt (fun r : ℝ => r / (1 + r) ^ 2) ((1 - r) / (1 + r) ^ 3) r := by
  have h1 : (1 + r) ^ 2 ≠ 0 := by have : 0 < 1 + r := by linarith
                                  positivity
  have hd := (hasDerivAt_id r).div (((hasDerivAt_const r (1 : ℝ)).add (hasDerivAt_id r)).pow 2) h1
  have : 1 + r ≠ 0 := by linarith
  convert hd using 1
  · rfl
  · simp only [Pi.add_apply, Pi.pow_apply, id]
    field_simp
    ring

lemma lipschitzOnWith_koebe_minus {ρ : ℝ} (hρ : ρ < 1) :
    ∃ L, LipschitzOnWith L (fun r : ℝ => r / (1 - r) ^ 2) (Icc 0 ρ) := by
  refine ContDiffOn.exists_lipschitzOnWith ?_ one_ne_zero (convex_Icc _ _) isCompact_Icc
  refine contDiffOn_id.div ((contDiffOn_const.sub contDiffOn_id).pow 2) fun r hr => ?_
  have : 0 < 1 - r := by linarith [hr.2]
  positivity

lemma lipschitzOnWith_koebe_plus (ρ : ℝ) :
    ∃ L, LipschitzOnWith L (fun r : ℝ => r / (1 + r) ^ 2) (Icc 0 ρ) := by
  refine ContDiffOn.exists_lipschitzOnWith ?_ one_ne_zero (convex_Icc _ _) isCompact_Icc
  refine contDiffOn_id.div ((contDiffOn_const.add contDiffOn_id).pow 2) fun r hr => ?_
  have : 0 < 1 + r := by linarith [hr.1]
  positivity

omit [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] in
lemma _root_.LipschitzOnWith.absolutelyContinuousOnInterval_of_Ici {γ : ℝ → E} {K : ℝ≥0}
    (hlip : LipschitzOnWith K γ (Ici 0)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    AbsolutelyContinuousOnInterval γ s t :=
  (hlip.mono (by rw [uIcc_of_le hst]; exact fun τ hτ => hs.trans hτ.1)
    ).absolutelyContinuousOnInterval

section Growth

variable (hh : IsHerglotzVF h) (hv : IsLoewnerSolution h v) {z : E} (hz : z ∈ unitBall E)
include hh hv hz

/-- A solution starting at `z ≠ 0` never reaches `0`. -/
theorem norm_sq_ge {t : ℝ} (ht : 0 ≤ t) :
    ‖z‖ ^ 2 * Real.exp (-(2 * ((1 + ‖z‖) / (1 - ‖z‖))) * t) ≤ ‖v t z‖ ^ 2 := by
  set K := (1 + ‖z‖) / (1 - ‖z‖) with hK
  have hz1 : ‖z‖ < 1 := LoewnerS0.mem_unitBall.mp hz
  have hlip := hv.lipschitzOnWith_Ici hh hz
  have hac : AbsolutelyContinuousOnInterval (fun τ => -‖v τ z‖ ^ 2) 0 t :=
    (absolutelyContinuousOnInterval_norm_sq (R := 1) zero_le_one
      (hlip.mono (by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self))
      (fun τ hτ => by
        rw [uIcc_of_le ht] at hτ
        exact (hv.norm_le hh hz hτ.1).trans hz1.le)).fun_neg
  have hgr := AbsolutelyContinuousOnInterval.le_mul_exp ht hac (K := -(2 * K))
    (ψ' := fun τ => 2 * (⟪v τ z, h τ (v τ z)⟫_ℂ).re) (by
      filter_upwards [hv.ae_hasDerivAt hz ht] with τ hτ hτI
      refine ⟨?_, ?_⟩
      · convert (hasDerivAt_norm_sq (hτ hτI)).neg using 1
        rw [inner_neg_right, Complex.neg_re]
        ring
      · have hτ0 : 0 ≤ τ := hτI.1.le
        have hvτ := hv.mem_unitBall hz hτ0
        have hle := (hh.isCaratheodory τ hτ0).re_inner_le hvτ
        have hr : ‖v τ z‖ ≤ ‖z‖ := hv.norm_le hh hz hτ0
        have hr1 : ‖v τ z‖ < 1 := LoewnerS0.mem_unitBall.mp hvτ
        have hq : (1 + ‖v τ z‖) / (1 - ‖v τ z‖) ≤ K := by
          rw [hK, div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith [norm_nonneg (v τ z)]
        have : ‖v τ z‖ ^ 2 * (1 + ‖v τ z‖) / (1 - ‖v τ z‖) ≤ ‖v τ z‖ ^ 2 * K := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hq (by positivity)
        nlinarith)
  rw [hv.apply_zero hz, sub_zero] at hgr
  linarith

theorem ne_zero (hz0 : z ≠ 0) {t : ℝ} (ht : 0 ≤ t) : v t z ≠ 0 := by
  intro h0
  have := hv.norm_sq_ge hh hz ht
  rw [h0, norm_zero] at this
  have h1 : 0 < ‖z‖ ^ 2 * Real.exp (-(2 * ((1 + ‖z‖) / (1 - ‖z‖))) * t) := by
    have := norm_pos_iff.mpr hz0
    positivity
  linarith [show (0 : ℝ) ^ 2 = 0 by norm_num]

/-- Along a solution, `τ ↦ eᵗ Φ(‖v(z, τ)‖)` is absolutely continuous on compact intervals and
has the expected derivative almost everywhere. -/
lemma exp_mul_comp_norm {Φ Φ' : ℝ → ℝ} {L : ℝ≥0} (hΦlip : LipschitzOnWith L Φ (Icc 0 ‖z‖))
    (hΦ : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt Φ (Φ' r) r) (hz0 : z ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    AbsolutelyContinuousOnInterval (fun τ => Real.exp τ * Φ ‖v τ z‖) s t ∧
      ∀ᵐ τ, τ ∈ Ioo s t → HasDerivAt (fun τ => Real.exp τ * Φ ‖v τ z‖)
        (Real.exp τ * Φ ‖v τ z‖ + Real.exp τ *
          (Φ' ‖v τ z‖ * (-(⟪v τ z, h τ (v τ z)⟫_ℂ).re / ‖v τ z‖))) τ := by
  have ht : 0 ≤ t := hs.trans hst
  have hlip := hv.lipschitzOnWith_Ici hh hz
  have hvac := hlip.absolutelyContinuousOnInterval_of_Ici hs hst
  have hrac : AbsolutelyContinuousOnInterval (fun τ => ‖v τ z‖) s t :=
    LipschitzWith.comp_absolutelyContinuousOnInterval lipschitzWith_one_norm hvac
  have hΦac : AbsolutelyContinuousOnInterval (Φ ∘ fun τ => ‖v τ z‖) s t :=
    hΦlip.comp_absolutelyContinuousOnInterval (fun τ hτ => by
      rw [uIcc_of_le hst] at hτ
      exact ⟨norm_nonneg _, hv.norm_le hh hz (hs.trans hτ.1)⟩) hrac
  have hexp : AbsolutelyContinuousOnInterval Real.exp s t :=
    ContDiffOn.absolutelyContinuousOnInterval Real.contDiff_exp.contDiffOn
  refine ⟨hexp.fun_mul hΦac, ?_⟩
  filter_upwards [hv.ae_hasDerivAt hz ht] with τ hτ hτI
  have hτI' : τ ∈ Ioo 0 t := ⟨lt_of_le_of_lt hs hτI.1, hτI.2⟩
  have hτ0 : 0 ≤ τ := hτI'.1.le
  have hvne := hv.ne_zero hh hz hz0 hτ0
  have hrpos : 0 < ‖v τ z‖ := norm_pos_iff.mpr hvne
  have hr1 : ‖v τ z‖ < 1 := LoewnerS0.mem_unitBall.mp (hv.mem_unitBall hz hτ0)
  -- the derivative of `‖v‖ = √(‖v‖²)`
  have hψ := hasDerivAt_norm_sq (hτ hτI')
  have hsq := hψ.sqrt (by positivity)
  have hnorm : (fun τ => √(‖v τ z‖ ^ 2)) = fun τ => ‖v τ z‖ := by
    funext τ; exact Real.sqrt_sq (norm_nonneg _)
  rw [hnorm, Real.sqrt_sq (norm_nonneg _)] at hsq
  have hr' : HasDerivAt (fun τ => ‖v τ z‖) (-(⟪v τ z, h τ (v τ z)⟫_ℂ).re / ‖v τ z‖) τ := by
    convert hsq using 1
    rw [inner_neg_right, Complex.neg_re]
    field_simp
  have hcomp := (hΦ _ ⟨hrpos, hr1⟩).comp τ hr'
  exact (Real.hasDerivAt_exp τ).fun_mul hcomp

/-- **Upper growth estimate along a solution**: `eᵗ r/(1-r)²` is nonincreasing, `r = ‖v(z, t)‖`. -/
theorem growth_upper {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.exp t * (‖v t z‖ / (1 - ‖v t z‖) ^ 2) ≤ Real.exp s * (‖v s z‖ / (1 - ‖v s z‖) ^ 2) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · have h1 : ∀ τ, 0 ≤ τ → ‖v τ 0‖ = 0 := fun τ hτ =>
      le_antisymm ((hv.norm_le hh hz hτ).trans_eq norm_zero) (norm_nonneg _)
    rw [h1 t (hs.trans hst), h1 s hs]
    simp
  obtain ⟨L, hL⟩ := lipschitzOnWith_koebe_minus (LoewnerS0.mem_unitBall.mp hz)
  obtain ⟨hac, hder⟩ := hv.exp_mul_comp_norm hh hz hL
    (fun r hr => hasDerivAt_koebe_minus hr.2) hz0 hs hst
  have hmono := AbsolutelyContinuousOnInterval.le_of_ae_deriv_nonneg hst hac.fun_neg
    (F' := fun τ => -(Real.exp τ * (‖v τ z‖ / (1 - ‖v τ z‖) ^ 2) + Real.exp τ *
      ((1 + ‖v τ z‖) / (1 - ‖v τ z‖) ^ 3 *
        (-(⟪v τ z, h τ (v τ z)⟫_ℂ).re / ‖v τ z‖)))) (by
      filter_upwards [hder] with τ hτ hτI
      refine ⟨(hτ hτI).fun_neg, ?_⟩
      have hτ0 : 0 ≤ τ := hs.trans hτI.1.le
      have hvτ := hv.mem_unitBall hz hτ0
      set r := ‖v τ z‖ with hr
      have hr0 : 0 < r := norm_pos_iff.mpr (hv.ne_zero hh hz hz0 hτ0)
      have hr1 : r < 1 := LoewnerS0.mem_unitBall.mp hvτ
      set A := (⟪v τ z, h τ (v τ z)⟫_ℂ).re with hA
      have hge : r ^ 2 * (1 - r) / (1 + r) ≤ A := (hh.isCaratheodory τ hτ0).re_inner_ge hvτ
      have h1r : 0 < 1 - r := by linarith
      have hkey : r / (1 - r) ^ 2 + (1 + r) / (1 - r) ^ 3 * (-A / r) =
          (r ^ 2 * (1 - r) - (1 + r) * A) / (r * (1 - r) ^ 3) := by
        field_simp
        ring
      have hnum : r ^ 2 * (1 - r) - (1 + r) * A ≤ 0 := by
        rw [div_le_iff₀ (by linarith)] at hge
        linarith
      have hneg : (r ^ 2 * (1 - r) - (1 + r) * A) / (r * (1 - r) ^ 3) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
      have : Real.exp τ * (r / (1 - r) ^ 2) + Real.exp τ * ((1 + r) / (1 - r) ^ 3 * (-A / r)) =
          Real.exp τ * ((r ^ 2 * (1 - r) - (1 + r) * A) / (r * (1 - r) ^ 3)) := by
        rw [← hkey]; ring
      rw [this]
      have := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos τ).le hneg
      linarith)
  linarith

/-- **Lower growth estimate along a solution**: `eᵗ r/(1+r)²` is nondecreasing. -/
theorem growth_lower {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.exp s * (‖v s z‖ / (1 + ‖v s z‖) ^ 2) ≤ Real.exp t * (‖v t z‖ / (1 + ‖v t z‖) ^ 2) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · have h1 : ∀ τ, 0 ≤ τ → ‖v τ 0‖ = 0 := fun τ hτ =>
      le_antisymm ((hv.norm_le hh hz hτ).trans_eq norm_zero) (norm_nonneg _)
    rw [h1 t (hs.trans hst), h1 s hs]
    simp
  obtain ⟨L, hL⟩ := lipschitzOnWith_koebe_plus ‖z‖
  obtain ⟨hac, hder⟩ := hv.exp_mul_comp_norm hh hz hL
    (fun r hr => hasDerivAt_koebe_plus (by linarith [hr.1])) hz0 hs hst
  refine AbsolutelyContinuousOnInterval.le_of_ae_deriv_nonneg hst hac
    (F' := fun τ => Real.exp τ * (‖v τ z‖ / (1 + ‖v τ z‖) ^ 2) + Real.exp τ *
      ((1 - ‖v τ z‖) / (1 + ‖v τ z‖) ^ 3 * (-(⟪v τ z, h τ (v τ z)⟫_ℂ).re / ‖v τ z‖))) ?_
  filter_upwards [hder] with τ hτ hτI
  refine ⟨hτ hτI, ?_⟩
  have hτ0 : 0 ≤ τ := hs.trans hτI.1.le
  have hvτ := hv.mem_unitBall hz hτ0
  set r := ‖v τ z‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr (hv.ne_zero hh hz hz0 hτ0)
  have hr1 : r < 1 := LoewnerS0.mem_unitBall.mp hvτ
  set A := (⟪v τ z, h τ (v τ z)⟫_ℂ).re with hA
  have hle : A ≤ r ^ 2 * (1 + r) / (1 - r) := (hh.isCaratheodory τ hτ0).re_inner_le hvτ
  have h1r : 0 < 1 - r := by linarith
  have hkey : r / (1 + r) ^ 2 + (1 - r) / (1 + r) ^ 3 * (-A / r) =
      (r ^ 2 * (1 + r) - (1 - r) * A) / (r * (1 + r) ^ 3) := by
    field_simp
    ring
  have hnum : 0 ≤ r ^ 2 * (1 + r) - (1 - r) * A := by
    rw [le_div_iff₀ h1r] at hle
    linarith
  have hpos : 0 ≤ (r ^ 2 * (1 + r) - (1 - r) * A) / (r * (1 + r) ^ 3) :=
    div_nonneg hnum (by positivity)
  have : Real.exp τ * (r / (1 + r) ^ 2) + Real.exp τ * ((1 - r) / (1 + r) ^ 3 * (-A / r)) =
      Real.exp τ * ((r ^ 2 * (1 + r) - (1 - r) * A) / (r * (1 + r) ^ 3)) := by
    rw [← hkey]; ring
  rw [this]
  exact mul_nonneg (Real.exp_pos τ).le hpos

/-- Exponential decay: `‖v(z, t)‖ ≤ e^{-t} ‖z‖/(1-‖z‖)²`. -/
theorem norm_le_exp {t : ℝ} (ht : 0 ≤ t) :
    ‖v t z‖ ≤ Real.exp (-t) * (‖z‖ / (1 - ‖z‖) ^ 2) := by
  have h1 := hv.growth_upper hh hz le_rfl ht
  rw [hv.apply_zero hz, Real.exp_zero, one_mul] at h1
  have hr1 : ‖v t z‖ < 1 := LoewnerS0.mem_unitBall.mp (hv.mem_unitBall hz ht)
  have h2 : ‖v t z‖ ≤ ‖v t z‖ / (1 - ‖v t z‖) ^ 2 := by
    rw [le_div_iff₀ (by nlinarith [norm_nonneg (v t z)])]
    have : (1 - ‖v t z‖) ^ 2 ≤ 1 := by nlinarith [norm_nonneg (v t z)]
    nlinarith [norm_nonneg (v t z)]
  have h3 : Real.exp t * ‖v t z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2 :=
    (mul_le_mul_of_nonneg_left h2 (Real.exp_pos t).le).trans h1
  rw [Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos t), mul_comm]
  exact h3

end Growth

section Limit

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
lemma _root_.LoewnerS0.hasDerivAt_re_inner_const {γ : ℝ → E} {γ' : E} {t : ℝ} (e : E)
    (hγ : HasDerivAt γ γ' t) : HasDerivAt (fun τ => (⟪e, γ τ⟫_ℂ).re) (⟪e, γ'⟫_ℂ).re t := by
  have h1 := HasDerivAt.inner ℂ (hasDerivAt_const t e) hγ
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
  have h3 : Complex.reCLM (⟪e, γ'⟫_ℂ + ⟪(0 : E), γ t⟫_ℂ) = (⟪e, γ'⟫_ℂ).re := by simp
  rw [h3] at h2
  exact h2

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
lemma _root_.LoewnerS0.lipschitzWith_re_inner (e : E) :
    LipschitzWith ‖e‖₊ (fun x : E => (⟪e, x⟫_ℂ).re) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm, coe_nnnorm, ← Complex.sub_re, ← inner_sub_right]
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)

variable (hh : IsHerglotzVF h) (hv : IsLoewnerSolution h v) {z : E} (hz : z ∈ unitBall E)
include hh hv hz

/-- **Cauchy estimate** for `eᵗ v(z, t)`. -/
theorem norm_exp_smul_sub_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖(Real.exp t : ℂ) • v t z - (Real.exp s : ℂ) • v s z‖ ≤
      8 * (‖z‖ / (1 - ‖z‖) ^ 2) ^ 2 / (1 - ‖z‖) ^ 2 * Real.exp (-s) := by
  set C := ‖z‖ / (1 - ‖z‖) ^ 2 with hC
  set K := 8 * C ^ 2 / (1 - ‖z‖) ^ 2 with hK
  have hz1 : ‖z‖ < 1 := LoewnerS0.mem_unitBall.mp hz
  have h1z : 0 < 1 - ‖z‖ := by linarith
  have hK0 : 0 ≤ K := by positivity
  set W : ℝ → E := fun τ => (Real.exp τ : ℂ) • v τ z with hW
  set e : E := W t - W s with he
  -- the auxiliary function `F(τ) = Re ⟨e, W(τ)⟩ + ‖e‖ K e^{-τ}` is nonincreasing
  have ht : 0 ≤ t := hs.trans hst
  have hlip := hv.lipschitzOnWith_Ici hh hz
  have hvac := hlip.absolutelyContinuousOnInterval_of_Ici hs hst
  have hcexp : AbsolutelyContinuousOnInterval (fun τ : ℝ => (Real.exp τ : ℂ)) s t :=
    ContDiffOn.absolutelyContinuousOnInterval
      (Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).contDiffOn
  have hWac : AbsolutelyContinuousOnInterval W s t := hcexp.fun_smul hvac
  have hFac : AbsolutelyContinuousOnInterval
      (fun τ => -((⟪e, W τ⟫_ℂ).re + ‖e‖ * K * Real.exp (-τ))) s t := by
    have h1 : AbsolutelyContinuousOnInterval (fun τ => (⟪e, W τ⟫_ℂ).re) s t :=
      LipschitzWith.comp_absolutelyContinuousOnInterval (lipschitzWith_re_inner e) hWac
    have h2 : AbsolutelyContinuousOnInterval (fun τ => ‖e‖ * K * Real.exp (-τ)) s t :=
      ContDiffOn.absolutelyContinuousOnInterval
        (contDiff_const.mul (Real.contDiff_exp.comp contDiff_neg)).contDiffOn
    exact (h1.fun_add h2).fun_neg
  have hmono := AbsolutelyContinuousOnInterval.le_of_ae_deriv_nonneg hst hFac
    (F' := fun τ => -((⟪e, (Real.exp τ : ℂ) • -h τ (v τ z) + (Real.exp τ : ℂ) • v τ z⟫_ℂ).re +
      ‖e‖ * K * (Real.exp (-τ) * -1))) (by
      filter_upwards [hv.ae_hasDerivAt hz ht] with τ hτ hτI
      have hτI' : τ ∈ Ioo 0 t := ⟨lt_of_le_of_lt hs hτI.1, hτI.2⟩
      have hτ0 : 0 ≤ τ := hτI'.1.le
      have hcd : HasDerivAt (fun τ : ℝ => (Real.exp τ : ℂ)) (Real.exp τ : ℂ) τ :=
        (Real.hasDerivAt_exp τ).ofReal_comp
      have hWd : HasDerivAt W ((Real.exp τ : ℂ) • -h τ (v τ z) + (Real.exp τ : ℂ) • v τ z) τ :=
        hcd.fun_smul (hτ hτI')
      have hed : HasDerivAt (fun τ => ‖e‖ * K * Real.exp (-τ)) (‖e‖ * K * (Real.exp (-τ) * -1))
          τ := ((hasDerivAt_neg τ).exp).const_mul (‖e‖ * K)
      refine ⟨((hasDerivAt_re_inner_const e hWd).add hed).fun_neg, ?_⟩
      -- the derivative is `≤ 0`
      have hvτ := hv.mem_unitBall hz hτ0
      have hr : ‖v τ z‖ ≤ ‖z‖ := hv.norm_le hh hz hτ0
      have hr1 : ‖v τ z‖ < 1 := LoewnerS0.mem_unitBall.mp hvτ
      have hdec := hv.norm_le_exp hh hz hτ0
      have hsub := (hh.isCaratheodory τ hτ0).norm_sub_le hvτ
      have hq : 8 * ‖v τ z‖ ^ 2 / (1 - ‖v τ z‖) ^ 2 ≤ K * Real.exp (-τ) ^ 2 := by
        have h1r : 0 < 1 - ‖v τ z‖ := by linarith
        have hden : (1 - ‖z‖) ^ 2 ≤ (1 - ‖v τ z‖) ^ 2 := by
          nlinarith [norm_nonneg (v τ z)]
        calc 8 * ‖v τ z‖ ^ 2 / (1 - ‖v τ z‖) ^ 2 ≤ 8 * ‖v τ z‖ ^ 2 / (1 - ‖z‖) ^ 2 :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hden
          _ ≤ 8 * (Real.exp (-τ) * C) ^ 2 / (1 - ‖z‖) ^ 2 := by
              gcongr
          _ = K * Real.exp (-τ) ^ 2 := by rw [hK]; ring
      have hin : (⟪e, (Real.exp τ : ℂ) • -h τ (v τ z) + (Real.exp τ : ℂ) • v τ z⟫_ℂ).re ≤
          ‖e‖ * (Real.exp τ * (K * Real.exp (-τ) ^ 2)) := by
        have heq : (Real.exp τ : ℂ) • -h τ (v τ z) + (Real.exp τ : ℂ) • v τ z =
            (Real.exp τ : ℂ) • -(h τ (v τ z) - v τ z) := by
          rw [← smul_add]; congr 1; abel
        rw [heq]
        refine (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos τ)]
        exact mul_le_mul_of_nonneg_left (hsub.trans hq) (Real.exp_pos τ).le
      have hexp : Real.exp τ * (K * Real.exp (-τ) ^ 2) = K * Real.exp (-τ) := by
        rw [sq, ← mul_assoc, mul_comm (Real.exp τ), mul_assoc K, ← mul_assoc (Real.exp τ),
          ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      rw [hexp] at hin
      nlinarith [norm_nonneg e, Real.exp_pos (-τ)])
  -- conclude
  have hee : (⟪e, W t⟫_ℂ).re - (⟪e, W s⟫_ℂ).re = ‖e‖ ^ 2 := by
    rw [← Complex.sub_re, ← inner_sub_right, ← he, inner_self_eq_norm_sq_to_K]
    norm_cast
  have h2 : ‖e‖ ^ 2 ≤ ‖e‖ * K * Real.exp (-s) := by
    have h3 : 0 ≤ ‖e‖ * K * Real.exp (-t) := by positivity
    linarith
  rcases eq_or_lt_of_le (norm_nonneg e) with h0 | hpos
  · rw [← h0]; positivity
  · have : ‖e‖ ≤ K * Real.exp (-s) := by nlinarith
    exact this

/-- **The limit `lim_{t → ∞} eᵗ v(z, t)` exists.** -/
theorem tendsto_exp_smul :
    ∃ L, Tendsto (fun t => (Real.exp t : ℂ) • v t z) atTop (𝓝 L) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff']
  intro ε hε
  set K := 8 * (‖z‖ / (1 - ‖z‖) ^ 2) ^ 2 / (1 - ‖z‖) ^ 2 with hK
  have hlim : Tendsto (fun N : ℝ => K * Real.exp (-N)) atTop (𝓝 (K * 0)) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.const_mul K
  rw [mul_zero] at hlim
  obtain ⟨N, hN, hN0⟩ := ((hlim.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 0)).exists
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hv.norm_exp_smul_sub_le hh hz hN0 hn) hN

end Limit

end IsLoewnerSolution

/-! ### Parametric representation and the growth theorem -/

variable [FiniteDimensional ℂ E]

/-- **Every solution of the Loewner ODE defines an element of `S⁰(𝔹)`**: the limit
`f(z) = lim_{t → ∞} eᵗ v(z, t)` exists for every `z ∈ 𝔹` [GHK02]. -/
theorem IsLoewnerSolution.exists_isParametricRep (hh : IsHerglotzVF h)
    (hv : IsLoewnerSolution h v) : ∃ f, IsParametricRep f h v :=
  ⟨fun z => limUnder atTop (fun t => (Real.exp t : ℂ) • v t z), hh, hv,
    fun _ hz => tendsto_nhds_limUnder (hv.tendsto_exp_smul hh hz)⟩

/-- **Growth theorem for `S⁰(𝔹)`** [GHK02]: `‖z‖/(1+‖z‖)² ≤ ‖f(z)‖ ≤ ‖z‖/(1-‖z‖)²`. -/
theorem classS0_norm_bounds {f : E → E} (hf : f ∈ classS0 E) {z : E} (hz : z ∈ unitBall E) :
    ‖z‖ / (1 + ‖z‖) ^ 2 ≤ ‖f z‖ ∧ ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2 := by
  obtain ⟨h, v, hrep⟩ := hf
  have hh := hrep.herglotz
  have hv := hrep.solution
  have hnorm : Tendsto (fun t => Real.exp t * ‖v t z‖) atTop (𝓝 ‖f z‖) := by
    refine (hrep.tendsto z hz).norm.congr' (Eventually.of_forall fun t => ?_)
    simp only
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
  have hr0 : Tendsto (fun t => ‖v t z‖) atTop (𝓝 0) := by
    have hlim : Tendsto (fun t : ℝ => Real.exp (-t) * (‖z‖ / (1 - ‖z‖) ^ 2)) atTop
        (𝓝 (0 * (‖z‖ / (1 - ‖z‖) ^ 2))) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.mul_const _
    rw [zero_mul] at hlim
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact hv.norm_le_exp hh hz ht
  constructor
  · have hlow : Tendsto (fun t => Real.exp t * (‖v t z‖ / (1 + ‖v t z‖) ^ 2)) atTop
        (𝓝 (‖f z‖ / (1 + 0) ^ 2)) := by
      have h1 : Tendsto (fun t => (1 + ‖v t z‖) ^ 2) atTop (𝓝 ((1 + 0) ^ 2)) :=
        (tendsto_const_nhds.add hr0).pow 2
      refine (hnorm.div h1 (by norm_num)).congr' (Eventually.of_forall fun t => ?_)
      rw [Pi.div_apply]
      ring
    rw [add_zero, one_pow, div_one] at hlow
    refine ge_of_tendsto hlow ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    have := hv.growth_lower hh hz le_rfl ht
    rwa [hv.apply_zero hz, Real.exp_zero, one_mul] at this
  · have hup : Tendsto (fun t => Real.exp t * (‖v t z‖ / (1 - ‖v t z‖) ^ 2)) atTop
        (𝓝 (‖f z‖ / (1 - 0) ^ 2)) := by
      have h1 : Tendsto (fun t => (1 - ‖v t z‖) ^ 2) atTop (𝓝 ((1 - 0) ^ 2)) :=
        (tendsto_const_nhds.sub hr0).pow 2
      refine (hnorm.div h1 (by norm_num)).congr' (Eventually.of_forall fun t => ?_)
      rw [Pi.div_apply]
      ring
    rw [sub_zero, one_pow, div_one] at hup
    refine le_of_tendsto hup ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    have := hv.growth_upper hh hz le_rfl ht
    rwa [hv.apply_zero hz, Real.exp_zero, one_mul] at this

end LoewnerS0
