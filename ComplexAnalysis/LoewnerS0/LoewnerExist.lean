import LoewnerS0.LoewnerODE
import LoewnerS0.Picard

/-!
# Existence of solutions of the Loewner ODE

Let `h` be a Herglotz vector field on the unit ball `𝔹` of a finite-dimensional complex inner
product space. For `z ∈ 𝔹` we choose `ρ = (1 + ‖z‖)/2` and replace `h(·, s)` by the globally
Lipschitz and bounded field `G(s, x) = h(π_ρ(x), s)` (`s ≥ 0`), where `π_ρ` is the radial
retraction onto `closedBall 0 ρ` (the Lipschitz constant and the bound depend only on `ρ`, by the
estimates for `M(𝔹)` in `LoewnerS0.ClassM`). The Carathéodory version of the Picard iteration
(`LoewnerS0.Picard`) gives a solution `w` of `w(t) = z - ∫₀ᵗ G(s, w(s)) ds`. Since
`Re ⟨G(s, x), x⟩ ≥ 0`, the norm of `w` does not increase, so `w` stays in `closedBall 0 ‖z‖`,
where `G(s, ·) = h(·, s)`: `w` solves the Loewner ODE.
-/

open Complex Metric Set Filter MeasureTheory
open scoped InnerProductSpace Topology NNReal Interval

noncomputable section

namespace LoewnerS0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {h : ℝ → E → E}

/-! ### Integral equations -/

section IntegralEquation

variable {g w : ℝ → E} {z : E}

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
lemma lipschitzOnWith_of_eq_integral [NormedSpace ℝ E] {M : ℝ} (hM0 : 0 ≤ M)
    (hint : ∀ t, 0 ≤ t → IntervalIntegrable g volume 0 t)
    (heq : ∀ t, 0 ≤ t → w t = z - ∫ s in (0)..t, g s) (hbd : ∀ s, ‖g s‖ ≤ M) :
    LipschitzOnWith M.toNNReal w (Ici 0) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [dist_eq_norm, heq s hs, heq t ht, sub_sub_sub_cancel_left,
    intervalIntegral.integral_interval_sub_left (hint t ht) (hint s hs), Real.coe_toNNReal _ hM0]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := M) fun x _ => hbd x).trans ?_
  rw [Real.dist_eq, abs_sub_comm]

omit [InnerProductSpace ℂ E] in
lemma ae_hasDerivAt_of_eq_integral [NormedSpace ℝ E] {T : ℝ} (hT : 0 ≤ T)
    (hint : IntervalIntegrable g volume 0 T)
    (heq : ∀ t, 0 ≤ t → w t = z - ∫ s in (0)..t, g s) :
    ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt w (-g t) t := by
  filter_upwards [hint.ae_hasDerivAt_integral] with t ht htI
  have htI' : t ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact Ioo_subset_Icc_self htI
  have hD := (ht htI' 0 left_mem_uIcc).const_sub z
  apply hD.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds htI.1] with τ hτ
  exact heq τ (le_of_lt hτ)

end IntegralEquation

/-! ### The retracted field -/

/-- The Loewner field, retracted onto `closedBall 0 ρ` in space and extended by `0` to negative
times. -/
def retractedField (h : ℝ → E → E) (ρ : ℝ) (s : ℝ) (x : E) : E :=
  (Ici (0 : ℝ)).indicator (fun s => h s (radialRetraction ρ x)) s

variable [FiniteDimensional ℂ E]

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
lemma retractedField_of_nonneg {ρ s : ℝ} (hs : 0 ≤ s) (x : E) :
    retractedField h ρ s x = h s (radialRetraction ρ x) := by
  simp [retractedField, hs]

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
lemma retractedField_of_neg {ρ s : ℝ} (hs : s < 0) (x : E) : retractedField h ρ s x = 0 := by
  simp [retractedField, not_le.mpr hs]

omit [CompleteSpace E] in
lemma lipschitzWith_retractedField (hh : IsHerglotzVF h) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (s : ℝ) : LipschitzWith ((32 / (1 - ρ) ^ 3).toNNReal * 2) (retractedField h ρ s) := by
  rcases le_or_gt 0 s with hs | hs
  · have hfun : retractedField h ρ s = h s ∘ radialRetraction ρ := by
      funext x; exact retractedField_of_nonneg hs x
    rw [hfun]
    have h1 := (hh.isCaratheodory s hs).lipschitzOnWith hρ1
    have h2 := (lipschitzWith_radialRetraction (E := E) hρ).lipschitzOnWith (s := univ)
    have := h1.comp h2 (fun x _ => mem_closedBall_zero_iff.mpr (norm_radialRetraction_le hρ x))
    exact lipschitzOnWith_univ.mp this
  · have hfun : retractedField h ρ s = fun _ => 0 := by
      funext x; exact retractedField_of_neg hs x
    rw [hfun]
    exact (LipschitzWith.const 0).weaken bot_le

omit [CompleteSpace E] in
lemma norm_retractedField_le (hh : IsHerglotzVF h) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (s : ℝ)
    (x : E) : ‖retractedField h ρ s x‖ ≤ 4 * ρ / (1 - ρ) ^ 2 := by
  rcases le_or_gt 0 s with hs | hs
  · rw [retractedField_of_nonneg hs]
    exact (hh.isCaratheodory s hs).norm_le_of_norm_le hρ1 (norm_radialRetraction_le hρ x)
  · rw [retractedField_of_neg hs, norm_zero]
    have : 0 < 1 - ρ := by linarith
    positivity

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
lemma aestronglyMeasurable_retractedField (hh : IsHerglotzVF h) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (x : E) :
    AEStronglyMeasurable (fun s => retractedField h ρ s x) volume := by
  have hmem : radialRetraction ρ x ∈ unitBall E :=
    mem_unitBall.mpr (lt_of_le_of_lt (norm_radialRetraction_le hρ x) hρ1)
  exact (aestronglyMeasurable_indicator_iff measurableSet_Ici).mpr
    (hh.aestronglyMeasurable _ hmem)

/-! ### Existence -/

omit [FiniteDimensional ℂ E] in
variable (h) in
/-- `γ` solves the Loewner ODE `γ' = -h(γ, t)` (in integral form) with initial value `z`. -/
def IsLoewnerCurve (z : E) (γ : ℝ → E) : Prop :=
  ∀ t, 0 ≤ t → γ t ∈ unitBall E ∧ IntervalIntegrable (fun s => h s (γ s)) volume 0 t ∧
    γ t = z - ∫ s in (0)..t, h s (γ s)

/-- The solution of the retracted equation (`ρ ≥ ‖z‖`) solves the Loewner ODE. -/
theorem isLoewnerCurve_sol (hh : IsHerglotzVF h) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) {z : E}
    (hzρ : ‖z‖ ≤ ρ) : IsLoewnerCurve h z (Picard.sol (retractedField h ρ) z) := by
  have hz1 : ‖z‖ < 1 := hzρ.trans_lt hρ1
  set G := retractedField h ρ with hGdef
  have hlip := lipschitzWith_retractedField hh hρ hρ1
  have hbd := norm_retractedField_le hh hρ hρ1
  have hmeas := aestronglyMeasurable_retractedField hh hρ hρ1
  set M := 4 * ρ / (1 - ρ) ^ 2 with hM
  have hM0 : 0 ≤ M := by
    have : 0 < 1 - ρ := by linarith
    positivity
  set w := Picard.sol G z with hw
  have hspec : ∀ t, 0 ≤ t → IntervalIntegrable (fun s => G s (w s)) volume 0 t ∧
      w t = z - ∫ s in (0)..t, G s (w s) := fun t ht => Picard.sol_spec hlip hbd hmeas z ht
  have hw0 : w 0 = z := by rw [(hspec 0 le_rfl).2]; simp
  have hlipw : LipschitzOnWith M.toNNReal w (Ici 0) :=
    lipschitzOnWith_of_eq_integral hM0 (fun t ht => (hspec t ht).1) (fun t ht => (hspec t ht).2)
      (fun s => hbd s (w s))
  -- the norm of `w` does not increase
  have hnorm : ∀ t, 0 ≤ t → ‖w t‖ ≤ ‖z‖ := by
    intro t ht
    set R := ‖z‖ + M * t with hR
    have hR0 : 0 ≤ R := by positivity
    have hlipt := hlipw.mono (show uIcc 0 t ⊆ Ici 0 by
      rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)
    have hbdw : ∀ τ ∈ uIcc 0 t, ‖w τ‖ ≤ R := by
      intro τ hτ
      rw [uIcc_of_le ht] at hτ
      have := hlipw.dist_le_mul τ hτ.1 0 (Set.mem_Ici.mpr le_rfl)
      rw [dist_eq_norm, hw0, Real.dist_eq, sub_zero, abs_of_nonneg hτ.1,
        Real.coe_toNNReal _ hM0] at this
      calc ‖w τ‖ = ‖(w τ - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖w τ - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ M * τ + ‖z‖ := by linarith
        _ ≤ R := by rw [hR]; nlinarith [hτ.2]
    have hac : AbsolutelyContinuousOnInterval (fun τ => -‖w τ‖ ^ 2) 0 t :=
      (absolutelyContinuousOnInterval_norm_sq hR0 hlipt hbdw).fun_neg
    have hmono := AbsolutelyContinuousOnInterval.le_of_ae_deriv_nonneg ht hac
      (F' := fun τ => 2 * (⟪w τ, G τ (w τ)⟫_ℂ).re) (by
        filter_upwards [ae_hasDerivAt_of_eq_integral ht (hspec t ht).1
          (fun τ hτ => (hspec τ hτ).2)] with τ hτ hτI
        refine ⟨?_, ?_⟩
        · convert (hasDerivAt_norm_sq (hτ hτI)).neg using 1
          rw [inner_neg_right, Complex.neg_re]
          ring
        · have hτ0 : 0 ≤ τ := hτI.1.le
          rw [hGdef, retractedField_of_nonneg hτ0]
          have := (hh.isCaratheodory τ hτ0).re_inner_radialRetraction_nonneg hρ hρ1 (w τ)
          linarith)
    have : ‖w t‖ ^ 2 ≤ ‖w 0‖ ^ 2 := by linarith
    rw [hw0] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  -- on `closedBall 0 ‖z‖` the retracted field is `h`
  have hG : ∀ s, 0 ≤ s → G s (w s) = h s (w s) := fun s hs => by
    rw [hGdef, retractedField_of_nonneg hs,
      radialRetraction_of_norm_le hρ ((hnorm s hs).trans hzρ)]
  refine fun t ht => ⟨mem_unitBall.mpr ((hnorm t ht).trans_lt hz1), ?_, ?_⟩
  · refine (hspec t ht).1.congr fun s hs => ?_
    rw [uIoc_of_le ht] at hs
    exact hG s hs.1.le
  · rw [(hspec t ht).2]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    exact hG s hs.1

/-- A solution of the Loewner ODE starting at a given point `z ∈ 𝔹`. -/
theorem exists_isLoewnerCurve (hh : IsHerglotzVF h) {z : E} (hz : z ∈ unitBall E) :
    ∃ w : ℝ → E, IsLoewnerCurve h z w := by
  have hz1 : ‖z‖ < 1 := mem_unitBall.mp hz
  exact ⟨_, isLoewnerCurve_sol hh (ρ := (1 + ‖z‖) / 2) (by positivity) (by linarith)
    (by linarith)⟩

/-- **Existence of solutions of the Loewner ODE** [GHK02]. -/
theorem IsHerglotzVF.exists_isLoewnerSolution (hh : IsHerglotzVF h) :
    ∃ v, IsLoewnerSolution h v := by
  have key : ∀ z ∈ unitBall E, ∃ w : ℝ → E, IsLoewnerCurve h z w :=
    fun z hz => exists_isLoewnerCurve hh hz
  choose! W hW using key
  exact ⟨fun t z => W z t, fun z hz t ht => hW z hz t ht⟩

/-- **Uniqueness for single solution curves.** -/
theorem IsLoewnerCurve.eq (hh : IsHerglotzVF h) {z : E} (hz : z ∈ unitBall E) {γ₁ γ₂ : ℝ → E}
    (h₁ : IsLoewnerCurve h z γ₁) (h₂ : IsLoewnerCurve h z γ₂) {t : ℝ} (ht : 0 ≤ t) :
    γ₁ t = γ₂ t := by
  classical
  obtain ⟨v₀, hv₀⟩ := hh.exists_isLoewnerSolution
  have hsol : ∀ γ : ℝ → E, IsLoewnerCurve h z γ →
      IsLoewnerSolution h (fun t y => if y = z then γ t else v₀ t y) := by
    intro γ hγ y hy t ht
    by_cases hyz : y = z
    · subst hyz
      simpa using hγ t ht
    · simpa [hyz] using hv₀ y hy t ht
  have := (hsol γ₁ h₁).eqOn_of_isHerglotzVF hh (hsol γ₂ h₂) ht hz
  simpa using this

/-- Every Herglotz vector field generates an element of `S⁰(𝔹)`. -/
theorem exists_mem_classS0 (hh : IsHerglotzVF h) :
    ∃ f ∈ classS0 E, ∃ v, IsParametricRep f h v := by
  obtain ⟨v, hv⟩ := hh.exists_isLoewnerSolution
  obtain ⟨f, hf⟩ := hv.exists_isParametricRep hh
  exact ⟨f, ⟨h, v, hf⟩, v, hf⟩

end LoewnerS0
