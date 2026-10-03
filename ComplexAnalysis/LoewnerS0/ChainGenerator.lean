import LoewnerS0.ChainEstimates
import LoewnerS0.StarlikeGen
import Mathlib.Analysis.Calculus.Rademacher

/-!
# The Herglotz vector field of a normal Loewner chain (assuming Osgood's theorem)

Let `F` be a Loewner chain on `𝔹` with `{e⁻ᵗ F_t}` locally bounded, and assume Osgood's theorem.
Since `t ↦ F_t(z)` is locally Lipschitz (`LoewnerS0.IsLoewnerChain.exists_norm_sub_le`), it is
differentiable almost everywhere (Rademacher). Fix a countable dense set (`denseSeq E`); for almost
every `t > 0` (a *good time*, `LoewnerS0.IsGoodTime`) all the maps `t ↦ F_t(d)`, `d` in the dense
set, are differentiable at `t`. At a good time:

* the difference quotients `(F_{t+ε} - F_t)/ε` are holomorphic and locally uniformly bounded, so
  they are locally equi-Lipschitz; as they converge on a dense set, they converge everywhere on `𝔹`
  as `ε → 0+`, to the *right time derivative* `∂_t F(·, t)` (`LoewnerS0.chainDeriv`), which is
  holomorphic (Vitali, `LoewnerS0.SCV.differentiableOn_of_tendsto_of_bounded`);
* the *generator* `h(·, t) = DF_t⁻¹ ∂_t F(·, t)` (`LoewnerS0.chainGen`) is the limit of
  `(z - v(z, t, t+ε))/ε` (`LoewnerS0.IsLoewnerChain.tendsto_transition`), where `v` are the
  transition maps; as these quotients are (essentially) in `M(𝔹)`, `h(·, t) ∈ M(𝔹)`
  (`LoewnerS0.IsLoewnerChain.isCaratheodory_chainGen`).

The Herglotz vector field `LoewnerS0.chainField F` is `h(·, t)` when this is in `M(𝔹)` (which is the
case for almost every `t`) and the identity otherwise; it is measurable in `t`
(`LoewnerS0.IsLoewnerChain.isHerglotzVF_chainField`).
-/

open Function Complex Metric Set Filter MeasureTheory TopologicalSpace
open scoped Topology InnerProductSpace NNReal

noncomputable section

namespace LoewnerS0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {F : ℝ → E → E}

/-- The right time derivative `∂_t F(w, t) = lim_{ε → 0+} (F_{t+ε}(w) - F_t(w))/ε` of a chain. -/
def chainDeriv (F : ℝ → E → E) (t : ℝ) (w : E) : E :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε : ℝ => ε⁻¹ • (F (t + ε) w - F t w)

/-- The generator `h(w, t) = DF_t(w)⁻¹ ∂_t F(w, t)` of a chain. -/
def chainGen (F : ℝ → E → E) (t : ℝ) (w : E) : E :=
  Ring.inverse (fderiv ℂ (F t) w) (chainDeriv F t w)

/-- A *good time* of the chain `F`: `t > 0`, and `τ ↦ F_τ(d)` is differentiable at `t` for every
`d ∈ 𝔹` of the fixed countable dense set `denseSeq E`. -/
def IsGoodTime (F : ℝ → E → E) (t : ℝ) : Prop :=
  0 < t ∧ ∀ n, denseSeq E n ∈ unitBall E → DifferentiableAt ℝ (fun τ => F τ (denseSeq E n)) t

open Classical in
/-- The Herglotz vector field of the chain: the generator `h(·, t)` when it is in `M(𝔹)` (for
almost every `t`), the identity otherwise. -/
def chainField (F : ℝ → E → E) (t : ℝ) : E → E :=
  if IsCaratheodory (chainGen F t) then chainGen F t else id

omit [FiniteDimensional ℂ E] in
lemma isCaratheodory_chainField (t : ℝ) : IsCaratheodory (chainField F t) := by
  unfold chainField
  split_ifs with h
  · exact h
  · exact isCaratheodory_id

/-- The slopes of `ε ↦ e^{-ε}` at `0`: `(1 - e^{-ε})/ε → 1`. -/
lemma tendsto_one_sub_exp_neg_div :
    Tendsto (fun ε : ℝ => ε⁻¹ * (1 - Real.exp (-ε))) (𝓝[>] 0) (𝓝 1) := by
  have h := ((hasDerivAt_neg (0 : ℝ)).exp).tendsto_slope_zero_right
  simp only [neg_zero, Real.exp_zero, one_mul, zero_add, smul_eq_mul] at h
  have h2 := h.neg
  rw [neg_neg] at h2
  refine h2.congr fun ε => ?_
  ring

omit [FiniteDimensional ℂ E] in
/-- The difference quotients `(F_{t+ε} - F_t)/ε`, `0 < ε ≤ 1`, are bounded on `closedBall 0 r`. -/
lemma norm_diffQuot_le {r K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ s t, 0 ≤ s → s ≤ t → ∀ w : E, ‖w‖ ≤ r → ‖F t w - F s w‖ ≤ Real.exp t * K * (t - s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε0 : 0 < ε) (hε1 : ε ≤ 1) {y : E} (hy : ‖y‖ ≤ r) :
    ‖ε⁻¹ • (F (t + ε) y - F t y)‖ ≤ Real.exp (t + 1) * K := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε0]
  have h1 := hK t (t + ε) ht (by linarith) y hy
  calc ε⁻¹ * ‖F (t + ε) y - F t y‖ ≤ ε⁻¹ * (Real.exp (t + ε) * K * (t + ε - t)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hε0.le)
    _ = Real.exp (t + ε) * K := by field_simp; ring
    _ ≤ Real.exp (t + 1) * K := by gcongr

namespace IsLoewnerChain

variable (hF : IsLoewnerChain F) (hO : OsgoodTheorem E)

section Inverse

include hF hO

/-- Under Osgood's theorem, `DF_t(w)` is invertible. -/
lemma isUnit_fderiv {t : ℝ} (ht : 0 ≤ t) {w : E} (hw : w ∈ unitBall E) :
    IsUnit (fderiv ℂ (F t) w) := by
  obtain ⟨e, he⟩ := hO.exists_equiv isOpen_unitBall (hF.differentiableOn t ht) (hF.injOn t ht) hw
  exact ⟨e.toUnit, he⟩

lemma inverse_apply_fderiv {t : ℝ} (ht : 0 ≤ t) {w : E} (hw : w ∈ unitBall E) (v : E) :
    Ring.inverse (fderiv ℂ (F t) w) (fderiv ℂ (F t) w v) = v := by
  have h := Ring.inverse_mul_cancel _ (hF.isUnit_fderiv hO ht hw)
  calc Ring.inverse (fderiv ℂ (F t) w) (fderiv ℂ (F t) w v)
      = (Ring.inverse (fderiv ℂ (F t) w) * fderiv ℂ (F t) w) v := rfl
    _ = v := by rw [h]; rfl

end Inverse

variable (hloc : IsLocallyBounded fun t z => (Real.exp (-t) : ℂ) • F t z)
include hF hO hloc

/-- **Almost every time is good** (Rademacher's theorem on the dense set). -/
theorem ae_isGoodTime : ∀ᵐ t, 0 < t → IsGoodTime F t := by
  have hd : ∀ n, ∀ᵐ t : ℝ, 0 < t → denseSeq E n ∈ unitBall E →
      DifferentiableAt ℝ (fun τ => F τ (denseSeq E n)) t := by
    intro n
    by_cases hn : denseSeq E n ∈ unitBall E
    · obtain ⟨K, -, hK⟩ := hF.exists_lipschitzOnWith hloc hO (mem_unitBall.mp hn)
      have hm : ∀ m : ℕ, ∀ᵐ t : ℝ, t ∈ Icc (0 : ℝ) m →
          DifferentiableWithinAt ℝ (fun τ => F τ (denseSeq E n)) (Icc 0 m) t :=
        fun m => (hK m _ le_rfl).ae_differentiableWithinAt_of_mem
      filter_upwards [ae_all_iff.mpr hm] with t ht ht0 _
      obtain ⟨m, hmt⟩ := exists_nat_gt t
      exact (ht m ⟨ht0.le, hmt.le⟩).differentiableAt (Icc_mem_nhds ht0 hmt)
    · exact Eventually.of_forall fun t _ h => absurd h hn
  filter_upwards [ae_all_iff.mpr hd] with t ht ht0
  exact ⟨ht0, fun n hn => ht n ht0 hn⟩

/-- At a good time, the right time derivative exists at every point of `𝔹`. -/
theorem tendsto_chainDeriv {t : ℝ} (hgood : IsGoodTime F t) {w : E} (hw : w ∈ unitBall E) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (F (t + ε) w - F t w)) (𝓝[>] 0) (𝓝 (chainDeriv F t w)) := by
  have ht : 0 ≤ t := hgood.1.le
  have hw1 : ‖w‖ < 1 := mem_unitBall.mp hw
  set ρ := (1 + ‖w‖) / 2 with hρ
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hwρ : ‖w‖ < ρ := by rw [hρ]; linarith
  set ρ' := (1 + ρ) / 2 with hρ'
  have hρρ' : ρ < ρ' := by rw [hρ']; linarith
  have hρ'1 : ρ' < 1 := by rw [hρ']; linarith
  obtain ⟨K, hK0, hK⟩ := hF.exists_norm_sub_le hloc hO hρ'1
  have hlip : ∀ᶠ ε in 𝓝[>] (0 : ℝ), LipschitzOnWith (Real.exp (t + 1) * K / (ρ' - ρ)).toNNReal
      (fun x => ε⁻¹ • (F (t + ε) x - F t x)) (ball 0 ρ) := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    have hd : DifferentiableOn ℂ (fun x => ε⁻¹ • (F (t + ε) x - F t x)) (unitBall E) :=
      ((hF.differentiableOn (t + ε) (by linarith [hε.1])).sub
        (hF.differentiableOn t ht)).const_smul ε⁻¹
    exact (SCV.lipschitzOnWith_of_bound hρρ' isOpen_unitBall hd (closedBall_subset_ball hρ'1)
      fun y hy => norm_diffQuot_le hK0 hK ht hε.1 hε.2.le (mem_closedBall_zero_iff.mp hy)).mono
      ball_subset_closedBall
  have hconv : ∀ d ∈ range (denseSeq E) ∩ ball (0 : E) ρ, ∃ y,
      Tendsto (fun ε : ℝ => ε⁻¹ • (F (t + ε) d - F t d)) (𝓝[>] 0) (𝓝 y) := by
    rintro _ ⟨⟨n, rfl⟩, hn⟩
    have hnB : denseSeq E n ∈ unitBall E :=
      mem_unitBall.mpr ((mem_ball_zero_iff.mp hn).trans hρ1)
    exact ⟨_, (hgood.2 n hnB).hasDerivAt.tendsto_slope_zero_right⟩
  have hD : ball (0 : E) ρ ⊆ closure (range (denseSeq E) ∩ ball 0 ρ) := by
    have := Dense.open_subset_closure_inter (denseRange_denseSeq E) (isOpen_ball (x := (0 : E))
      (ε := ρ))
    rwa [inter_comm] at this
  obtain ⟨y, hy⟩ := SCV.exists_tendsto_of_dense hlip hD hconv (mem_ball_zero_iff.mpr hwρ)
  exact tendsto_nhds_limUnder ⟨y, hy⟩

/-- At a good time, `∂_t F(·, t)` is holomorphic (Vitali). -/
theorem differentiableOn_chainDeriv {t : ℝ} (hgood : IsGoodTime F t) :
    DifferentiableOn ℂ (chainDeriv F t) (unitBall E) := by
  have ht : 0 ≤ t := hgood.1.le
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hε0 : ∀ n, 0 < ε n := fun n => by positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    rw [hε, div_le_one (by positivity)]
    linarith [n.cast_nonneg (α := ℝ)]
  have hεlim : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall hε0⟩
  refine SCV.differentiableOn_of_tendsto_of_bounded
    (Q := fun n x => (ε n)⁻¹ • (F (t + ε n) x - F t x)) (fun n => ?_) (fun r hr => ?_)
    (fun w hw => ?_)
  · exact ((hF.differentiableOn _ (by linarith [hε0 n])).sub (hF.differentiableOn t ht)).const_smul _
  · obtain ⟨K, hK0, hK⟩ := hF.exists_norm_sub_le hloc hO hr
    exact ⟨Real.exp (t + 1) * K, fun n y hy =>
      norm_diffQuot_le hK0 hK ht (hε0 n) (hε1 n) (mem_closedBall_zero_iff.mp hy)⟩
  · exact (tendsto_chainDeriv hF hO hloc hgood hw).comp hεlim

/-- At a good time, `(w - v(w, t, t+ε))/ε → h(w, t)` as `ε → 0+`. -/
theorem tendsto_transition {t : ℝ} (hgood : IsGoodTime F t) {w : E} (hw : w ∈ unitBall E) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (w - transition F t (t + ε) w)) (𝓝[>] 0)
      (𝓝 (chainGen F t w)) := by
  have ht : 0 ≤ t := hgood.1.le
  have hw1 : ‖w‖ < 1 := mem_unitBall.mp hw
  set A := fderiv ℂ (F t) w with hA
  obtain ⟨K₃, hK₃0, hK₃⟩ := hF.exists_norm_fderiv_sub_le hloc hO hw1
  obtain ⟨K₄, hK₄0, hK₄⟩ := hF.exists_norm_sub_sub_fderiv_le hloc hw1
  set c := 4 * ‖w‖ / (1 - ‖w‖) ^ 2 with hc
  have hc0 : 0 ≤ c := by
    have : 0 < 1 - ‖w‖ := by linarith
    positivity
  have hd : ∀ ε, 0 < ε → ‖w - transition F t (t + ε) w‖ ≤ ε * c := by
    intro ε hε
    have h1 := hF.norm_sub_transition_le hO ht (by linarith : t ≤ t + ε) hw1 le_rfl
    have h2 := one_sub_exp_sub_le (s := t) (t := t + ε)
    calc ‖w - transition F t (t + ε) w‖ ≤ (1 - Real.exp (t - (t + ε))) * c := h1
      _ ≤ (t + ε - t) * c := mul_le_mul_of_nonneg_right h2 hc0
      _ = ε * c := by ring
  set M := Real.exp (t + 1) * (K₃ * c + K₄ * c ^ 2) with hM
  have hkey : ∀ ε, 0 < ε → ε ≤ 1 →
      ‖A (ε⁻¹ • (w - transition F t (t + ε) w)) - ε⁻¹ • (F (t + ε) w - F t w)‖ ≤ ε * M := by
    intro ε hε0 hε1
    have htε : t ≤ t + ε := by linarith
    set v := transition F t (t + ε) w with hv
    have hvw : ‖v‖ ≤ ‖w‖ := hF.norm_transition_le hO ht htε hw
    have hFv : F (t + ε) v = F t w := hF.apply_transition ht htε hw
    set B := fderiv ℂ (F (t + ε)) w with hB
    have heq : A (ε⁻¹ • (w - v)) - ε⁻¹ • (F (t + ε) w - F t w) =
        ε⁻¹ • ((A - B) (w - v) + (F (t + ε) v - F (t + ε) w - B (v - w))) := by
      rw [← hFv, A.map_smul_of_tower, ← smul_sub]
      congr 1
      have : v - w = -(w - v) := by abel
      rw [this, map_neg, sub_apply]
      abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε0]
    have hdv : ‖w - v‖ ≤ ε * c := hd ε hε0
    have hb1 : ‖(A - B) (w - v)‖ ≤ Real.exp (t + ε) * K₃ * ε * (ε * c) := by
      refine ((A - B).le_opNorm _).trans ?_
      have h3 := hK₃ t (t + ε) ht htε w le_rfl
      rw [norm_sub_rev] at h3
      have h3' : ‖A - B‖ ≤ Real.exp (t + ε) * K₃ * ε := by
        have : t + ε - t = ε := by ring
        rwa [this] at h3
      exact mul_le_mul h3' hdv (norm_nonneg _) (by positivity)
    have hb2 : ‖F (t + ε) v - F (t + ε) w - B (v - w)‖ ≤ Real.exp (t + ε) * K₄ * (ε * c) ^ 2 := by
      have h4 := hK₄ (t + ε) (by linarith) v w hvw le_rfl
      refine h4.trans ?_
      have : ‖v - w‖ = ‖w - v‖ := norm_sub_rev _ _
      rw [this]
      gcongr
    have hexp : Real.exp (t + ε) ≤ Real.exp (t + 1) := Real.exp_le_exp.mpr (by linarith)
    calc ε⁻¹ * ‖(A - B) (w - v) + (F (t + ε) v - F (t + ε) w - B (v - w))‖
        ≤ ε⁻¹ * (Real.exp (t + ε) * K₃ * ε * (ε * c) + Real.exp (t + ε) * K₄ * (ε * c) ^ 2) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hb1 hb2))
            (inv_nonneg.mpr hε0.le)
      _ = ε * (Real.exp (t + ε) * (K₃ * c + K₄ * c ^ 2)) := by field_simp
      _ ≤ ε * M := by
          rw [hM]
          gcongr
  have hlim1 : Tendsto (fun ε : ℝ => A (ε⁻¹ • (w - transition F t (t + ε) w))) (𝓝[>] 0)
      (𝓝 (chainDeriv F t w)) := by
    have h0 : Tendsto (fun ε : ℝ => A (ε⁻¹ • (w - transition F t (t + ε) w)) -
        ε⁻¹ • (F (t + ε) w - F t w)) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (a := fun ε => ε * M) ?_
      · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε using hkey ε hε.1 hε.2.le
      · have : Tendsto (fun ε : ℝ => ε * M) (𝓝 0) (𝓝 (0 * M)) := tendsto_id.mul_const M
        rw [zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
    have := (tendsto_chainDeriv hF hO hloc hgood hw).add h0
    rw [add_zero] at this
    exact this.congr fun ε => by abel
  have hinv := ((Ring.inverse A).continuous.tendsto _).comp hlim1
  refine hinv.congr fun ε => ?_
  exact hF.inverse_apply_fderiv hO ht hw _

/-- At a good time, the generator `h(·, t)` belongs to `M(𝔹)`. -/
theorem isCaratheodory_chainGen {t : ℝ} (hgood : IsGoodTime F t) :
    IsCaratheodory (chainGen F t) := by
  have ht : 0 ≤ t := hgood.1.le
  -- holomorphy
  have hdiff : DifferentiableOn ℂ (chainGen F t) (unitBall E) := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun x => Ring.inverse (fderiv ℂ (F t) x)) w :=
      (differentiableAt_inverse (hF.isUnit_fderiv hO ht hw)).comp w
        ((hF.differentiableOn_fderiv ht).differentiableAt (isOpen_unitBall.mem_nhds hw))
    have h2 : DifferentiableAt ℂ (chainDeriv F t) w :=
      (differentiableOn_chainDeriv hF hO hloc hgood).differentiableAt (isOpen_unitBall.mem_nhds hw)
    exact (h1.clm_apply h2).differentiableWithinAt
  -- the value at `0`
  have h0 : chainGen F t 0 = 0 := by
    have hlim := tendsto_chainDeriv hF hO hloc hgood zero_mem_unitBall
    have hzero : (fun ε : ℝ => ε⁻¹ • (F (t + ε) 0 - F t 0)) =ᶠ[𝓝[>] 0] fun _ => 0 := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      rw [hF.map_zero _ (by linarith), hF.map_zero t ht, sub_self, smul_zero]
    have : chainDeriv F t 0 = 0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hzero.symm)
    simp [chainGen, this]
  -- `‖h(w, t) - w‖ ≤ 8‖w‖²/(1-‖w‖)²`
  have hquad : ∀ w ∈ unitBall E, ‖chainGen F t w - w‖ ≤ 8 * ‖w‖ ^ 2 / (1 - ‖w‖) ^ 2 := by
    intro w hw
    have hlim := tendsto_transition hF hO hloc hgood hw
    have hc := tendsto_one_sub_exp_neg_div
    have h1 : Tendsto (fun ε : ℝ => ε⁻¹ • (w - transition F t (t + ε) w) -
        (ε⁻¹ * (1 - Real.exp (-ε))) • w) (𝓝[>] 0) (𝓝 (chainGen F t w - (1 : ℝ) • w)) :=
      hlim.sub (hc.smul_const w)
    rw [one_smul] at h1
    refine le_of_tendsto h1.norm (eventually_nhdsWithin_of_forall fun ε hε => ?_)
    have hε0 : (0 : ℝ) < ε := hε
    have hb := hF.norm_sub_transition_sub_le hO ht (by linarith : t ≤ t + ε) hw
    rw [show t - (t + ε) = -ε by ring] at hb
    have heq : ε⁻¹ • (w - transition F t (t + ε) w) - (ε⁻¹ * (1 - Real.exp (-ε))) • w =
        ε⁻¹ • ((w - transition F t (t + ε) w) - ((1 - Real.exp (-ε) : ℝ) : ℂ) • w) := by
      rw [smul_sub ε⁻¹ (w - transition F t (t + ε) w), Complex.coe_smul, smul_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε0]
    have hle : 1 - Real.exp (-ε) ≤ ε := by have := Real.add_one_le_exp (-ε); linarith
    have hB : 0 ≤ 8 * ‖w‖ ^ 2 / (1 - ‖w‖) ^ 2 := by positivity
    calc ε⁻¹ * ‖(w - transition F t (t + ε) w) - ((1 - Real.exp (-ε) : ℝ) : ℂ) • w‖
        ≤ ε⁻¹ * ((1 - Real.exp (-ε)) * (8 * ‖w‖ ^ 2 / (1 - ‖w‖) ^ 2)) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hε0.le)
      _ ≤ ε⁻¹ * (ε * (8 * ‖w‖ ^ 2 / (1 - ‖w‖) ^ 2)) := by gcongr
      _ = 8 * ‖w‖ ^ 2 / (1 - ‖w‖) ^ 2 := by field_simp
  have hN : IsNormalized (chainGen F t) :=
    { differentiableOn := hdiff
      map_zero := h0
      fderiv_zero := by
        refine (hasFDerivAt_zero_of_norm_sub_le_sq (δ := 1 / 2) (C := 32) (by norm_num) h0
          fun z hz => ?_).fderiv
        have hzB : z ∈ unitBall E := mem_unitBall.mpr (by linarith)
        have h1 : 1 / 4 ≤ (1 - ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
        calc ‖chainGen F t z - ContinuousLinearMap.id ℂ E z‖ = ‖chainGen F t z - z‖ := rfl
          _ ≤ 8 * ‖z‖ ^ 2 / (1 - ‖z‖) ^ 2 := hquad z hzB
          _ ≤ 32 * ‖z‖ ^ 2 := by
              rw [div_le_iff₀ (by positivity)]
              nlinarith [sq_nonneg ‖z‖] }
  -- `Re ⟨h(w, t), w⟩ ≥ 0`
  refine hN.isCaratheodory_of_re_inner_nonneg fun w hw => ?_
  have hlim := tendsto_transition hF hO hloc hgood hw
  have h1 : Tendsto (fun ε : ℝ => (⟪w, ε⁻¹ • (w - transition F t (t + ε) w)⟫_ℂ).re) (𝓝[>] 0)
      (𝓝 (⟪w, chainGen F t w⟫_ℂ).re) :=
    (Complex.continuous_re.tendsto _).comp ((tendsto_const_nhds (x := w)).inner hlim)
  refine ge_of_tendsto h1 (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  have hε0 : (0 : ℝ) < ε := hε
  rw [← Complex.coe_smul, inner_smul_right, Complex.re_ofReal_mul]
  exact mul_nonneg (inv_nonneg.mpr hε0.le)
    (hF.re_inner_sub_transition_nonneg hO ht (by linarith) hw)

lemma chainField_eq {t : ℝ} (hgood : IsGoodTime F t) : chainField F t = chainGen F t := by
  simp only [chainField, isCaratheodory_chainGen hF hO hloc hgood, ↓reduceIte]

/-- Almost every `t ≥ 0` is a good time. -/
lemma ae_restrict_isGoodTime : ∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))), IsGoodTime F t := by
  rw [ae_restrict_iff' measurableSet_Ici]
  have h2 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
  filter_upwards [ae_isGoodTime hF hO hloc, h2] with t ht ht0 htI
  exact ht (lt_of_le_of_ne htI (Ne.symm ht0))

/-- `t ↦ h(w, t)` is measurable. -/
theorem aestronglyMeasurable_chainField {w : E} (hw : w ∈ unitBall E) :
    AEStronglyMeasurable (fun t => chainField F t w) (volume.restrict (Ici 0)) := by
  have hgood := ae_restrict_isGoodTime hF hO hloc
  have hinv : ContinuousOn (fun t => Ring.inverse (fderiv ℂ (F t) w)) (Ici 0) := by
    intro t ht
    have hu := hF.isUnit_fderiv hO ht hw
    have h1 := NormedRing.inverse_continuousAt hu.unit
    rw [IsUnit.unit_spec] at h1
    exact ContinuousAt.comp_continuousWithinAt (f := fun τ => fderiv ℂ (F τ) w) h1
      (hF.continuousOn_fderiv hloc hO hw t ht)
  have hderiv : AEStronglyMeasurable (fun t => chainDeriv F t w) (volume.restrict (Ici 0)) := by
    set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
    have hε0 : ∀ n, 0 < ε n := fun n => by positivity
    have hεlim : Tendsto ε atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall hε0⟩
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n t => (ε n)⁻¹ • (F (t + ε n) w - F t w)) (fun n => ?_) ?_
    · have hc1 : ContinuousOn (fun t => F (t + ε n) w) (Ici 0) :=
        (hF.continuousOn_apply hloc hO hw).comp (continuousOn_id.add continuousOn_const)
          fun t ht => by
            simp only [mem_Ici] at ht ⊢
            linarith [hε0 n]
      exact ((hc1.sub (hF.continuousOn_apply hloc hO hw)).const_smul _).aestronglyMeasurable
        measurableSet_Ici
    · filter_upwards [hgood] with t ht
      exact (tendsto_chainDeriv hF hO hloc ht hw).comp hεlim
  have hgen : AEStronglyMeasurable (fun t => chainGen F t w) (volume.restrict (Ici 0)) :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (A : E →L[ℂ] E) (x : E) => A x)
      isBoundedBilinearMap_apply.continuous (hinv.aestronglyMeasurable measurableSet_Ici) hderiv
  refine hgen.congr ?_
  filter_upwards [hgood] with t ht
  rw [chainField_eq hF hO hloc ht]

/-- The **Herglotz vector field** of the chain. -/
theorem isHerglotzVF_chainField : IsHerglotzVF (chainField F) where
  isCaratheodory t _ := isCaratheodory_chainField t
  aestronglyMeasurable _ hw := aestronglyMeasurable_chainField hF hO hloc hw

end IsLoewnerChain

end LoewnerS0
