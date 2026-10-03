import LoewnerS0.Osgood
import LoewnerS0.ClassM
import LoewnerS0.Examples

/-!
# Transition maps of Loewner chains (assuming Osgood's theorem)

Let `F` be a Loewner chain on the unit ball `𝔹` of a finite-dimensional complex inner product
space. Its *transition maps* are `v(z, s, t) = F_t⁻¹(F_s(z))` for `0 ≤ s ≤ t`
(`LoewnerS0.transition`), where `F_t⁻¹ = invFunOn (F t) 𝔹`; they are self-maps of `𝔹` with
`F_t ∘ v(·, s, t) = F_s` and `v(·, s, u) = v(·, t, u) ∘ v(·, s, t)`.

Assuming Osgood's theorem (so that `F_t⁻¹` is holomorphic on the open set `F_t(𝔹)`), the transition
maps are holomorphic, with `v(0, s, t) = 0` and `Dv(0, s, t) = e^{s-t} I`. By the Schwarz lemma
`‖v(z, s, t)‖ ≤ ‖z‖`; so `p(z) = (z - v(z, s, t))/(1 - e^{s-t})` is a normalized map with
`Re ⟨p(z), z⟩ ≥ 0`, hence `p ∈ M(𝔹)` by the minimum principle
(`LoewnerS0.IsLoewnerChain.isCaratheodory_transition`), and the growth estimate of `M(𝔹)` gives

  `‖z - v(z, s, t)‖ ≤ (1 - e^{s-t}) 4‖z‖/(1-‖z‖)² ≤ (t - s) 4‖z‖/(1-‖z‖)²`

(`LoewnerS0.IsLoewnerChain.norm_sub_transition_le`).
-/

open Function Complex Metric Set Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace LoewnerS0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {F : ℝ → E → E}

/-- The transition maps `v(z, s, t) = F_t⁻¹(F_s(z))` of a Loewner chain `F`. -/
def transition (F : ℝ → E → E) (s t : ℝ) (z : E) : E :=
  invFunOn (F t) (unitBall E) (F s z)

lemma one_sub_exp_sub_le {s t : ℝ} : 1 - Real.exp (s - t) ≤ t - s := by
  have := Real.add_one_le_exp (s - t)
  linarith

lemma one_sub_exp_sub_nonneg {s t : ℝ} (hst : s ≤ t) : 0 ≤ 1 - Real.exp (s - t) := by
  have : Real.exp (s - t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

lemma one_sub_exp_sub_pos {s t : ℝ} (hst : s < t) : 0 < 1 - Real.exp (s - t) := by
  have : Real.exp (s - t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

/-- `4ρ/(1-ρ)²` is monotone on `[0, 1)`. -/
lemma growth_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    4 * a / (1 - a) ^ 2 ≤ 4 * b / (1 - b) ^ 2 := by
  have h1 : 0 < 1 - b := by linarith
  have h2 : (1 - b) ^ 2 ≤ (1 - a) ^ 2 := by nlinarith
  exact div_le_div₀ (by linarith) (by linarith) (by positivity) h2

/-- `8ρ²/(1-ρ)²` is monotone on `[0, 1)`. -/
lemma growth_sq_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    8 * a ^ 2 / (1 - a) ^ 2 ≤ 8 * b ^ 2 / (1 - b) ^ 2 := by
  have h1 : 0 < 1 - b := by linarith
  have h2 : (1 - b) ^ 2 ≤ (1 - a) ^ 2 := by nlinarith
  have h3 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
  exact div_le_div₀ (by positivity) (by linarith) (by positivity) h2

namespace IsLoewnerChain

variable (hF : IsLoewnerChain F)
include hF

lemma mem_image {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {z : E} (hz : z ∈ unitBall E) :
    F s z ∈ F t '' unitBall E :=
  hF.image_subset s t hs hst (mem_image_of_mem _ hz)

lemma transition_mem {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {z : E} (hz : z ∈ unitBall E) :
    transition F s t z ∈ unitBall E := by
  obtain ⟨w, hw, hwz⟩ := hF.mem_image hs hst hz
  exact invFunOn_mem ⟨w, hw, hwz⟩

/-- `F_t(v(z, s, t)) = F_s(z)`. -/
lemma apply_transition {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {z : E} (hz : z ∈ unitBall E) :
    F t (transition F s t z) = F s z := by
  obtain ⟨w, hw, hwz⟩ := hF.mem_image hs hst hz
  exact invFunOn_eq ⟨w, hw, hwz⟩

lemma transition_self {s : ℝ} (hs : 0 ≤ s) {z : E} (hz : z ∈ unitBall E) :
    transition F s s z = z :=
  (hF.injOn s hs).leftInvOn_invFunOn hz

lemma transition_zero {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : transition F s t 0 = 0 := by
  have ht : 0 ≤ t := hs.trans hst
  have h := hF.transition_self ht zero_mem_unitBall
  simp only [transition, hF.map_zero t ht] at h
  simp only [transition, hF.map_zero s hs]
  exact h

/-- The **semigroup property** `v(·, s, u) = v(·, t, u) ∘ v(·, s, t)`. -/
lemma transition_transition {s t u : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htu : t ≤ u) {z : E}
    (hz : z ∈ unitBall E) :
    transition F t u (transition F s t z) = transition F s u z := by
  have ht : 0 ≤ t := hs.trans hst
  have hu : 0 ≤ u := ht.trans htu
  have h1 := hF.transition_mem hs hst hz
  refine hF.injOn u hu (hF.transition_mem ht htu h1) (hF.transition_mem hs (hst.trans htu) hz) ?_
  rw [hF.apply_transition ht htu h1, hF.apply_transition hs hst hz,
    hF.apply_transition hs (hst.trans htu) hz]

variable [FiniteDimensional ℂ E] (hO : OsgoodTheorem E)
include hO

/-- The transition maps are holomorphic. -/
lemma differentiableOn_transition {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    DifferentiableOn ℂ (transition F s t) (unitBall E) := by
  have ht : 0 ≤ t := hs.trans hst
  have hg := hO.differentiableOn_invFunOn isOpen_unitBall (hF.differentiableOn t ht)
    (hF.injOn t ht)
  exact hg.comp (hF.differentiableOn s hs) fun z hz => hF.mem_image hs hst hz

/-- `Dv(0, s, t) = e^{s-t} I`. -/
lemma hasFDerivAt_transition_zero {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    HasFDerivAt (transition F s t) ((Real.exp (s - t) : ℂ) • ContinuousLinearMap.id ℂ E) 0 := by
  have ht : 0 ≤ t := hs.trans hst
  obtain ⟨e, he, hge⟩ := hO.hasFDerivAt_invFunOn isOpen_unitBall (hF.differentiableOn t ht)
    (hF.injOn t ht) zero_mem_unitBall
  rw [hF.fderiv_zero t ht] at he
  have hes : (e.symm : E →L[ℂ] E) = (Real.exp (-t) : ℂ) • ContinuousLinearMap.id ℂ E := by
    ext v
    have h1 := e.apply_symm_apply v
    rw [← ContinuousLinearEquiv.coe_coe, he] at h1
    simp only [smul_apply, ContinuousLinearMap.id_apply] at h1
    simp only [ContinuousLinearEquiv.coe_coe, smul_apply,
      ContinuousLinearMap.id_apply]
    conv_rhs => rw [← h1]
    rw [smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      Complex.ofReal_one, one_smul]
  have hfs : HasFDerivAt (F s) ((Real.exp s : ℂ) • ContinuousLinearMap.id ℂ E) 0 := by
    rw [← hF.fderiv_zero s hs]
    exact ((hF.differentiableOn s hs).differentiableAt
      (unitBall_mem_nhds zero_mem_unitBall)).hasFDerivAt
  have hg0 : F t 0 = F s 0 := by rw [hF.map_zero t ht, hF.map_zero s hs]
  rw [hg0, hes] at hge
  have e1 : transition F s t = invFunOn (F t) (unitBall E) ∘ F s := rfl
  rw [e1]
  convert hge.comp 0 hfs using 1
  ext v
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, map_smul, smul_smul]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  ring_nf

/-- **Schwarz lemma** for the transition maps: `‖v(z, s, t)‖ ≤ ‖z‖`. -/
lemma norm_transition_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {z : E} (hz : z ∈ unitBall E) :
    ‖transition F s t z‖ ≤ ‖z‖ := by
  have hd := hF.differentiableOn_transition hO hs hst
  have hmaps : MapsTo (transition F s t) (ball 0 1) (closedBall (transition F s t 0) 1) := by
    intro w hw
    rw [hF.transition_zero hs hst, mem_closedBall_zero_iff]
    exact (mem_unitBall.mp (hF.transition_mem hs hst hw)).le
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps hz
  rwa [hF.transition_zero hs hst, div_one, one_mul, dist_zero_right, dist_zero_right] at this

/-- `Re ⟨z - v(z, s, t), z⟩ ≥ 0`. -/
lemma re_inner_sub_transition_nonneg {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {z : E}
    (hz : z ∈ unitBall E) : 0 ≤ (⟪z, z - transition F s t z⟫_ℂ).re := by
  rw [inner_sub_right, Complex.sub_re, re_inner_self]
  have h1 : (⟪z, transition F s t z⟫_ℂ).re ≤ ‖z‖ * ‖z‖ :=
    (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hF.norm_transition_le hO hs hst hz) (norm_nonneg _)))
  nlinarith

/-- `p(z) = (z - v(z, s, t))/(1 - e^{s-t})` belongs to `M(𝔹)` for `s < t`. -/
theorem isCaratheodory_transition {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    IsCaratheodory fun z => ((1 - Real.exp (s - t) : ℝ) : ℂ)⁻¹ • (z - transition F s t z) := by
  have hc : 0 < 1 - Real.exp (s - t) := one_sub_exp_sub_pos hst
  have hc' : ((1 - Real.exp (s - t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hN : IsNormalized fun z => ((1 - Real.exp (s - t) : ℝ) : ℂ)⁻¹ • (z - transition F s t z) :=
    { differentiableOn :=
        (differentiableOn_id.sub (hF.differentiableOn_transition hO hs hst.le)).const_smul _
      map_zero := by simp [hF.transition_zero hs hst.le]
      fderiv_zero := by
        have h1 := ((hasFDerivAt_id (0 : E)).sub
          (hF.hasFDerivAt_transition_zero hO hs hst.le)).const_smul
          ((1 - Real.exp (s - t) : ℝ) : ℂ)⁻¹
        refine h1.fderiv.trans ?_
        ext v
        simp only [smul_apply, sub_apply,
          ContinuousLinearMap.id_apply]
        have : v - ((Real.exp (s - t) : ℝ) : ℂ) • v = ((1 - Real.exp (s - t) : ℝ) : ℂ) • v := by
          rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
        rw [this, smul_smul, inv_mul_cancel₀ hc', one_smul] }
  refine hN.isCaratheodory_of_re_inner_nonneg fun z hz => ?_
  rw [inner_smul_right, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  exact mul_nonneg (inv_nonneg.mpr hc.le) (hF.re_inner_sub_transition_nonneg hO hs hst.le hz)

/-- `‖z - v(z, s, t)‖ ≤ (1 - e^{s-t}) 4r/(1-r)²` for `‖z‖ ≤ r < 1`. -/
theorem norm_sub_transition_le {s t r : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hr : r < 1) {z : E}
    (hzr : ‖z‖ ≤ r) :
    ‖z - transition F s t z‖ ≤ (1 - Real.exp (s - t)) * (4 * r / (1 - r) ^ 2) := by
  have hz : z ∈ unitBall E := mem_unitBall.mpr (hzr.trans_lt hr)
  rcases hst.eq_or_lt with rfl | hlt
  · rw [hF.transition_self hs hz, sub_self, norm_zero, sub_self, Real.exp_zero, sub_self,
      zero_mul]
  have hc : 0 < 1 - Real.exp (s - t) := one_sub_exp_sub_pos hlt
  have hc' : ((1 - Real.exp (s - t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hp := (hF.isCaratheodory_transition hO hs hlt).norm_le_of_norm_le hr hzr
  have heq : z - transition F s t z = ((1 - Real.exp (s - t) : ℝ) : ℂ) •
      (((1 - Real.exp (s - t) : ℝ) : ℂ)⁻¹ • (z - transition F s t z)) := by
    rw [smul_smul, mul_inv_cancel₀ hc', one_smul]
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left hp hc.le

/-- `‖(z - v(z, s, t)) - (1 - e^{s-t}) z‖ ≤ (1 - e^{s-t}) 8‖z‖²/(1-‖z‖)²`. -/
theorem norm_sub_transition_sub_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {z : E}
    (hz : z ∈ unitBall E) :
    ‖(z - transition F s t z) - ((1 - Real.exp (s - t) : ℝ) : ℂ) • z‖ ≤
      (1 - Real.exp (s - t)) * (8 * ‖z‖ ^ 2 / (1 - ‖z‖) ^ 2) := by
  rcases hst.eq_or_lt with rfl | hlt
  · rw [hF.transition_self hs hz]
    simp
  have hc : 0 < 1 - Real.exp (s - t) := one_sub_exp_sub_pos hlt
  have hc' : ((1 - Real.exp (s - t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hp := (hF.isCaratheodory_transition hO hs hlt).norm_sub_le hz
  have heq : (z - transition F s t z) - ((1 - Real.exp (s - t) : ℝ) : ℂ) • z =
      ((1 - Real.exp (s - t) : ℝ) : ℂ) •
        ((((1 - Real.exp (s - t) : ℝ) : ℂ)⁻¹ • (z - transition F s t z)) - z) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hc', one_smul]
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left hp hc.le

end IsLoewnerChain

end LoewnerS0
