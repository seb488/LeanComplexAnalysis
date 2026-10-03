import LoewnerS0.Osgood
import LoewnerS0.StarlikeGen
import LoewnerS0.ClassM

/-!
# Starlike maps have parametric representation (assuming Osgood's theorem)

Let `f ∈ S*(𝔹)` be a normalized starlike map of the unit ball `𝔹` of a finite-dimensional complex
inner product space. Assuming Osgood's theorem (`LoewnerS0.OsgoodTheorem`), we show that
`f ∈ S⁰(𝔹)` (`LoewnerS0.classSstar_subset_classS0_of_osgood`).

* By Osgood's theorem and the inverse function theorem, `f` is biholomorphic from `𝔹` onto the
  open set `f(𝔹)`, with inverse `g = invFunOn f 𝔹` (`LoewnerS0.OsgoodTheorem.hasFDerivAt_invFunOn`).
* `h(z) = Dg(f(z)) f(z) = Df(z)⁻¹ f(z)` (`LoewnerS0.starlikeGenerator`) is a normalized holomorphic
  map of `𝔹` with `Df(z) h(z) = f(z)`.
* **Suffridge's argument**: since `f(𝔹)` is starlike, `v_t = g ∘ (e^{-t} f)` is a holomorphic
  self-map of `𝔹` fixing `0`, so `‖v_t(z)‖ ≤ ‖z‖` by the Schwarz lemma. As `v_0(z) = z` and
  `∂_t v_t(z)|_{t=0} = -h(z)`, this gives `Re ⟨h(z), z⟩ ≥ 0`, and `h ∈ M(𝔹)` by the minimum
  principle (`LoewnerS0.IsNormalized.isCaratheodory_of_re_inner_nonneg`).
* Along the flow `φ_t` of `h`, `e^t f(φ_t(z))` is constant (because `Df · h = f`), equal to `f(z)`;
  since `f(w) = w + o(‖w‖)` and `e^t φ_t(z)` converges, `e^t φ_t(z) → f(z)`. So `f` has parametric
  representation, with the constant Herglotz vector field `h` (`isParametricRep_of_mem_classSstar`).

## References

* [Suf70] T. J. Suffridge, *The principle of subordination applied to functions of several
  variables*, Pacific J. Math. 33 (1970).
* [GK03] I. Graham, G. Kohr, *Geometric Function Theory in One and Higher Dimensions*,
  Dekker 2003, Chapter 6.
-/

open Function Complex Metric Set Filter Asymptotics
open scoped Topology InnerProductSpace

noncomputable section

namespace LoewnerS0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {f : E → E}

/-- The generator `h(z) = Df(z)⁻¹ f(z)` of a starlike map `f`, written with the inverse
`g = invFunOn f 𝔹` of `f`: `h(z) = Dg(f(z)) f(z)`. -/
def starlikeGenerator (f : E → E) (z : E) : E :=
  fderiv ℂ (invFunOn f (unitBall E)) (f z) (f z)

namespace StarlikeOsgood

variable (hO : OsgoodTheorem E) (hf : f ∈ classSstar E)
include hf

omit [FiniteDimensional ℂ E] in
lemma isNormalized : IsNormalized f := hf.1.1

omit [FiniteDimensional ℂ E] in
lemma injOn : InjOn f (unitBall E) := hf.1.2

omit [FiniteDimensional ℂ E] in
lemma invFunOn_apply {z : E} (hz : z ∈ unitBall E) : invFunOn f (unitBall E) (f z) = z :=
  (injOn hf).leftInvOn_invFunOn hz

omit [FiniteDimensional ℂ E] in
lemma invFunOn_zero : invFunOn f (unitBall E) 0 = 0 := by
  have := invFunOn_apply hf zero_mem_unitBall
  rwa [(isNormalized hf).map_zero] at this

omit [FiniteDimensional ℂ E] in
/-- `c f(z) ∈ f(𝔹)` for `0 ≤ c ≤ 1` (starlikeness). -/
lemma smul_mem_image {z : E} (hz : z ∈ unitBall E) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (c : ℂ) • f z ∈ f '' unitBall E := by
  rw [Complex.coe_smul]
  exact hf.2.smul_mem (mem_image_of_mem f hz) hc0 hc1

omit [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] hf in
lemma invFunOn_mem {y : E} (hy : y ∈ f '' unitBall E) : invFunOn f (unitBall E) y ∈ unitBall E := by
  obtain ⟨z, hz, rfl⟩ := hy
  exact Function.invFunOn_mem ⟨z, hz, rfl⟩

include hO

lemma isOpen_image : IsOpen (f '' unitBall E) :=
  hO.isOpen_image isOpen_unitBall (isNormalized hf).differentiableOn (injOn hf)

lemma differentiableOn_invFunOn :
    DifferentiableOn ℂ (invFunOn f (unitBall E)) (f '' unitBall E) :=
  hO.differentiableOn_invFunOn isOpen_unitBall (isNormalized hf).differentiableOn (injOn hf)

lemma differentiableAt_invFunOn {y : E} (hy : y ∈ f '' unitBall E) :
    DifferentiableAt ℂ (invFunOn f (unitBall E)) y :=
  (differentiableOn_invFunOn hO hf y hy).differentiableAt ((isOpen_image hO hf).mem_nhds hy)

/-- `Df(z) h(z) = f(z)`. -/
lemma fderiv_apply_starlikeGenerator {z : E} (hz : z ∈ unitBall E) :
    fderiv ℂ f z (starlikeGenerator f z) = f z :=
  hO.fderiv_apply_fderiv_invFunOn isOpen_unitBall (isNormalized hf).differentiableOn (injOn hf) hz
    (f z)

/-- `h` is holomorphic. -/
lemma differentiableOn_starlikeGenerator :
    DifferentiableOn ℂ (starlikeGenerator f) (unitBall E) := by
  have hV := isOpen_image hO hf
  have hD : DifferentiableOn ℂ (fderiv ℂ (invFunOn f (unitBall E))) (f '' unitBall E) :=
    (((differentiableOn_invFunOn hO hf).contDiffOn_of_isOpen hV 2).fderiv_of_isOpen hV
      (m := 1) (by norm_num)).differentiableOn (by norm_num)
  intro z hz
  have hfz := (isNormalized hf).differentiableAt hz
  have h1 : DifferentiableAt ℂ (fun w => fderiv ℂ (invFunOn f (unitBall E)) (f w)) z :=
    ((hD (f z) (mem_image_of_mem f hz)).differentiableAt
      (hV.mem_nhds (mem_image_of_mem f hz))).comp z hfz
  exact (h1.clm_apply hfz).differentiableWithinAt

/-- `h` is normalized. -/
lemma isNormalized_starlikeGenerator : IsNormalized (starlikeGenerator f) where
  differentiableOn := differentiableOn_starlikeGenerator hO hf
  map_zero := by simp [starlikeGenerator, (isNormalized hf).map_zero]
  fderiv_zero := by
    have hN := isNormalized hf
    have hD := (differentiableOn_starlikeGenerator hO hf)
    have hV := isOpen_image hO hf
    obtain ⟨e, he, hge⟩ := hO.hasFDerivAt_invFunOn isOpen_unitBall hN.differentiableOn
      (injOn hf) zero_mem_unitBall
    rw [hN.fderiv_zero] at he
    have he' : (e.symm : E →L[ℂ] E) = ContinuousLinearMap.id ℂ E := by
      ext v
      have := e.apply_symm_apply v
      rw [← ContinuousLinearEquiv.coe_coe, he] at this
      simpa using this
    -- the derivative of `z ↦ Dg(f z)` at `0`
    have hc : DifferentiableAt ℂ (fun w => fderiv ℂ (invFunOn f (unitBall E)) (f w)) 0 := by
      have hD' : DifferentiableOn ℂ (fderiv ℂ (invFunOn f (unitBall E))) (f '' unitBall E) :=
        (((differentiableOn_invFunOn hO hf).contDiffOn_of_isOpen hV 2).fderiv_of_isOpen hV
          (m := 1) (by norm_num)).differentiableOn (by norm_num)
      exact ((hD' (f 0) (mem_image_of_mem f zero_mem_unitBall)).differentiableAt
        (hV.mem_nhds (mem_image_of_mem f zero_mem_unitBall))).comp 0
        (hN.differentiableAt zero_mem_unitBall)
    have key := hc.hasFDerivAt.clm_apply hN.hasFDerivAt_zero
    have hg0 : fderiv ℂ (invFunOn f (unitBall E)) (f 0) = ContinuousLinearMap.id ℂ E := by
      rw [hge.fderiv, he']
    rw [hg0, hN.map_zero, ContinuousLinearMap.map_zero, add_zero,
      ContinuousLinearMap.id_comp] at key
    exact key.fderiv

/-- **Suffridge's argument**: `Re ⟨h(z), z⟩ ≥ 0`. -/
lemma re_inner_starlikeGenerator_nonneg {z : E} (hz : z ∈ unitBall E) :
    0 ≤ (⟪z, starlikeGenerator f z⟫_ℂ).re := by
  have hN := isNormalized hf
  set g := invFunOn f (unitBall E) with hg_def
  -- Schwarz: `‖g(c f(z))‖ ≤ ‖z‖` for `0 ≤ c ≤ 1`
  have hschwarz : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → ‖g (c • f z)‖ ≤ ‖z‖ := by
    intro c hc0 hc1
    set Φ : E → E := fun w => g ((c : ℂ) • f w) with hΦ
    have hΦ0 : Φ 0 = 0 := by simp [hΦ, hN.map_zero, hg_def, invFunOn_zero hf]
    have hd : DifferentiableOn ℂ Φ (ball 0 1) := fun w hw => by
      have h1 : DifferentiableAt ℂ (fun w => (c : ℂ) • f w) w :=
        (hN.differentiableAt hw).const_smul (c : ℂ)
      exact ((differentiableAt_invFunOn hO hf (smul_mem_image hf hw hc0 hc1)).comp w
        h1).differentiableWithinAt
    have hmaps : MapsTo Φ (ball 0 1) (closedBall (Φ 0) 1) := fun w hw => by
      rw [hΦ0, mem_closedBall_zero_iff]
      exact (mem_unitBall.mp (invFunOn_mem (smul_mem_image hf hw hc0 hc1))).le
    have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps hz
    rw [hΦ0, div_one, one_mul, dist_zero_right, dist_zero_right] at this
    simpa [hΦ, Complex.coe_smul] using this
  -- the curve `c(τ) = g(e^{-τ} f(z))` and its derivative `-h(z)` at `τ = 0`
  obtain ⟨e, he, hge⟩ := hO.hasFDerivAt_invFunOn isOpen_unitBall hN.differentiableOn
    (injOn hf) hz
  have hgen : starlikeGenerator f z = e.symm (f z) := by
    rw [starlikeGenerator, ← hg_def, hge.fderiv]; rfl
  have h1 : HasDerivAt (fun τ : ℝ => Real.exp (-τ) • f z) (-(f z)) 0 := by
    have := ((hasDerivAt_neg (0 : ℝ)).exp).smul_const (f z)
    simpa using this
  have h2 : HasDerivAt (fun τ : ℝ => g (Real.exp (-τ) • f z)) (e.symm (-(f z))) 0 := by
    have h3 : HasFDerivAt g (e.symm : E →L[ℂ] E) (Real.exp (-(0 : ℝ)) • f z) := by
      simpa using hge
    exact (h3.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) h1
  have h4 := hasDerivWithinAt_norm_sq (s := univ) h2.hasDerivWithinAt
  rw [hasDerivWithinAt_univ] at h4
  have hc0 : g (Real.exp (-(0 : ℝ)) • f z) = z := by
    simp [hg_def, invFunOn_apply hf hz]
  rw [hc0] at h4
  -- `‖c(τ)‖² ≤ ‖c(0)‖²` for `τ ≥ 0`, so the derivative at `0` is `≤ 0`
  have hlim := h4.tendsto_slope_zero_right
  have hle : 2 * (⟪z, e.symm (-(f z))⟫_ℂ).re ≤ 0 := by
    refine le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun τ hτ => ?_)
    have hτ : 0 < τ := hτ
    have hb := hschwarz (Real.exp (-τ)) (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hτ.le))
    simp only [zero_add, smul_eq_mul]
    rw [hc0]
    refine mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hτ.le) (sub_nonpos.mpr ?_)
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [map_neg, inner_neg_right, Complex.neg_re, ← hgen] at hle
  linarith

/-- `h ∈ M(𝔹)`. -/
theorem isCaratheodory_starlikeGenerator : IsCaratheodory (starlikeGenerator f) :=
  (isNormalized_starlikeGenerator hO hf).isCaratheodory_of_re_inner_nonneg
    fun _ hz => re_inner_starlikeGenerator_nonneg hO hf hz

/-- `e^t f(φ_t(z)) = f(z)` along the flow `φ_t` of `h`. -/
lemma exp_smul_flow {z : E} (hz : z ∈ unitBall E) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp t • f (flow (isCaratheodory_starlikeGenerator hO hf) t z) = f z := by
  set hh := isCaratheodory_starlikeGenerator hO hf
  have hN := isNormalized hf
  have hcont : ContinuousOn (fun τ => Real.exp τ • f (flow hh τ z)) (Icc 0 t) :=
    Real.continuous_exp.continuousOn.smul (hN.differentiableOn.continuousOn.comp
      ((continuousOn_flow hh hz).mono Icc_subset_Ici_self) fun τ hτ => flow_mem hh hz hτ.1)
  have hderiv : ∀ x ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt (fun τ => Real.exp τ • f (flow hh τ z)) 0 (Ici x) x := by
    intro x hx
    have hw := flow_mem hh hz hx.1
    have h1 := ((hN.differentiableAt hw).hasFDerivAt.restrictScalars ℝ).comp_hasDerivWithinAt x
      (hasDerivWithinAt_flow hh hz hx.1)
    have h2 : HasDerivWithinAt (fun τ => Real.exp τ • f (flow hh τ z))
        (Real.exp x • fderiv ℂ f (flow hh x z) (-starlikeGenerator f (flow hh x z)) +
          Real.exp x • f (flow hh x z)) (Ici x) x :=
      (Real.hasDerivAt_exp x).hasDerivWithinAt.smul h1
    convert h2 using 1
    rw [map_neg, fderiv_apply_starlikeGenerator hO hf hw, smul_neg, neg_add_cancel]
  have := constant_of_has_deriv_right_zero hcont hderiv t (right_mem_Icc.mpr ht)
  rw [this, Real.exp_zero, one_smul, flow_zero hh hz]

/-- **Parametric representation of starlike maps** (assuming Osgood's theorem): `f(z) =
lim e^t φ_t(z)`, where `φ_t` is the flow of the generator `h = Df⁻¹ f ∈ M(𝔹)`. -/
theorem isParametricRep_of_mem_classSstar :
    IsParametricRep f (fun _ => starlikeGenerator f)
      (fun t z => flow (isCaratheodory_starlikeGenerator hO hf) t z) := by
  set hh := isCaratheodory_starlikeGenerator hO hf
  have hP := isParametricRep_starlikeMap hh
  refine ⟨hP.herglotz, hP.solution, fun z hz => ?_⟩
  have hN := isNormalized hf
  have hlim := tendsto_scaledFlow hh hz
  -- `φ_t(z) → 0`
  have h0 : Tendsto (fun t => flow hh t z) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.smul hlim
    rw [zero_smul] at this
    refine this.congr fun t => ?_
    simp only [scaledFlow, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
  -- `f(w) - w = o(‖w‖)`
  have hlo : (fun w => f w - w) =o[𝓝 0] fun w => w := by
    refine (hasFDerivAt_iff_isLittleO_nhds_zero.mp hN.hasFDerivAt_zero).congr_left fun w => ?_
    simp [hN.map_zero]
  have h1 := (isBigO_refl (fun t : ℝ => Real.exp t) atTop).smul_isLittleO (hlo.comp_tendsto h0)
  have h2 := h1.trans_isBigO (hlim.isBigO_one ℝ)
  rw [isLittleO_one_iff] at h2
  -- `e^t (f(φ_t z) - φ_t z) = f(z) - e^t φ_t(z)`
  have h3 : Tendsto (fun t => f z - Real.exp t • (f (flow hh t z) - flow hh t z)) atTop
      (𝓝 (f z)) := by
    simpa using (tendsto_const_nhds (x := f z)).sub h2
  refine h3.congr' (eventually_atTop.mpr ⟨0, fun t ht => ?_⟩)
  show _ = ((Real.exp t : ℝ) : ℂ) • flow hh t z
  rw [smul_sub, exp_smul_flow hO hf hz ht, Complex.coe_smul]
  abel

end StarlikeOsgood

/-- **Starlike maps have parametric representation**, assuming Osgood's theorem:
`S*(𝔹) ⊆ S⁰(𝔹)`. -/
theorem classSstar_subset_classS0_of_osgood (hO : OsgoodTheorem E) :
    classSstar E ⊆ classS0 E := fun _ hf =>
  ⟨_, _, StarlikeOsgood.isParametricRep_of_mem_classSstar hO hf⟩

end LoewnerS0
