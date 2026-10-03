import LoewnerS0.Loewner

/-!
# First examples and closure properties

* `id ∈ M(𝔹)`, `id ∈ S(𝔹)`, and `id ∈ S⁰(𝔹)`: the constant Herglotz vector field `h t = id`
  has the solution `v(z, t) = e⁻ᵗ z` and `eᵗ v(z, t) = z`.
* `M(𝔹)` is convex.
* The Koebe generator `h(z) = (1 + ⟨z, u⟩)/(1 - ⟨z, u⟩) · z` belongs to `M(𝔹)` for `‖u‖ ≤ 1`.
* `f(z, t) = eᵗ z` is a Loewner chain, so `id ∈ classS0'`.
-/

open Complex Metric Set Filter MeasureTheory
open scoped InnerProductSpace Topology

noncomputable section

namespace LoewnerS0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### The identity map -/

lemma re_inner_self (z : E) : (⟪z, z⟫_ℂ).re = ‖z‖ ^ 2 := by
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) z

lemma im_inner_self (z : E) : (⟪z, z⟫_ℂ).im = 0 := by
  simpa using inner_self_im (𝕜 := ℂ) z

/-- `h = id` satisfies the Carathéodory condition, since `⟨z, z⟩ = ‖z‖² > 0`. -/
lemma isCaratheodory_id : IsCaratheodory (id : E → E) where
  isNormalized := isNormalized_id
  re_inner_pos z _ hz := by
    show 0 < (⟪z, z⟫_ℂ).re
    rw [re_inner_self]
    exact pow_pos (norm_pos_iff.mpr hz) 2

/-- `h = id` belongs to the Carathéodory class. -/
theorem id_mem_classM : (id : E → E) ∈ classM E := isCaratheodory_id

/-- The identity map belongs to `S(𝔹)`. -/
theorem id_mem_classS : (id : E → E) ∈ classS E :=
  ⟨isNormalized_id, injOn_id _⟩

/-- `∫₀ᵗ e⁻ˢ ds = 1 - e⁻ᵗ`. -/
lemma integral_exp_neg (t : ℝ) : ∫ s in (0)..t, Real.exp (-s) = 1 - Real.exp (-t) := by
  rw [intervalIntegral.integral_comp_neg (fun s => Real.exp s)]
  simp [integral_exp]

/-- The constant Herglotz vector field `h t = id`. -/
lemma isHerglotzVF_id : IsHerglotzVF (fun _ : ℝ => (id : E → E)) where
  isCaratheodory _ _ := isCaratheodory_id
  aestronglyMeasurable _ _ := aestronglyMeasurable_const

/-- `v(z, t) = e⁻ᵗ z` solves the Loewner ODE of the constant field `h t = id`. -/
lemma isLoewnerSolution_id [CompleteSpace E] :
    IsLoewnerSolution (fun _ : ℝ => (id : E → E)) (fun t z => (Real.exp (-t) : ℂ) • z) := by
  intro z hz t ht
  have hcont : Continuous fun s : ℝ => (Real.exp (-s) : ℂ) • z :=
    (continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).smul continuous_const
  refine ⟨?_, hcont.intervalIntegrable _ _, ?_⟩
  · rw [mem_unitBall] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc Real.exp (-t) * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < 1 := by simpa using hz
  · simp only [id_eq]
    rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_ofReal, integral_exp_neg,
      Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, sub_sub_cancel]

/-- The identity map belongs to `S⁰(𝔹)`. -/
theorem id_mem_classS0 [CompleteSpace E] : (id : E → E) ∈ classS0 E := by
  refine ⟨fun _ => id, fun t z => (Real.exp (-t) : ℂ) • z, isHerglotzVF_id,
    isLoewnerSolution_id, fun z _ => ?_⟩
  have h : (fun t : ℝ => (Real.exp t : ℂ) • ((Real.exp (-t) : ℂ) • z)) = fun _ => z := by
    funext t
    rw [smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      Complex.ofReal_one, one_smul]
  show Tendsto (fun t : ℝ => (Real.exp t : ℂ) • ((Real.exp (-t) : ℂ) • z)) atTop (𝓝 z)
  rw [h]
  exact tendsto_const_nhds

/-! ### Convexity of `M(𝔹)` -/

/-- The Carathéodory class `M(𝔹)` is convex. -/
theorem convex_classM : Convex ℝ (classM E) := by
  intro h₁ hh₁ h₂ hh₂ a b ha hb hab
  replace hh₁ : IsCaratheodory h₁ := hh₁
  replace hh₂ : IsCaratheodory h₂ := hh₂
  have key : a • h₁ + b • h₂ = fun z => (a : ℂ) • h₁ z + (b : ℂ) • h₂ z := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  rw [key]
  have hd₁ := hh₁.isNormalized.differentiableAt_zero
  have hd₂ := hh₂.isNormalized.differentiableAt_zero
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact (hh₁.isNormalized.differentiableOn.fun_const_smul (a : ℂ)).fun_add
      (hh₂.isNormalized.differentiableOn.fun_const_smul (b : ℂ))
  · simp [hh₁.map_zero, hh₂.map_zero]
  · rw [fderiv_fun_add (hd₁.fun_const_smul _) (hd₂.fun_const_smul _),
      fderiv_fun_const_smul hd₁, fderiv_fun_const_smul hd₂, hh₁.isNormalized.fderiv_zero,
      hh₂.isNormalized.fderiv_zero, ← add_smul, ← Complex.ofReal_add, hab, Complex.ofReal_one,
      one_smul]
  · intro z hz hz0
    have h1 := hh₁.re_inner_pos z hz hz0
    have h2 := hh₂.re_inner_pos z hz hz0
    rw [inner_add_right, inner_smul_right, inner_smul_right, Complex.add_re,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' h1) (mul_nonneg hb h2.le)
    · have hb' : 0 < b := by rw [← ha'] at hab; linarith
      exact add_pos_of_nonneg_of_pos (mul_nonneg ha h1.le) (mul_pos hb' h2)

/-! ### The Koebe generator -/

/-- `Re ((1 + w)/(1 - w)) > 0` for `|w| < 1`. -/
lemma re_cayley_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < ((1 + w) / (1 - w)).re := by
  have h1 : 1 - w ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hw
    exact lt_irrefl _ hw
  have hN : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr h1
  have hw2 : w.re * w.re + w.im * w.im < 1 := by
    have e : Complex.normSq w = ‖w‖ ^ 2 := Complex.normSq_eq_norm_sq w
    rw [Complex.normSq_apply] at e
    nlinarith [norm_nonneg w]
  rw [Complex.div_re, ← add_div]
  apply div_pos _ hN
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    Complex.sub_im]
  nlinarith

lemma norm_inner_lt_one {u z : E} (hu : ‖u‖ ≤ 1) (hz : z ∈ unitBall E) : ‖⟪u, z⟫_ℂ‖ < 1 := by
  rw [mem_unitBall] at hz
  calc ‖⟪u, z⟫_ℂ‖ ≤ ‖u‖ * ‖z‖ := norm_inner_le_norm u z
    _ ≤ 1 * ‖z‖ := by gcongr
    _ < 1 := by linarith

lemma one_sub_inner_ne_zero {u z : E} (hu : ‖u‖ ≤ 1) (hz : z ∈ unitBall E) :
    1 - ⟪u, z⟫_ℂ ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  have := norm_inner_lt_one hu hz
  rw [← h, norm_one] at this
  exact lt_irrefl _ this

/-- The *Koebe generator* `h(z) = (1 + ⟨z, u⟩)/(1 - ⟨z, u⟩) · z`. For a unit vector `u` it is the
infinitesimal generator of the starlike map `z / (1 + ⟨z, u⟩)²`, the extremal map for the
coefficient problems in the direction `u`. -/
def koebeGen (u : E) (z : E) : E :=
  ((1 + ⟪u, z⟫_ℂ) / (1 - ⟪u, z⟫_ℂ)) • z

/-- The Koebe generator satisfies the Carathéodory condition (for `‖u‖ ≤ 1`). -/
theorem isCaratheodory_koebeGen {u : E} (hu : ‖u‖ ≤ 1) : IsCaratheodory (koebeGen u) := by
  set c : E → ℂ := fun z => (1 + ⟪u, z⟫_ℂ) / (1 - ⟪u, z⟫_ℂ) with hc_def
  have hc : ∀ z ∈ unitBall E, DifferentiableAt ℂ c z := by
    intro z hz
    have hl : DifferentiableAt ℂ (fun z => innerSL ℂ u z) z := (innerSL ℂ u).differentiableAt
    simp only [innerSL_apply_apply] at hl
    have h1 : DifferentiableAt ℂ (fun z => (1 + ⟪u, z⟫_ℂ) * (1 - ⟪u, z⟫_ℂ)⁻¹) z :=
      ((differentiableAt_const _).fun_add hl).fun_mul
        (((differentiableAt_const _).fun_sub hl).fun_inv (one_sub_inner_ne_zero hu hz))
    rw [hc_def]
    simpa only [div_eq_mul_inv] using h1
  have hk : koebeGen u = fun z => c z • z := rfl
  refine ⟨⟨fun z hz => ((hc z hz).fun_smul differentiableAt_fun_id).differentiableWithinAt,
    by simp [koebeGen], ?_⟩, ?_⟩
  · rw [hk, fderiv_fun_smul (hc 0 zero_mem_unitBall) differentiableAt_fun_id, fderiv_fun_id]
    ext x
    simp [hc_def]
  · intro z hz hz0
    show 0 < (⟪z, c z • z⟫_ℂ).re
    rw [inner_smul_right, Complex.mul_re, re_inner_self, im_inner_self, mul_zero, sub_zero]
    exact mul_pos (re_cayley_pos (norm_inner_lt_one hu hz)) (pow_pos (norm_pos_iff.mpr hz0) 2)

/-- The Koebe generator belongs to the Carathéodory class `M(𝔹)` (for `‖u‖ ≤ 1`). -/
theorem koebeGen_mem_classM {u : E} (hu : ‖u‖ ≤ 1) : koebeGen u ∈ classM E :=
  isCaratheodory_koebeGen hu

/-! ### A Loewner chain: `f(z, t) = eᵗ z` -/

/-- `f(z, t) = eᵗ z` is a Loewner chain. -/
theorem isLoewnerChain_exp_smul :
    IsLoewnerChain (fun t (z : E) => (Real.exp t : ℂ) • z) where
  differentiableOn t _ := differentiableOn_id.fun_const_smul _
  injOn t _ := fun x _ y _ hxy =>
    smul_right_injective E (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne') hxy
  map_zero t _ := smul_zero _
  fderiv_zero t _ := ((hasFDerivAt_id (0 : E)).fun_const_smul (Real.exp t : ℂ)).fderiv
  image_subset s t _ hst := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨(Real.exp (s - t) : ℂ) • z, ?_, ?_⟩
    · rw [mem_unitBall] at hz ⊢
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have : Real.exp (s - t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      calc Real.exp (s - t) * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
        _ < 1 := by simpa using hz
    · simp only
      rw [smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, add_sub_cancel]

/-- The identity map belongs to `classS0'` (via the chain `f(z, t) = eᵗ z`). -/
theorem id_mem_classS0' : (id : E → E) ∈ classS0' E := by
  refine ⟨fun t z => (Real.exp t : ℂ) • z, isLoewnerChain_exp_smul, ?_, ?_⟩
  · intro z _
    simp
  · intro r _
    refine ⟨r, fun t _ z hz => ?_⟩
    simp only
    rw [smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      Complex.ofReal_one, one_smul]
    exact hz

end LoewnerS0
