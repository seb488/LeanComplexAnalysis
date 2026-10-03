import LoewnerS0.SCV
import LoewnerS0.Starlike
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The Taylor recursion for `Df · h = f`

If `f` and `h` are normalized holomorphic maps of the unit ball of a finite-dimensional complex
inner product space with `Df(z) h(z) = f(z)`, and `h(z) = z + B(z, z) + C(z, z, z) + O(‖z‖⁴)`,
then the homogeneous expansion of `f` to order three is determined by `B` and `C`:

* `D²f(0)(u, u)/2 = -B(u, u)`;
* `D³f(0)(u, u, u)/6 = (B(u, B(u, u)) + B(B(u, u), u) - C(u, u, u))/2`.

This is `LoewnerS0.taylorRecursion`, which proves the statement `TaylorRecursion E`.

The proof restricts the identity `Df · h = f` to complex lines `ζ ↦ ζ u`, expands all one-variable
functions that occur with Taylor's formula (with an `O(|ζ|^m)` remainder, from mathlib's power
series of holomorphic functions of one variable) and compares the coefficients of `ζ²` and `ζ³`.
The regularity of `f` comes from `DifferentiableOn.contDiffOn_of_isOpen` (holomorphic maps are
`C^∞`); the symmetry of `D²f(0)` and polarization finish the computation.
-/

open Complex Metric Set Filter Asymptotics
open scoped Topology InnerProductSpace

noncomputable section

namespace LoewnerS0

section OneVariable

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Taylor's formula** with remainder `O(|ζ|^m)` for a holomorphic function of one variable. -/
theorem exists_taylor_bound [CompleteSpace F] {φ : ℂ → F} {U : Set ℂ} (hφ : DifferentiableOn ℂ φ U)
    (hU : U ∈ 𝓝 0) (m : ℕ) : ∃ C ε, 0 < ε ∧ ∀ ζ : ℂ, ‖ζ‖ < ε →
      ‖φ ζ - ∑ k ∈ Finset.range m, ((k.factorial : ℂ)⁻¹ * ζ ^ k) • iteratedDeriv k φ 0‖ ≤
        C * ‖ζ‖ ^ m := by
  obtain ⟨p, r, hp⟩ := hφ.analyticAt hU
  have h2 : ∀ ζ : ℂ, p.partialSum m ζ =
      ∑ k ∈ Finset.range m, ((k.factorial : ℂ)⁻¹ * ζ ^ k) • iteratedDeriv k φ 0 := by
    intro ζ
    unfold FormalMultilinearSeries.partialSum
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have := hp.factorial_smul ζ k
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ] at this
    rw [mul_smul, ← this, smul_smul, inv_mul_cancel₀ hk, one_smul]
  have h1 := hp.hasFPowerSeriesAt.isBigO_sub_partialSum_pow m
  simp only [zero_add, h2] at h1
  obtain ⟨C, hC⟩ := h1.bound
  obtain ⟨ε, hε, hεC⟩ := Metric.eventually_nhds_iff.mp hC
  refine ⟨C, ε, hε, fun ζ hζ => ?_⟩
  have := hεC (show dist ζ 0 < ε by simpa using hζ)
  simpa using this

/-- The first four terms of the Taylor polynomial. -/
lemma taylor_sum_four (φ : ℂ → F) (ζ : ℂ) :
    ∑ k ∈ Finset.range 4, ((k.factorial : ℂ)⁻¹ * ζ ^ k) • iteratedDeriv k φ 0 =
      φ 0 + ζ • iteratedDeriv 1 φ 0 + ((2 : ℂ)⁻¹ * ζ ^ 2) • iteratedDeriv 2 φ 0 +
        ((6 : ℂ)⁻¹ * ζ ^ 3) • iteratedDeriv 3 φ 0 := by
  simp [Finset.sum_range_succ, Nat.factorial]

lemma taylor_sum_three (φ : ℂ → F) (ζ : ℂ) :
    ∑ k ∈ Finset.range 3, ((k.factorial : ℂ)⁻¹ * ζ ^ k) • iteratedDeriv k φ 0 =
      φ 0 + ζ • iteratedDeriv 1 φ 0 + ((2 : ℂ)⁻¹ * ζ ^ 2) • iteratedDeriv 2 φ 0 := by
  simp [Finset.sum_range_succ, Nat.factorial]

lemma taylor_sum_two (φ : ℂ → F) (ζ : ℂ) :
    ∑ k ∈ Finset.range 2, ((k.factorial : ℂ)⁻¹ * ζ ^ k) • iteratedDeriv k φ 0 =
      φ 0 + ζ • iteratedDeriv 1 φ 0 := by
  simp [Finset.sum_range_succ]

lemma taylor_sum_one (φ : ℂ → F) (ζ : ℂ) :
    ∑ k ∈ Finset.range 1, ((k.factorial : ℂ)⁻¹ * ζ ^ k) • iteratedDeriv k φ 0 = φ 0 := by
  simp

/-- If `ζ² v₂ + ζ³ v₃ = O(|ζ|⁴)` near `0`, then `v₂ = v₃ = 0`. -/
lemma coeff_eq_zero_of_bound {v₂ v₃ : F} {C ε : ℝ} (hε : 0 < ε)
    (h : ∀ ζ : ℂ, ‖ζ‖ < ε → ‖ζ ^ 2 • v₂ + ζ ^ 3 • v₃‖ ≤ C * ‖ζ‖ ^ 4) : v₂ = 0 ∧ v₃ = 0 := by
  have key : ∀ t : ℝ, 0 < t → t < ε →
      ‖((t : ℂ)) ^ 2 • v₂ + ((t : ℂ)) ^ 3 • v₃‖ ≤ C * t ^ 4 := by
    intro t ht htε
    have := h (t : ℂ) (by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht])
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at this
  have e2 : ∀ t : ℝ, 0 < t → ‖((t : ℂ)) ^ 2 • v₂‖ = t ^ 2 * ‖v₂‖ := fun t ht => by
    rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have e3 : ∀ t : ℝ, 0 < t → ‖((t : ℂ)) ^ 3 • v₃‖ = t ^ 3 * ‖v₃‖ := fun t ht => by
    rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hv₂ : v₂ = 0 := by
    have hlim : Tendsto (fun t : ℝ => C * t ^ 2 + t * ‖v₃‖) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun t : ℝ => C * t ^ 2 + t * ‖v₃‖) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖v₂‖ ≤ C * t ^ 2 + t * ‖v₃‖ := by
      filter_upwards [Ioo_mem_nhdsGT hε] with t ht
      have h1 := key t ht.1 ht.2
      have h2 : t ^ 2 * ‖v₂‖ ≤ C * t ^ 4 + t ^ 3 * ‖v₃‖ := by
        rw [← e2 t ht.1, ← e3 t ht.1]
        calc ‖((t : ℂ)) ^ 2 • v₂‖
            = ‖(((t : ℂ)) ^ 2 • v₂ + ((t : ℂ)) ^ 3 • v₃) - ((t : ℂ)) ^ 3 • v₃‖ := by
              rw [add_sub_cancel_right]
          _ ≤ ‖((t : ℂ)) ^ 2 • v₂ + ((t : ℂ)) ^ 3 • v₃‖ + ‖((t : ℂ)) ^ 3 • v₃‖ :=
              norm_sub_le _ _
          _ ≤ C * t ^ 4 + ‖((t : ℂ)) ^ 3 • v₃‖ := by linarith
      have ht2 : 0 < t ^ 2 := by have := ht.1; positivity
      have h3 : t ^ 2 * ‖v₂‖ ≤ t ^ 2 * (C * t ^ 2 + t * ‖v₃‖) := by
        calc t ^ 2 * ‖v₂‖ ≤ C * t ^ 4 + t ^ 3 * ‖v₃‖ := h2
          _ = t ^ 2 * (C * t ^ 2 + t * ‖v₃‖) := by ring
      exact le_of_mul_le_mul_left h3 ht2
    exact norm_le_zero_iff.mp (ge_of_tendsto hlim hev)
  refine ⟨hv₂, ?_⟩
  have hlim : Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => C * t) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖v₃‖ ≤ C * t := by
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    have h1 := key t ht.1 ht.2
    rw [hv₂, smul_zero, zero_add, e3 t ht.1] at h1
    have ht3 : 0 < t ^ 3 := by have := ht.1; positivity
    have h3 : t ^ 3 * ‖v₃‖ ≤ t ^ 3 * (C * t) := by
      calc t ^ 3 * ‖v₃‖ ≤ C * t ^ 4 := h1
        _ = t ^ 3 * (C * t) := by ring
    exact le_of_mul_le_mul_left h3 ht3
  exact norm_le_zero_iff.mp (ge_of_tendsto hlim hev)

end OneVariable

section Multilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma bilin_smul (B : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => E) E) (ζ : ℂ) (u : E) :
    B ![ζ • u, ζ • u] = ζ ^ 2 • B ![u, u] := by
  have e : (![ζ • u, ζ • u] : Fin 2 → E) = fun i => ζ • (![u, u] : Fin 2 → E) i := by
    funext i; fin_cases i <;> rfl
  rw [e, B.map_smul_univ]
  simp [Finset.prod_const]

lemma trilin_smul (C : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E) (ζ : ℂ) (u : E) :
    C ![ζ • u, ζ • u, ζ • u] = ζ ^ 3 • C ![u, u, u] := by
  have e : (![ζ • u, ζ • u, ζ • u] : Fin 3 → E) = fun i => ζ • (![u, u, u] : Fin 3 → E) i := by
    funext i; fin_cases i <;> rfl
  rw [e, C.map_smul_univ]
  simp [Finset.prod_const]

lemma bilin_add_left (B : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => E) E) (x y z : E) :
    B ![x + y, z] = B ![x, z] + B ![y, z] := by
  have h := B.map_update_add ![x, z] 0 x y
  have e1 : Function.update (![x, z] : Fin 2 → E) 0 (x + y) = ![x + y, z] := by
    funext i; fin_cases i <;> simp
  have e2 : Function.update (![x, z] : Fin 2 → E) 0 x = ![x, z] := by
    funext i; fin_cases i <;> simp
  have e3 : Function.update (![x, z] : Fin 2 → E) 0 y = ![y, z] := by
    funext i; fin_cases i <;> simp
  rw [e1, e2, e3] at h
  exact h

lemma bilin_add_right (B : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => E) E) (x y z : E) :
    B ![x, y + z] = B ![x, y] + B ![x, z] := by
  have h := B.map_update_add ![x, y] 1 y z
  have e1 : Function.update (![x, y] : Fin 2 → E) 1 (y + z) = ![x, y + z] := by
    funext i; fin_cases i <;> simp
  have e2 : Function.update (![x, y] : Fin 2 → E) 1 y = ![x, y] := by
    funext i; fin_cases i <;> simp
  have e3 : Function.update (![x, y] : Fin 2 → E) 1 z = ![x, z] := by
    funext i; fin_cases i <;> simp
  rw [e1, e2, e3] at h
  exact h

end Multilinear

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Comparison of the coefficients of `ζ²` and `ζ³` in `Df(ζu) h(ζu) = f(ζu)`. -/
theorem taylor_coeff_identities {f h : E → E}
    {B : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => E) E}
    {C : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E} {K δ : ℝ}
    (hf : IsNormalized f) (hfh : ∀ z ∈ unitBall E, fderiv ℂ f z (h z) = f z) (hδ : 0 < δ)
    (hrem : ∀ z : E, ‖z‖ < δ → ‖h z - z - B ![z, z] - C ![z, z, z]‖ ≤ K * ‖z‖ ^ 4) (u : E) :
    (2 : ℂ)⁻¹ • iteratedFDeriv ℂ 2 f 0 (fun _ => u) + B ![u, u] = 0 ∧
      (3 : ℂ)⁻¹ • iteratedFDeriv ℂ 3 f 0 (fun _ => u) + fderiv ℂ (fderiv ℂ f) 0 u (B ![u, u]) +
        C ![u, u, u] = 0 := by
  have hC4 : ContDiffOn ℂ 4 f (unitBall E) :=
    hf.differentiableOn.contDiffOn_of_isOpen isOpen_unitBall 4
  obtain ⟨L, hL⟩ : ∃ L : ℂ →L[ℂ] E, ∀ ζ : ℂ, L ζ = ζ • u :=
    ⟨ContinuousLinearMap.toSpanSingleton ℂ u, fun ζ => ContinuousLinearMap.toSpanSingleton_apply _ _ _⟩
  have hL0 : L 0 = 0 := map_zero L
  have hL1 : L 1 = u := by rw [hL, one_smul]
  have hWo : IsOpen (L ⁻¹' unitBall E) := isOpen_unitBall.preimage L.continuous
  have h0W : (0 : ℂ) ∈ L ⁻¹' unitBall E := by simp [hL0]
  have hWn : L ⁻¹' unitBall E ∈ 𝓝 (0 : ℂ) := hWo.mem_nhds h0W
  -- the restriction of `f` to the line `ℂ u`
  have hgd : DifferentiableOn ℂ (f ∘ L) (L ⁻¹' unitBall E) :=
    hf.differentiableOn.comp L.differentiableOn fun ζ hζ => hζ
  have hiter : ∀ k : ℕ, k ≤ 4 →
      iteratedDeriv k (f ∘ L) 0 = iteratedFDeriv ℂ k f 0 (fun _ => u) := by
    intro k hk
    have h1 := L.iteratedFDerivWithin_comp_right hC4 isOpen_unitBall.uniqueDiffOn
      hWo.uniqueDiffOn (x := 0) (by simp [hL0]) (i := k) (by exact_mod_cast hk)
    rw [iteratedFDerivWithin_of_isOpen k hWo h0W, hL0,
      iteratedFDerivWithin_of_isOpen k isOpen_unitBall zero_mem_unitBall] at h1
    rw [iteratedDeriv_eq_iteratedFDeriv, h1]
    simp [hL1]
  have hderivg : ∀ ζ ∈ L ⁻¹' unitBall E, deriv (f ∘ L) ζ = fderiv ℂ f (L ζ) u := by
    intro ζ hζ
    have hfd : DifferentiableAt ℂ f (L ζ) := hf.differentiableAt hζ
    have := hfd.hasFDerivAt.comp_hasDerivAt ζ L.hasFDerivAt.hasDerivAt
    rw [this.deriv, hL1]
  -- the functions `ζ ↦ Df(ζ u) w`
  have hkd : ∀ w : E, DifferentiableOn ℂ (fun ζ => fderiv ℂ f (L ζ) w) (L ⁻¹' unitBall E) :=
    fun w => (hf.differentiableOn.differentiableOn_fderiv_apply isOpen_unitBall w).comp
      L.differentiableOn fun ζ hζ => hζ
  have hk0 : ∀ w : E, fderiv ℂ f (L 0) w = w := fun w => by rw [hL0, hf.fderiv_zero]; rfl
  have hDf : DifferentiableAt ℂ (fderiv ℂ f) 0 :=
    ((hC4.contDiffAt (unitBall_mem_nhds zero_mem_unitBall)).fderiv_right
      (m := 3) (by norm_num)).differentiableAt (by norm_num)
  have hkderiv : ∀ w : E, deriv (fun ζ => fderiv ℂ f (L ζ) w) 0 = fderiv ℂ (fderiv ℂ f) 0 u w := by
    intro w
    have h1 := hDf.hasFDerivAt.clm_apply (hasFDerivAt_const w (0 : E))
    have h2 : HasDerivAt (fun ζ => fderiv ℂ f (L ζ) w) _ 0 :=
      h1.comp_hasDerivAt_of_eq (0 : ℂ) L.hasFDerivAt.hasDerivAt hL0.symm
    rw [h2.deriv, hL1]
    simp
  -- a bound for `Df(ζ u)` near `0`
  have hA0 : ContinuousAt (fderiv ℂ f) 0 :=
    (hC4.continuousOn_fderiv_of_isOpen isOpen_unitBall (by norm_num)).continuousAt
      (unitBall_mem_nhds zero_mem_unitBall)
  have hAc : ContinuousAt (fun ζ => fderiv ℂ f (L ζ)) 0 :=
    hA0.comp_of_eq L.continuous.continuousAt hL0
  obtain ⟨εA, hεA, hA⟩ := Metric.continuousAt_iff.mp hAc 1 one_pos
  set MA := ‖fderiv ℂ f (L 0)‖ + 1 with hMA
  have hMA0 : 0 ≤ MA := by positivity
  have hAbound : ∀ ζ : ℂ, ‖ζ‖ < εA → ‖fderiv ℂ f (L ζ)‖ ≤ MA := by
    intro ζ hζ
    have := hA (show dist ζ 0 < εA by simpa using hζ)
    rw [dist_eq_norm] at this
    calc ‖fderiv ℂ f (L ζ)‖ = ‖(fderiv ℂ f (L ζ) - fderiv ℂ f (L 0)) + fderiv ℂ f (L 0)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖fderiv ℂ f (L ζ) - fderiv ℂ f (L 0)‖ + ‖fderiv ℂ f (L 0)‖ := norm_add_le _ _
      _ ≤ MA := by rw [hMA]; linarith
  -- Taylor expansions
  obtain ⟨C₄, ε₄, hε₄, hT₄⟩ := exists_taylor_bound hgd hWn 4
  obtain ⟨C₃, ε₃, hε₃, hT₃⟩ := exists_taylor_bound (hgd.deriv hWo) hWn 3
  obtain ⟨C₂, ε₂, hε₂, hT₂⟩ := exists_taylor_bound (hkd (B ![u, u])) hWn 2
  obtain ⟨C₁, ε₁, hε₁, hT₁⟩ := exists_taylor_bound (hkd (C ![u, u, u])) hWn 1
  simp only [taylor_sum_four, taylor_sum_three, taylor_sum_two, taylor_sum_one] at hT₄ hT₃ hT₂ hT₁
  have hI0 : deriv (f ∘ L) 0 = u := by rw [hderivg 0 h0W, hk0]
  have hI1 : iteratedDeriv 1 (deriv (f ∘ L)) 0 = iteratedFDeriv ℂ 2 f 0 (fun _ => u) := by
    rw [← iteratedDeriv_succ']; exact hiter 2 (by norm_num)
  have hI2 : iteratedDeriv 2 (deriv (f ∘ L)) 0 = iteratedFDeriv ℂ 3 f 0 (fun _ => u) := by
    rw [← iteratedDeriv_succ']; exact hiter 3 (by norm_num)
  rw [hI0, hI1, hI2] at hT₃
  rw [hiter 1 (by norm_num), hiter 2 (by norm_num), hiter 3 (by norm_num)] at hT₄
  rw [iteratedDeriv_one, hkderiv, hk0] at hT₂
  rw [hk0] at hT₁
  have hG0 : (f ∘ L) 0 = 0 := by simp [hL0, hf.map_zero]
  have hG1 : iteratedFDeriv ℂ 1 f 0 (fun _ => u) = u := by simp [hf.fderiv_zero]
  rw [hG0, hG1] at hT₄
  -- the radius
  set εW := min 1 δ / (‖u‖ + 1) with hεW
  have hεW0 : 0 < εW := by positivity
  set ε₀ := min (min (min ε₄ ε₃) (min ε₂ ε₁)) (min εA εW) with hε₀
  have hε₀0 : 0 < ε₀ := by
    simp only [hε₀, lt_min_iff]; exact ⟨⟨⟨hε₄, hε₃⟩, hε₂, hε₁⟩, hεA, hεW0⟩
  have hsmall : ∀ ζ : ℂ, ‖ζ‖ < ε₀ → ‖ζ‖ < ε₄ ∧ ‖ζ‖ < ε₃ ∧ ‖ζ‖ < ε₂ ∧ ‖ζ‖ < ε₁ ∧ ‖ζ‖ < εA ∧
      ‖ζ‖ < εW := by
    intro ζ hζ
    simp only [hε₀, lt_min_iff] at hζ
    exact ⟨hζ.1.1.1, hζ.1.1.2, hζ.1.2.1, hζ.1.2.2, hζ.2.1, hζ.2.2⟩
  set b := B ![u, u] with hb
  set c := C ![u, u, u] with hc
  set G2 := iteratedFDeriv ℂ 2 f 0 (fun _ => u) with hG2
  set G3 := iteratedFDeriv ℂ 3 f 0 (fun _ => u) with hG3
  set β := fderiv ℂ (fderiv ℂ f) 0 u b with hβ
  apply coeff_eq_zero_of_bound hε₀0 (C := C₃ + C₂ + C₁ + MA * K * ‖u‖ ^ 4 + C₄)
  intro ζ hζ
  obtain ⟨h₄, h₃, h₂, h₁, hA', hW'⟩ := hsmall ζ hζ
  -- the point `z = ζ u`
  have hz : ‖L ζ‖ < min 1 δ := by
    rw [hL, norm_smul]
    have hu1 : ‖u‖ < ‖u‖ + 1 := by linarith
    calc ‖ζ‖ * ‖u‖ ≤ ‖ζ‖ * (‖u‖ + 1) := by gcongr
      _ < εW * (‖u‖ + 1) := by gcongr
      _ = min 1 δ := by rw [hεW]; field_simp
  have hz1 : L ζ ∈ unitBall E := by
    rw [mem_unitBall]; exact lt_of_lt_of_le hz (min_le_left _ _)
  have hzδ : ‖L ζ‖ < δ := lt_of_lt_of_le hz (min_le_right _ _)
  -- the identity `Df(z) h(z) = f(z)` along the line
  set ρ := h (L ζ) - L ζ - B ![L ζ, L ζ] - C ![L ζ, L ζ, L ζ] with hρ
  have hρb : ‖ρ‖ ≤ K * ‖L ζ‖ ^ 4 := hrem (L ζ) hzδ
  have hhz : h (L ζ) = ζ • u + ζ ^ 2 • b + ζ ^ 3 • c + ρ := by
    rw [hρ, hL, bilin_smul, trilin_smul]; abel
  have hid : ζ • deriv (f ∘ L) ζ + ζ ^ 2 • fderiv ℂ f (L ζ) b + ζ ^ 3 • fderiv ℂ f (L ζ) c +
      fderiv ℂ f (L ζ) ρ = (f ∘ L) ζ := by
    rw [hderivg ζ hz1, Function.comp_apply, ← hfh (L ζ) hz1, hhz]
    simp only [map_add, map_smul]
  -- the polynomial part is a combination of the remainders
  have hpoly : ζ ^ 2 • ((2 : ℂ)⁻¹ • G2 + b) + ζ ^ 3 • ((3 : ℂ)⁻¹ • G3 + β + c) =
      -(ζ • (deriv (f ∘ L) ζ - (u + ζ • G2 + ((2 : ℂ)⁻¹ * ζ ^ 2) • G3)) +
        ζ ^ 2 • (fderiv ℂ f (L ζ) b - (b + ζ • β)) + ζ ^ 3 • (fderiv ℂ f (L ζ) c - c) +
        fderiv ℂ f (L ζ) ρ -
        ((f ∘ L) ζ - (0 + ζ • u + ((2 : ℂ)⁻¹ * ζ ^ 2) • G2 + ((6 : ℂ)⁻¹ * ζ ^ 3) • G3))) := by
    linear_combination (norm := module) hid
  rw [hpoly, norm_neg]
  have e1 : ‖ζ • (deriv (f ∘ L) ζ - (u + ζ • G2 + ((2 : ℂ)⁻¹ * ζ ^ 2) • G3))‖ ≤
      ‖ζ‖ * (C₃ * ‖ζ‖ ^ 3) := by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hT₃ ζ h₃) (norm_nonneg _)
  have e2 : ‖ζ ^ 2 • (fderiv ℂ f (L ζ) b - (b + ζ • β))‖ ≤ ‖ζ‖ ^ 2 * (C₂ * ‖ζ‖ ^ 2) := by
    rw [norm_smul, norm_pow]; exact mul_le_mul_of_nonneg_left (hT₂ ζ h₂) (by positivity)
  have e3 : ‖ζ ^ 3 • (fderiv ℂ f (L ζ) c - c)‖ ≤ ‖ζ‖ ^ 3 * (C₁ * ‖ζ‖ ^ 1) := by
    rw [norm_smul, norm_pow]; exact mul_le_mul_of_nonneg_left (hT₁ ζ h₁) (by positivity)
  have e4 : ‖fderiv ℂ f (L ζ) ρ‖ ≤ MA * (K * (‖ζ‖ ^ 4 * ‖u‖ ^ 4)) := by
    calc ‖fderiv ℂ f (L ζ) ρ‖ ≤ ‖fderiv ℂ f (L ζ)‖ * ‖ρ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ MA * ‖ρ‖ := mul_le_mul_of_nonneg_right (hAbound ζ hA') (norm_nonneg _)
      _ ≤ MA * (K * ‖L ζ‖ ^ 4) := mul_le_mul_of_nonneg_left hρb hMA0
      _ = MA * (K * (‖ζ‖ ^ 4 * ‖u‖ ^ 4)) := by rw [hL, norm_smul, mul_pow]
  have e5 := hT₄ ζ h₄
  calc _ ≤ ‖ζ • (deriv (f ∘ L) ζ - (u + ζ • G2 + ((2 : ℂ)⁻¹ * ζ ^ 2) • G3))‖ +
        ‖ζ ^ 2 • (fderiv ℂ f (L ζ) b - (b + ζ • β))‖ + ‖ζ ^ 3 • (fderiv ℂ f (L ζ) c - c)‖ +
        ‖fderiv ℂ f (L ζ) ρ‖ +
        ‖(f ∘ L) ζ - (0 + ζ • u + ((2 : ℂ)⁻¹ * ζ ^ 2) • G2 + ((6 : ℂ)⁻¹ * ζ ^ 3) • G3)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖ζ‖ * (C₃ * ‖ζ‖ ^ 3) + ‖ζ‖ ^ 2 * (C₂ * ‖ζ‖ ^ 2) + ‖ζ‖ ^ 3 * (C₁ * ‖ζ‖ ^ 1) +
        MA * (K * (‖ζ‖ ^ 4 * ‖u‖ ^ 4)) + C₄ * ‖ζ‖ ^ 4 := by gcongr
    _ = (C₃ + C₂ + C₁ + MA * K * ‖u‖ ^ 4 + C₄) * ‖ζ‖ ^ 4 := by ring

/-- **The Taylor recursion** (Corollary 2.2 of `disproof_starlike.tex`): in finite dimension,
`Df · h = f` determines the third homogeneous term of `f` from the expansion of `h` to order 3. -/
theorem taylorRecursion : TaylorRecursion E := by
  intro f h B C K δ hf _ hfh hδ hrem u
  have hC2 : ContDiffAt ℂ 2 f 0 :=
    (hf.differentiableOn.contDiffOn_of_isOpen isOpen_unitBall 2).contDiffAt
      (unitBall_mem_nhds zero_mem_unitBall)
  have hsymm : ∀ x y, fderiv ℂ (fderiv ℂ f) 0 x y = fderiv ℂ (fderiv ℂ f) 0 y x :=
    hC2.isSymmSndFDerivAt (by simp)
  have hS : ∀ x, fderiv ℂ (fderiv ℂ f) 0 x x = -(2 : ℂ) • B ![x, x] := by
    intro x
    have h1 := (taylor_coeff_identities hf hfh hδ hrem x).1
    rw [iteratedFDeriv_two_apply] at h1
    linear_combination (norm := module) (2 : ℂ) • h1
  have hpol : fderiv ℂ (fderiv ℂ f) 0 u (B ![u, u]) = -(B ![u, B ![u, u]] + B ![B ![u, u], u]) := by
    have h1 := hS (u + B ![u, u])
    simp only [map_add, _root_.add_apply, bilin_add_left, bilin_add_right] at h1
    rw [hS u, hS (B ![u, u]), hsymm (B ![u, u]) u] at h1
    linear_combination (norm := module) (2 : ℂ)⁻¹ • h1
  have h2 := (taylor_coeff_identities hf hfh hδ hrem u).2
  rw [hpol] at h2
  linear_combination (norm := module) (2 : ℂ)⁻¹ • h2

end Main

end LoewnerS0
