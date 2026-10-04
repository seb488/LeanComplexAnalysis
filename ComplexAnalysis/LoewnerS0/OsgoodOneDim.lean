import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Osgood's theorem in one variable

An injective holomorphic function of one complex variable has nonvanishing derivative
(`LoewnerS0.deriv_ne_zero_of_injOn`).

Proof: if `φ'(a) = 0`, then `φ(z) - φ(a) = (z - a)^k g(z)` near `a` with `k ≥ 2` and `g(a) ≠ 0`.
Near `a`, `g = h^k` for a holomorphic `h` (a branch of `exp (log g / k)`), so `φ - φ(a) = ρ^k` with
`ρ(z) = (z - a) h(z)`. As `ρ'(a) = h(a) ≠ 0`, `ρ` maps neighbourhoods of `a` onto neighbourhoods of
`0`; if `ρ(z₁) = t` and `ρ(z₂) = ω t` with `ω = e^{2πi/k} ≠ 1`, then `φ(z₁) = φ(z₂)`, `z₁ ≠ z₂`.
-/

open Complex Metric Set Filter
open scoped Topology Real

noncomputable section

namespace LoewnerS0

/-- A holomorphic `k`-th root of a function that does not vanish at `a`. -/
lemma exists_pow_eq_of_ne_zero {g : ℂ → ℂ} {a : ℂ} (hg : AnalyticAt ℂ g a) (hga : g a ≠ 0)
    {k : ℕ} (hk : k ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧ h a ≠ 0 ∧ ∀ᶠ z in 𝓝 a, h z ^ k = g z := by
  set c : ℂ := g a ^ ((k : ℂ)⁻¹) with hc
  have hck : c ^ k = g a := Complex.cpow_nat_inv_pow _ hk
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow hk] at hck
    exact hga hck.symm
  -- `g z / g a` stays in the slit plane near `a`
  have hcont : ContinuousAt (fun z => g z / g a) a := hg.continuousAt.div_const _
  have hslit : ∀ᶠ z in 𝓝 a, g z / g a ∈ slitPlane := by
    have h1 : g a / g a ∈ slitPlane := by rw [div_self hga]; exact one_mem_slitPlane
    exact hcont.eventually (isOpen_slitPlane.mem_nhds h1)
  refine ⟨fun z => c * exp (log (g z / g a) / k), ?_, ?_, ?_⟩
  · have hq : AnalyticAt ℂ (fun z => g z / g a) a := hg.div_const
    have hlog : AnalyticAt ℂ (fun z => log (g z / g a)) a :=
      hq.clog (by rw [div_self hga]; exact one_mem_slitPlane)
    exact analyticAt_const.mul ((hlog.div_const).cexp)
  · simp only [div_self hga, log_one, zero_div, exp_zero, mul_one]
    exact hc0
  · filter_upwards [hslit] with z hz
    have hz0 : g z / g a ≠ 0 := slitPlane_ne_zero hz
    rw [mul_pow, ← exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hk), exp_log hz0, hck,
      mul_div_cancel₀ _ hga]

/-- **Osgood's theorem in one variable**: an injective holomorphic function on an open set has
nonvanishing derivative. -/
theorem deriv_ne_zero_of_injOn {φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) {a : ℂ} (ha : a ∈ U) : deriv φ a ≠ 0 := by
  intro hd
  have hUa : U ∈ 𝓝 a := hU.mem_nhds ha
  have han : AnalyticAt ℂ φ a := hφ.analyticAt hUa
  have hψ : AnalyticAt ℂ (fun z => φ z - φ a) a := han.sub analyticAt_const
  -- `φ` is not constant near `a`
  have hne : ¬∀ᶠ z in 𝓝 a, φ z - φ a = 0 := by
    intro h0
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (h0.and hUa)
    have h1 : a + (ε / 2 : ℝ) ∈ ball a ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have h2 := hεU h1
    have h3 := hεU (mem_ball_self hε)
    have heq : φ (a + (ε / 2 : ℝ)) = φ a := sub_eq_zero.mp h2.1
    have := hinj h2.2 h3.2 heq
    have h4 : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination this
    have h5 : (ε / 2 : ℝ) = 0 := by exact_mod_cast h4
    linarith
  obtain ⟨k, g, hg, hga, hfg⟩ := hψ.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  simp only [smul_eq_mul] at hfg
  -- `k ≥ 2`
  have hk0 : k ≠ 0 := by
    rintro rfl
    have := hfg.self_of_nhds
    simp only [sub_self, pow_zero, one_mul] at this
    exact hga this.symm
  have hk1 : k ≠ 1 := by
    rintro rfl
    simp only [pow_one] at hfg
    have h1 : HasDerivAt (fun z => (z - a) * g z) (g a) a := by
      have := ((hasDerivAt_id a).sub_const a).fun_mul hg.differentiableAt.hasDerivAt
      simpa using this
    have h2 : HasDerivAt (fun z => φ z - φ a) (g a) a := h1.congr_of_eventuallyEq hfg
    have h3 : HasDerivAt φ (g a) a := by
      have := h2.add_const (φ a)
      simpa using this
    exact hga (h3.deriv.symm.trans hd)
  have hk2 : 1 < k := by omega
  -- a holomorphic `k`-th root of `g`
  obtain ⟨h, hh, hha, hhk⟩ := exists_pow_eq_of_ne_zero hg hga hk0
  set ρ : ℂ → ℂ := fun z => (z - a) * h z with hρ
  have hρan : AnalyticAt ℂ ρ a := (analyticAt_id.sub analyticAt_const).mul hh
  have hρd : HasDerivAt ρ (h a) a := by
    have := ((hasDerivAt_id a).sub_const a).fun_mul hh.differentiableAt.hasDerivAt
    simpa [ρ] using this
  have hρs : HasStrictDerivAt ρ (h a) a := by
    have := hρan.hasStrictDerivAt
    rwa [hρd.deriv] at this
  have hmap := hρs.map_nhds_eq hha
  have hρa : ρ a = 0 := by simp [ρ]
  rw [hρa] at hmap
  -- the neighbourhood where `φ - φ(a) = ρ^k`
  have hW : {z | z ∈ U ∧ φ z - φ a = ρ z ^ k} ∈ 𝓝 a := by
    filter_upwards [hUa, hfg, hhk] with z hz h1 h2
    refine ⟨hz, ?_⟩
    rw [h1, ← h2, hρ, mul_pow]
  have himg : ρ '' {z | z ∈ U ∧ φ z - φ a = ρ z ^ k} ∈ 𝓝 (0 : ℂ) := by
    rw [← hmap]; exact image_mem_map hW
  obtain ⟨ε, hε, hεimg⟩ := Metric.mem_nhds_iff.mp himg
  set ω : ℂ := exp (2 * π * I / k) with hω
  have hωp : IsPrimitiveRoot ω k := Complex.isPrimitiveRoot_exp k hk0
  have hω1 : ω ≠ 1 := hωp.ne_one hk2
  have hωn : ‖ω‖ = 1 := hωp.norm'_eq_one hk0
  set t : ℂ := ((ε / 2 : ℝ) : ℂ) with ht
  have ht0 : t ≠ 0 := by
    rw [ht]
    exact_mod_cast (by positivity : (ε / 2 : ℝ) ≠ 0)
  have htn : ‖t‖ < ε := by
    rw [ht, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have h1 : t ∈ ball (0 : ℂ) ε := by rw [mem_ball_zero_iff]; exact htn
  have h2 : ω * t ∈ ball (0 : ℂ) ε := by rw [mem_ball_zero_iff, norm_mul, hωn, one_mul]; exact htn
  obtain ⟨z₁, ⟨hz₁U, hz₁⟩, hρ₁⟩ := hεimg h1
  obtain ⟨z₂, ⟨hz₂U, hz₂⟩, hρ₂⟩ := hεimg h2
  have hφeq : φ z₁ = φ z₂ := by
    have e1 : φ z₁ - φ a = t ^ k := by rw [hz₁, hρ₁]
    have e2 : φ z₂ - φ a = t ^ k := by rw [hz₂, hρ₂, mul_pow, hωp.pow_eq_one, one_mul]
    linear_combination e1 - e2
  have hz := hinj hz₁U hz₂U hφeq
  have : t = ω * t := by
    have h3 : ρ z₁ = ρ z₂ := by rw [hz]
    rwa [hρ₁, hρ₂] at h3
  have : ω = 1 := by
    have h3 : (ω - 1) * t = 0 := by linear_combination -this
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd h4 ht0
  exact hω1 this

end LoewnerS0
