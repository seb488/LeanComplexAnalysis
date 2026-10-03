import LoewnerS0.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A sphere criterion for the Carathéodory class

If `H` is holomorphic on a ball of radius `R > 1`, normalized, and `Re ⟨H(w), w⟩ ≥ c > 0` on the
unit sphere, then `H ∈ M(𝔹)`.

For a unit vector `u` the function `p(ζ) = ⟨H(ζu), u⟩/ζ` is holomorphic on a neighbourhood of the
closed unit disc (the singularity at `0` is removable), and `Re p ≥ c` on the unit circle. The
maximum modulus principle applied to `exp(-p)` gives `Re p ≥ c` on the disc, hence
`Re ⟨H(z), z⟩ = |z|² Re p(|z|) > 0` for `0 < |z| < 1`. This is Lemma 3.1 of
`disproof_starlike.tex`.
-/

open Complex Metric Set Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace LoewnerS0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Sphere criterion.** -/
theorem isCaratheodory_of_sphere {H : E → E} {R : ℝ} (hR : 1 < R)
    (hd : DifferentiableOn ℂ H (ball 0 R)) (h0 : H 0 = 0)
    (h1 : fderiv ℂ H 0 = ContinuousLinearMap.id ℂ E)
    {c : ℝ} (hc : 0 < c) (hsph : ∀ w : E, ‖w‖ = 1 → c ≤ (⟪w, H w⟫_ℂ).re) :
    IsCaratheodory H := by
  refine ⟨⟨hd.mono (ball_subset_ball hR.le), h0, h1⟩, ?_⟩
  intro z hz hz0
  set ρ : ℝ := ‖z‖ with hρdef
  have hρ : 0 < ρ := norm_pos_iff.mpr hz0
  have hρ1 : ρ < 1 := by simpa using hz
  set u : E := ((ρ : ℂ)⁻¹) • z with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
      inv_mul_cancel₀ hρ.ne']
  have hzu : z = (ρ : ℂ) • u := by
    rw [hudef, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hρ.ne'), one_smul]
  -- `q(ζ) = ⟪u, H(ζ u)⟫`
  set q : ℂ → ℂ := fun ζ => ⟪u, H (ζ • u)⟫_ℂ with hqdef
  have hmaps : MapsTo (fun ζ : ℂ => ζ • u) (ball 0 R) (ball 0 R) := by
    intro ζ hζ
    simpa [norm_smul, hu] using hζ
  have hq : DifferentiableOn ℂ q (ball 0 R) :=
    (innerSL ℂ u).differentiable.comp_differentiableOn
      (hd.comp (differentiable_id.smul_const u).differentiableOn hmaps)
  have hq0 : q 0 = 0 := by simp [hqdef, h0]
  -- `p = dslope q 0`
  set p : ℂ → ℂ := dslope q 0 with hpdef
  have hp : DifferentiableOn ℂ p (ball 0 R) :=
    (differentiableOn_dslope (ball_mem_nhds 0 (by linarith))).mpr hq
  have hp_eq : ∀ ζ : ℂ, ζ ≠ 0 → p ζ = ζ⁻¹ * q ζ := by
    intro ζ hζ
    rw [hpdef, dslope_of_ne _ hζ, slope_def_field, hq0, sub_zero, sub_zero, div_eq_inv_mul]
  -- `Re p ≥ c` on the unit circle
  have hcircle : ∀ ζ ∈ sphere (0 : ℂ) 1, c ≤ (p ζ).re := by
    intro ζ hζ
    have hζ1 : ‖ζ‖ = 1 := by simpa using hζ
    have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ1
    have hinv : ζ⁻¹ = starRingEnd ℂ ζ := by
      have hn : normSq ζ = 1 := by rw [Complex.normSq_eq_norm_sq, hζ1, one_pow]
      rw [Complex.inv_def, hn]
      simp
    have hin : ⟪ζ • u, H (ζ • u)⟫_ℂ = starRingEnd ℂ ζ * q ζ := by
      rw [inner_smul_left]
    have hn : ‖ζ • u‖ = 1 := by rw [norm_smul, hu, hζ1, one_mul]
    have := hsph (ζ • u) hn
    rw [hin] at this
    rw [hp_eq ζ hζ0, hinv]
    exact this
  -- maximum modulus principle for `exp (-p)`
  have hg : DiffContOnCl ℂ (fun ζ => cexp (-p ζ)) (ball 0 1) :=
    (hp.neg.cexp).diffContOnCl_ball (closedBall_subset_ball hR)
  have hmax : ∀ ζ ∈ closure (ball (0 : ℂ) 1), ‖cexp (-p ζ)‖ ≤ Real.exp (-c) := fun ζ hζ =>
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg (fun ζ hζ => by
      rw [frontier_ball 0 one_ne_zero] at hζ
      rw [Complex.norm_exp, Complex.neg_re]
      exact Real.exp_le_exp.mpr (by linarith [hcircle ζ hζ])) hζ
  have hρmem : (ρ : ℂ) ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball 0 one_ne_zero, mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ]
    exact hρ1.le
  have hpρ : c ≤ (p ρ).re := by
    have := hmax _ hρmem
    rw [Complex.norm_exp, Complex.neg_re] at this
    linarith [Real.exp_le_exp.mp this]
  -- back to `⟪z, H z⟫`
  have hzH : ⟪z, H z⟫_ℂ = ((ρ ^ 2 : ℝ) : ℂ) * p ρ := by
    have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    rw [hp_eq _ hρ0, hzu, inner_smul_left, Complex.conj_ofReal]
    simp only [hqdef]
    push_cast
    field_simp
  rw [hzH, Complex.re_ofReal_mul]
  have : 0 < ρ ^ 2 := by positivity
  nlinarith

end LoewnerS0
