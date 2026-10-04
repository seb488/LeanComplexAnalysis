import LoewnerS0.OsgoodSlice
import LoewnerS0.SCV
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Osgood's theorem: the degenerate case

Let `f` be holomorphic and injective on an open set `U` of a complex vector space `V` of dimension
`n ≥ 2`, and assume the *dichotomy* that at every point of `U` the derivative `Df` is either `0` or
injective (this is what the slicing step `LoewnerS0.injective_fderiv_of_ne_zero` gives, by
induction on the dimension). Then `Df` vanishes nowhere (`LoewnerS0.fderiv_ne_zero_of_dichotomy`).

Proof. Let `J = det Df` (`LoewnerS0.jacDet`), a holomorphic function; by the dichotomy, `Df = 0`
exactly on the zero set `Z(J)`. If `Df(z₀) = 0`:

* `J` does not vanish identically on any ball (else `f` would be constant there);
* among the zeros of `J` near `z₀`, choose one, `p`, with minimal *order along lines*: some
  `m`-th derivative `∂_v^m J(p) ≠ 0`, while `∂_w^j J(q) = 0` for all `j < m`, all `w` and all zeros
  `q`. Then `K = ∂_v^{m-1} J` vanishes on `Z(J)` and `∂_v K(p) ≠ 0`;
* for `x` near `p`, the function `ζ ↦ J(x + ζ v)` has a zero in a small disc (a version of
  Hurwitz's theorem, from the maximum modulus principle, `LoewnerS0.exists_zero_of_norm_lt`), and
  this zero is unique among the zeros of `ζ ↦ K(x + ζ v)` because `∂_v K ≠ 0`; moving `x` along a
  direction `w ∉ ℂ v` gives a Lipschitz curve `c` in `Z(J)` with `c(0) = p ≠ c(s₀)`
  (`LoewnerS0.exists_curve`);
* `Df = 0` on `Z(J)`, so `‖f(b) - f(a)‖ ≤ M ‖b - a‖²` for `a, b` on the curve, and `f ∘ c` is
  constant (`LoewnerS0.eq_of_norm_sub_le_mul_sq`): `f(c(s₀)) = f(p)`, contradicting injectivity.
-/

open Function Set Filter Module Metric Complex
open scoped Topology

noncomputable section

namespace LoewnerS0

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-! ### The Jacobian determinant -/

/-- The Jacobian determinant `det Df(z)`. -/
def jacDet (f : V → V) (z : V) : ℂ := LinearMap.det (fderiv ℂ f z : V →ₗ[ℂ] V)

lemma jacDet_ne_zero_iff {f : V → V} {z : V} : jacDet f z ≠ 0 ↔ Injective (fderiv ℂ f z) := by
  rw [jacDet, ← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det,
    LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  rfl

omit [FiniteDimensional ℂ V] in
lemma differentiableAt_finset_prod {ι : Type*} (s : Finset ι) {g : ι → V → ℂ} {x : V}
    (h : ∀ i ∈ s, DifferentiableAt ℂ (g i) x) :
    DifferentiableAt ℂ (fun y => ∏ i ∈ s, g i y) x := by
  classical
  exact (HasFDerivAt.finsetProd fun i hi => (h i hi).hasFDerivAt).differentiableAt

/-- The Jacobian determinant of a holomorphic map is holomorphic. -/
lemma differentiableOn_jacDet {f : V → V} {U : Set V} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : DifferentiableOn ℂ (jacDet f) U := by
  classical
  set b := Module.finBasis ℂ V with hb
  have hent : ∀ i k, DifferentiableOn ℂ (fun z => b.repr (fderiv ℂ f z (b i)) k) U := by
    intro i k
    have h1 := hf.differentiableOn_fderiv_apply hU (b i)
    exact (LinearMap.toContinuousLinearMap (b.coord k)).differentiable.comp_differentiableOn h1
  have heq : jacDet f = fun z => ∑ σ : Equiv.Perm (Fin (finrank ℂ V)),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, b.repr (fderiv ℂ f z (b i)) (σ i) := by
    funext z
    rw [jacDet, ← LinearMap.det_toMatrix b, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [LinearMap.toMatrix_apply]
    rfl
  rw [heq]
  intro z hz
  refine (DifferentiableAt.differentiableWithinAt ?_)
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  refine (differentiableAt_const _).mul (differentiableAt_finset_prod _ fun i _ => ?_)
  exact (hent i (σ i) z hz).differentiableAt (hU.mem_nhds hz)

/-! ### One-variable tools -/

/-- Derivatives along a complex line. -/
lemma iteratedDeriv_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {J : V → F} {U : Set V} (hU : IsOpen U) (hJ : DifferentiableOn ℂ J U) {q : V} (hq : q ∈ U)
    (v : V) (k : ℕ) :
    iteratedDeriv k (fun ζ : ℂ => J (q + ζ • v)) 0 = iteratedFDeriv ℂ k J q (fun _ => v) := by
  set W := (fun y => q + y) ⁻¹' U with hW
  have hWo : IsOpen W := hU.preimage (continuous_const.add continuous_id)
  have h0W : (0 : V) ∈ W := by simp [hW, hq]
  set J' : V → F := fun y => J (q + y) with hJ'
  have hJ'd : DifferentiableOn ℂ J' W :=
    hJ.comp ((differentiable_const q).add differentiable_id).differentiableOn fun y hy => hy
  have hCm : ContDiffOn ℂ k J' W := hJ'd.contDiffOn_of_isOpen hWo k
  set L : ℂ →L[ℂ] V := ContinuousLinearMap.toSpanSingleton ℂ v with hL
  have hL0 : L 0 = 0 := map_zero L
  have hL1 : L 1 = v := by simp [hL]
  have hLo : IsOpen (L ⁻¹' W) := hWo.preimage L.continuous
  have h0L : (0 : ℂ) ∈ L ⁻¹' W := by simp [hL0, h0W]
  have h1 := L.iteratedFDerivWithin_comp_right hCm hWo.uniqueDiffOn hLo.uniqueDiffOn
    (x := 0) (by simp [hL0, h0W]) (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hLo h0L, hL0, iteratedFDerivWithin_of_isOpen k hWo h0W]
    at h1
  have hfun : (fun ζ : ℂ => J (q + ζ • v)) = J' ∘ L := by
    funext ζ; simp [hJ', hL]
  rw [hfun, iteratedDeriv_eq_iteratedFDeriv, h1]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hL1, hJ',
    iteratedFDeriv_comp_add_left, add_zero]

/-- **Hurwitz's lemma** (a simple version): a function holomorphic on a closed disc with `‖g‖ ≥ c`
on the boundary circle and `‖g(0)‖ < c` has a zero in the open disc. -/
lemma exists_zero_of_norm_lt {g : ℂ → ℂ} {δ c : ℝ} (hδ : 0 < δ)
    (hg : DifferentiableOn ℂ g (closedBall 0 δ)) (hsph : ∀ ζ ∈ sphere (0 : ℂ) δ, c ≤ ‖g ζ‖)
    (h0 : ‖g 0‖ < c) : ∃ ζ ∈ ball (0 : ℂ) δ, g ζ = 0 := by
  by_contra hne
  push Not at hne
  have hc : 0 < c := (norm_nonneg _).trans_lt h0
  have hne' : ∀ ζ ∈ closedBall (0 : ℂ) δ, g ζ ≠ 0 := by
    intro ζ hζ
    rcases (mem_closedBall.mp hζ).lt_or_eq with h | h
    · exact hne ζ (mem_ball.mpr h)
    · intro h0'
      have := hsph ζ (mem_sphere.mpr h)
      rw [h0', norm_zero] at this
      linarith
  have hinv : DiffContOnCl ℂ (fun ζ => (g ζ)⁻¹) (ball (0 : ℂ) δ) := by
    have hd : DifferentiableOn ℂ (fun ζ => (g ζ)⁻¹) (closedBall 0 δ) := hg.inv hne'
    rw [← closure_ball (0 : ℂ) hδ.ne'] at hd
    exact hd.diffContOnCl
  have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hinv
    (C := c⁻¹) (fun ζ hζ => by
      rw [frontier_ball (0 : ℂ) hδ.ne'] at hζ
      rw [norm_inv]
      exact inv_anti₀ hc (hsph ζ hζ)) (subset_closure (mem_ball_self hδ))
  rw [norm_inv] at hbound
  have h1 := (inv_le_inv₀ (norm_pos_iff.mpr (hne 0 (mem_ball_self hδ))) hc).mp hbound
  linarith

/-- A map with `‖g(s) - g(s')‖ ≤ C |s - s'|²` on `[0, s₀]` is constant there. -/
lemma eq_of_norm_sub_le_mul_sq {W : Type*} [NormedAddCommGroup W] {g : ℝ → W} {s₀ C : ℝ}
    (hs₀ : 0 ≤ s₀) (hC : 0 ≤ C)
    (hg : ∀ s ∈ Icc 0 s₀, ∀ s' ∈ Icc 0 s₀, ‖g s - g s'‖ ≤ C * (s - s') ^ 2) : g s₀ = g 0 := by
  have key : ∀ N : ℕ, 0 < N → ‖g s₀ - g 0‖ ≤ C * s₀ ^ 2 / N := by
    intro N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    set t : ℕ → ℝ := fun i => s₀ * i / N with ht
    have hmem : ∀ i ≤ N, t i ∈ Icc 0 s₀ := by
      intro i hi
      refine ⟨by positivity, ?_⟩
      rw [ht, div_le_iff₀ hN']
      have : (i : ℝ) ≤ N := by exact_mod_cast hi
      nlinarith
    have hsum : g s₀ - g 0 = ∑ i ∈ Finset.range N, (g (t (i + 1)) - g (t i)) := by
      rw [Finset.sum_range_sub (fun i => g (t i))]
      simp [ht, hN'.ne']
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    have hstep : ∀ i ∈ Finset.range N, ‖g (t (i + 1)) - g (t i)‖ ≤ C * (s₀ / N) ^ 2 := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      refine (hg _ (hmem _ (by omega)) _ (hmem _ hi'.le)).trans (le_of_eq ?_)
      rw [ht]
      push_cast
      field_simp
      ring
    refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  by_contra hne
  have hpos : 0 < ‖g s₀ - g 0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (C * s₀ ^ 2 / ‖g s₀ - g 0‖)
  have hN' : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hN0 : 0 < N := by exact_mod_cast hN'
  have h1 := key N hN0
  rw [div_lt_iff₀ hpos] at hN
  rw [le_div_iff₀ hN'] at h1
  nlinarith

/-! ### The quadratic estimate -/

/-- Near a point where `Df = 0`, `f` moves quadratically: `‖f(b) - f(a)‖ ≤ M ‖b - a‖²`. -/
lemma exists_norm_sub_le_sq {f : V → V} {U : Set V} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {p : V} {η : ℝ} (hsub : closedBall p η ⊆ U) :
    ∃ M, 0 ≤ M ∧ ∀ a ∈ closedBall p η, ∀ b ∈ closedBall p η, fderiv ℂ f a = 0 →
      ‖f b - f a‖ ≤ M * ‖b - a‖ ^ 2 := by
  have : ProperSpace V := FiniteDimensional.proper ℂ V
  have hD : DifferentiableOn ℂ (fderiv ℂ f) U :=
    ((hf.contDiffOn_of_isOpen hU 2).fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn
      (by norm_num)
  have hD2 : ContinuousOn (fderiv ℂ (fderiv ℂ f)) U :=
    ((hf.contDiffOn_of_isOpen hU 3).fderiv_of_isOpen hU (m := 2) (by norm_num)).continuousOn_fderiv_of_isOpen
      hU (by norm_num)
  obtain ⟨M, hM⟩ := (isCompact_closedBall p η).exists_bound_of_continuousOn (hD2.mono hsub)
  refine ⟨max M 0, le_max_right _ _, fun a ha b hb hDa => ?_⟩
  have hDlip : ∀ x ∈ closedBall p η, ‖fderiv ℂ f x - fderiv ℂ f a‖ ≤ max M 0 * ‖x - a‖ := by
    intro x hx
    exact (convex_closedBall p η).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
      (fun y hy => hD.differentiableAt (hU.mem_nhds (hsub hy)))
      (fun y hy => (hM y hy).trans (le_max_left _ _)) ha hx
  set S := closedBall p η ∩ closedBall a ‖b - a‖ with hS
  have hSconv : Convex ℝ S := (convex_closedBall _ _).inter (convex_closedBall _ _)
  have haS : a ∈ S := ⟨ha, mem_closedBall_self (norm_nonneg _)⟩
  have hbS : b ∈ S := ⟨hb, by rw [mem_closedBall, dist_eq_norm]⟩
  have key := hSconv.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℂ) (f := f)
    (φ := fderiv ℂ f a) (C := max M 0 * ‖b - a‖)
    (fun x hx => hf.differentiableAt (hU.mem_nhds (hsub hx.1)))
    (fun x hx => (hDlip x hx.1).trans (mul_le_mul_of_nonneg_left
      (by have := hx.2; rwa [mem_closedBall, dist_eq_norm] at this) (le_max_right _ _))) haS hbS
  rw [hDa, zero_apply, sub_zero] at key
  calc ‖f b - f a‖ ≤ max M 0 * ‖b - a‖ * ‖b - a‖ := key
    _ = max M 0 * ‖b - a‖ ^ 2 := by ring

/-! ### A Lipschitz curve in the zero set -/

/-- **The curve lemma.** Let `J, K` be holomorphic on `ball p ρ` with `J(p) = 0`,
`ζ ↦ J(p + ζ v)` without zeros for `0 < |ζ| < δ₀`, `K = 0` on the zeros of `J`, and
`DK(p) v ≠ 0`. Then for `w ∉ ℂ v` there is a Lipschitz curve `c : [0, s₀] → ball p η`, `η < ρ`, of
zeros of `J`, with `c(0) = p` and `c(s₀) ≠ p`. -/
lemma exists_curve {J K : V → ℂ} {p v w : V} {ρ δ₀ : ℝ} (hρ : 0 < ρ)
    (hJ : DifferentiableOn ℂ J (ball p ρ)) (hK : DifferentiableOn ℂ K (ball p ρ)) (hJp : J p = 0)
    (hδ₀ : 0 < δ₀) (hiso : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < δ₀ → J (p + ζ • v) ≠ 0)
    (hKJ : ∀ q ∈ ball p ρ, J q = 0 → K q = 0) (hKv : fderiv ℂ K p v ≠ 0)
    (hw : w ∉ Submodule.span ℂ {v}) :
    ∃ η, 0 < η ∧ η < ρ ∧ ∃ s₀ > 0, ∃ L : ℝ, ∃ c : ℝ → V, c 0 = p ∧ c s₀ ≠ p ∧
      ∀ s ∈ Icc 0 s₀, c s ∈ ball p η ∧ J (c s) = 0 ∧
        ∀ s' ∈ Icc 0 s₀, ‖c s - c s'‖ ≤ L * |s - s'| := by
  have hpo : IsOpen (ball p ρ) := isOpen_ball
  have hpB : p ∈ ball p ρ := mem_ball_self hρ
  -- continuity of the derivatives at `p`
  have hKc : ContinuousAt (fderiv ℂ K) p :=
    ((hK.contDiffOn_of_isOpen hpo 1).continuousOn_fderiv_of_isOpen hpo le_rfl).continuousAt
      (hpo.mem_nhds hpB)
  have hJc : ContinuousAt (fderiv ℂ J) p :=
    ((hJ.contDiffOn_of_isOpen hpo 1).continuousOn_fderiv_of_isOpen hpo le_rfl).continuousAt
      (hpo.mem_nhds hpB)
  set c₀ := ‖fderiv ℂ K p v‖ with hc₀
  have hc₀0 : 0 < c₀ := norm_pos_iff.mpr hKv
  set ε := c₀ / (2 * (‖v‖ + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨η₁, hη₁, hη₁K⟩ := Metric.continuousAt_iff.mp hKc ε hε0
  obtain ⟨η₂, hη₂, hη₂J⟩ := Metric.continuousAt_iff.mp hJc 1 one_pos
  set η := min (min η₁ η₂) (ρ / 2) with hη
  have hη0 : 0 < η := lt_min (lt_min hη₁ hη₂) (half_pos hρ)
  have hηρ : η < ρ := (min_le_right _ _).trans_lt (half_lt_self hρ)
  have hball : ball p η ⊆ ball p ρ := ball_subset_ball hηρ.le
  -- derivative bounds on `ball p η`
  set LK := ‖fderiv ℂ K p‖ + ε with hLK
  set LJ := ‖fderiv ℂ J p‖ + 1 with hLJ
  have hLJ1 : 1 ≤ LJ := by rw [hLJ]; linarith [norm_nonneg (fderiv ℂ J p)]
  have hDK : ∀ y ∈ ball p η, ‖fderiv ℂ K y - fderiv ℂ K p‖ ≤ ε := by
    intro y hy
    have h1 : dist y p < η₁ :=
      lt_of_lt_of_le (mem_ball.mp hy) ((min_le_left _ _).trans (min_le_left _ _))
    have := hη₁K h1
    rw [dist_eq_norm] at this
    exact this.le
  have hDJ : ∀ y ∈ ball p η, ‖fderiv ℂ J y - fderiv ℂ J p‖ ≤ 1 := by
    intro y hy
    have h1 : dist y p < η₂ :=
      lt_of_lt_of_le (mem_ball.mp hy) ((min_le_left _ _).trans (min_le_right _ _))
    have := hη₂J h1
    rw [dist_eq_norm] at this
    exact this.le
  have hDKb : ∀ y ∈ ball p η, ‖fderiv ℂ K y‖ ≤ LK := fun y hy => by
    have := norm_le_insert' (fderiv ℂ K y) (fderiv ℂ K p)
    linarith [hDK y hy]
  have hDJb : ∀ y ∈ ball p η, ‖fderiv ℂ J y‖ ≤ LJ := fun y hy => by
    have := norm_le_insert' (fderiv ℂ J y) (fderiv ℂ J p)
    linarith [hDJ y hy]
  have hKd : ∀ y ∈ ball p η, DifferentiableAt ℂ K y := fun y hy =>
    hK.differentiableAt (hpo.mem_nhds (hball hy))
  have hJd : ∀ y ∈ ball p η, DifferentiableAt ℂ J y := fun y hy =>
    hJ.differentiableAt (hpo.mem_nhds (hball hy))
  have hKlip : ∀ y₁ ∈ ball p η, ∀ y₂ ∈ ball p η, ‖K y₁ - K y₂‖ ≤ LK * ‖y₁ - y₂‖ :=
    fun y₁ h₁ y₂ h₂ => (convex_ball p η).norm_image_sub_le_of_norm_fderiv_le hKd hDKb h₂ h₁
  have hJlip : ∀ y₁ ∈ ball p η, ∀ y₂ ∈ ball p η, ‖J y₁ - J y₂‖ ≤ LJ * ‖y₁ - y₂‖ :=
    fun y₁ h₁ y₂ h₂ => (convex_ball p η).norm_image_sub_le_of_norm_fderiv_le hJd hDJb h₂ h₁
  -- `K` is injective along `v`, quantitatively
  have hKinj : ∀ y₁ ∈ ball p η, ∀ y₂ ∈ ball p η, ∀ t : ℂ, y₁ - y₂ = t • v →
      c₀ / 2 * ‖t‖ ≤ ‖K y₁ - K y₂‖ := by
    intro y₁ h₁ y₂ h₂ t ht
    have h3 := (convex_ball p η).norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℂ) hKd hDK h₂ h₁
    rw [ht, map_smul, smul_eq_mul] at h3
    have h4 : ε * ‖t • v‖ ≤ c₀ / 2 * ‖t‖ := by
      rw [norm_smul, hε]
      have h5 : ‖v‖ / (‖v‖ + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
      calc c₀ / (2 * (‖v‖ + 1)) * (‖t‖ * ‖v‖) = c₀ / 2 * ‖t‖ * (‖v‖ / (‖v‖ + 1)) := by
            field_simp
        _ ≤ c₀ / 2 * ‖t‖ * 1 := mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = c₀ / 2 * ‖t‖ := mul_one _
    have h6 : ‖t * fderiv ℂ K p v‖ = ‖t‖ * c₀ := norm_mul _ _
    have h7 : ‖t * fderiv ℂ K p v‖ ≤ ‖K y₁ - K y₂‖ + ‖K y₁ - K y₂ - t * fderiv ℂ K p v‖ := by
      have := norm_sub_le (K y₁ - K y₂) (K y₁ - K y₂ - t * fderiv ℂ K p v)
      rwa [sub_sub_cancel] at this
    nlinarith
  -- the radius `δ` of the discs
  set δ := min (δ₀ / 2) (η / (4 * (‖v‖ + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (half_pos hδ₀) (by positivity)
  have hδδ₀ : δ < δ₀ := (min_le_left _ _).trans_lt (half_lt_self hδ₀)
  have hδv : δ * ‖v‖ < η / 4 := by
    have h1 : δ ≤ η / (4 * (‖v‖ + 1)) := min_le_right _ _
    have h2 : η / (4 * (‖v‖ + 1)) * ‖v‖ < η / 4 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc δ * ‖v‖ ≤ η / (4 * (‖v‖ + 1)) * ‖v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ < η / 4 := h2
  have hline : ∀ x : V, ‖x - p‖ < η / 4 → ∀ ζ : ℂ, ‖ζ‖ ≤ δ → x + ζ • v ∈ ball p η := by
    intro x hx ζ hζ
    rw [mem_ball, dist_eq_norm]
    calc ‖x + ζ • v - p‖ = ‖(x - p) + ζ • v‖ := by congr 1; abel
      _ ≤ ‖x - p‖ + ‖ζ‖ * ‖v‖ := by rw [← norm_smul]; exact norm_add_le _ _
      _ ≤ ‖x - p‖ + δ * ‖v‖ := by gcongr
      _ < η / 4 + η / 4 := by linarith
      _ < η := by linarith
  -- the minimum `μ` of `|J(p + ζ v)|` on the circle `|ζ| = δ`
  have hsphne : (sphere (0 : ℂ) δ).Nonempty := ⟨(δ : ℂ), by simp [abs_of_pos hδ0]⟩
  have hcont : ContinuousOn (fun ζ : ℂ => ‖J (p + ζ • v)‖) (sphere (0 : ℂ) δ) := by
    refine (continuous_norm.comp_continuousOn ?_)
    refine (hJ.continuousOn.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      fun ζ hζ => hball (hline p (by simp; positivity) ζ (le_of_eq (mem_sphere_zero_iff_norm.mp hζ))))
  obtain ⟨ζ₁, hζ₁, hmin⟩ := (isCompact_sphere (0 : ℂ) δ).exists_isMinOn hsphne hcont
  set μ := ‖J (p + ζ₁ • v)‖ with hμ
  have hζ₁n : ‖ζ₁‖ = δ := mem_sphere_zero_iff_norm.mp hζ₁
  have hμ0 : 0 < μ := by
    refine norm_pos_iff.mpr (hiso ζ₁ ?_ (by rw [hζ₁n]; exact hδδ₀))
    intro h0
    rw [h0, norm_zero] at hζ₁n
    exact hδ0.ne hζ₁n
  have hμmin : ∀ ζ ∈ sphere (0 : ℂ) δ, μ ≤ ‖J (p + ζ • v)‖ := fun ζ hζ => hmin hζ
  -- zeros of `J` on the lines `x + ℂ v`, `x` near `p`
  set η₃ := min (η / 4) (μ / (2 * (LJ + 1))) with hη₃
  have hη₃0 : 0 < η₃ := lt_min (by positivity) (by positivity)
  have hzero : ∀ x : V, ‖x - p‖ < η₃ → ∃ ζ : ℂ, ‖ζ‖ < δ ∧ J (x + ζ • v) = 0 := by
    intro x hx
    have hx4 : ‖x - p‖ < η / 4 := lt_of_lt_of_le hx (min_le_left _ _)
    have hxμ : LJ * ‖x - p‖ < μ / 2 := by
      have h1 : ‖x - p‖ < μ / (2 * (LJ + 1)) := lt_of_lt_of_le hx (min_le_right _ _)
      have h2 : LJ * (μ / (2 * (LJ + 1))) ≤ μ / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      calc LJ * ‖x - p‖ < LJ * (μ / (2 * (LJ + 1))) := by
            exact mul_lt_mul_of_pos_left h1 (by linarith)
        _ ≤ μ / 2 := h2
    have hxB : x ∈ ball p η := by
      rw [mem_ball, dist_eq_norm]; linarith
    have hd : DifferentiableOn ℂ (fun ζ : ℂ => J (x + ζ • v)) (closedBall 0 δ) := by
      intro ζ hζ
      have hζ' : ‖ζ‖ ≤ δ := mem_closedBall_zero_iff.mp hζ
      have h1 := hJd _ (hline x hx4 ζ hζ')
      exact (h1.comp ζ ((differentiableAt_const x).add
        (differentiableAt_id.smul_const v))).differentiableWithinAt
    obtain ⟨ζ, hζ, hJζ⟩ := exists_zero_of_norm_lt hδ0 hd (c := μ / 2) (fun ζ hζ => by
        have hζ' : ‖ζ‖ = δ := mem_sphere_zero_iff_norm.mp hζ
        have h1 := hμmin ζ hζ
        have h2 := hJlip (x + ζ • v) (hline x hx4 ζ hζ'.le) (p + ζ • v)
          (hline p (by simp; positivity) ζ hζ'.le)
        have h3 : (x + ζ • v) - (p + ζ • v) = x - p := by abel
        rw [h3] at h2
        have h4 := norm_sub_norm_le (J (p + ζ • v)) (J (p + ζ • v) - J (x + ζ • v))
        rw [sub_sub_cancel, norm_sub_rev] at h4
        linarith)
      (by
        simp only [zero_smul, add_zero]
        have h1 := hJlip x hxB p (mem_ball_self hη0)
        rw [hJp, sub_zero] at h1
        linarith)
    exact ⟨ζ, mem_ball_zero_iff.mp hζ, hJζ⟩
  -- the curve
  set s₀ := η₃ / (2 * (‖w‖ + 1)) with hs₀
  have hs₀0 : 0 < s₀ := by positivity
  have hsw : ∀ s ∈ Icc (0 : ℝ) s₀, ‖(s : ℂ) • w‖ < η₃ := by
    intro s hs
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖w‖ ≤ s₀ * ‖w‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ = η₃ / 2 * (‖w‖ / (‖w‖ + 1)) := by rw [hs₀]; field_simp
      _ ≤ η₃ / 2 * 1 := mul_le_mul_of_nonneg_left
          (div_le_one_of_le₀ (by linarith) (by positivity)) (by positivity)
      _ < η₃ := by linarith
  have hex : ∀ s : ℝ, ∃ ζ : ℂ, s ∈ Icc (0 : ℝ) s₀ → ‖ζ‖ < δ ∧
      J (p + (s : ℂ) • w + ζ • v) = 0 := by
    intro s
    by_cases hs : s ∈ Icc (0 : ℝ) s₀
    · obtain ⟨ζ, h1, h2⟩ := hzero (p + (s : ℂ) • w) (by rw [add_sub_cancel_left]; exact hsw s hs)
      exact ⟨ζ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hs⟩
  choose ζ hζ using hex
  set c : ℝ → V := fun s => p + (s : ℂ) • w + ζ s • v with hc
  have hη₃4 : η₃ ≤ η / 4 := min_le_left _ _
  have hcB : ∀ s ∈ Icc (0 : ℝ) s₀, ∀ ζ' : ℂ, ‖ζ'‖ < δ →
      p + (s : ℂ) • w + ζ' • v ∈ ball p η := by
    intro s hs ζ' hζ'
    have h1 : ‖(p + (s : ℂ) • w) - p‖ < η / 4 := by
      rw [add_sub_cancel_left]; exact lt_of_lt_of_le (hsw s hs) hη₃4
    exact hline _ h1 ζ' hζ'.le
  have hKc0 : ∀ s ∈ Icc (0 : ℝ) s₀, K (c s) = 0 := fun s hs =>
    hKJ (c s) (hball (hcB s hs (ζ s) (hζ s hs).1)) (hζ s hs).2
  -- Lipschitz bound
  set L := ‖w‖ + 2 * LK * ‖w‖ / c₀ * ‖v‖ with hL
  refine ⟨η, hη0, hηρ, s₀, hs₀0, L, c, ?_, ?_, fun s hs => ⟨hcB s hs (ζ s) (hζ s hs).1,
    (hζ s hs).2, fun s' hs' => ?_⟩⟩
  · -- `c 0 = p`
    have h1 := hζ 0 ⟨le_rfl, hs₀0.le⟩
    have h2 : ζ 0 = 0 := by
      by_contra hne
      refine hiso (ζ 0) hne (lt_trans h1.1 hδδ₀) ?_
      have := h1.2
      simpa using this
    simp [hc, h2]
  · -- `c s₀ ≠ p`
    intro hcp
    have h1 : (s₀ : ℂ) • w + ζ s₀ • v = 0 := by
      have : c s₀ - p = (s₀ : ℂ) • w + ζ s₀ • v := by simp only [hc]; abel
      rw [← this, hcp, sub_self]
    have hs₀c : (s₀ : ℂ) ≠ 0 := by exact_mod_cast hs₀0.ne'
    apply hw
    rw [Submodule.mem_span_singleton]
    refine ⟨-((s₀ : ℂ)⁻¹ * ζ s₀), ?_⟩
    have h2 : w = -((s₀ : ℂ)⁻¹ * ζ s₀) • v := by
      have h3 : (s₀ : ℂ) • w = -(ζ s₀ • v) := eq_neg_of_add_eq_zero_left h1
      calc w = (s₀ : ℂ)⁻¹ • ((s₀ : ℂ) • w) := by rw [smul_smul, inv_mul_cancel₀ hs₀c, one_smul]
        _ = -((s₀ : ℂ)⁻¹ * ζ s₀) • v := by rw [h3, smul_neg, smul_smul, neg_smul]
    exact h2.symm
  · -- Lipschitz bound
    have hy₁ := hcB s hs (ζ s) (hζ s hs).1
    have hy₂ := hcB s hs (ζ s') (hζ s' hs').1
    have hy₃ := hcB s' hs' (ζ s') (hζ s' hs').1
    have h1 := hKinj (c s) hy₁ (p + (s : ℂ) • w + ζ s' • v) hy₂ (ζ s - ζ s') (by
      simp only [hc]; rw [sub_smul]; abel)
    have h2 := hKlip (p + (s : ℂ) • w + ζ s' • v) hy₂ (c s') hy₃
    rw [hKc0 s hs, zero_sub, norm_neg] at h1
    rw [hKc0 s' hs', sub_zero] at h2
    have h3 : (p + (s : ℂ) • w + ζ s' • v) - c s' = ((s : ℂ) - s') • w := by
      simp only [hc]; rw [sub_smul]; abel
    rw [h3, norm_smul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h2
    have h4 : ‖ζ s - ζ s'‖ ≤ 2 * LK * ‖w‖ / c₀ * |s - s'| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc₀0]
      nlinarith [norm_nonneg (ζ s - ζ s'), abs_nonneg (s - s'), norm_nonneg w]
    have h5 : c s - c s' = ((s : ℂ) - s') • w + (ζ s - ζ s') • v := by
      simp only [hc]; rw [sub_smul, sub_smul]; abel
    rw [h5]
    calc ‖((s : ℂ) - s') • w + (ζ s - ζ s') • v‖
        ≤ ‖((s : ℂ) - s') • w‖ + ‖(ζ s - ζ s') • v‖ := norm_add_le _ _
      _ = |s - s'| * ‖w‖ + ‖ζ s - ζ s'‖ * ‖v‖ := by
          rw [norm_smul, norm_smul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |s - s'| * ‖w‖ + 2 * LK * ‖w‖ / c₀ * |s - s'| * ‖v‖ := by
          gcongr
      _ = L * |s - s'| := by rw [hL]; ring

end LoewnerS0
