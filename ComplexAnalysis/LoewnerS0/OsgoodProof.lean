import LoewnerS0.OsgoodCurve
import LoewnerS0.OsgoodOneDim

/-!
# Osgood's theorem

**Theorem** (Osgood, 1899). Let `V` be a finite-dimensional complex normed space, `U ⊆ V` open and
`f : U → V` holomorphic and injective. Then `det Df(z) ≠ 0` for every `z ∈ U`
(`LoewnerS0.osgoodTheorem : OsgoodTheorem V`).

The proof is by induction on `n = dim V` (`LoewnerS0.osgoodInj_of_finrank`):

* `n = 0`: nothing to prove; `n = 1`: the one-variable theorem (`LoewnerS0.deriv_ne_zero_of_injOn`,
  a `k`-th root argument), see `LoewnerS0.injective_fderiv_of_finrank_one`;
* `n ≥ 2`: if `Df(z) ≠ 0`, the slicing step (`LoewnerS0.injective_fderiv_of_ne_zero`) and the
  induction hypothesis for the hyperplanes of `V` show that `Df(z)` is injective. So at every point
  `Df` is either `0` or injective, and the degenerate case `Df(z) = 0` is impossible
  (`LoewnerS0.fderiv_ne_zero_of_dichotomy`): the zero set of `det Df` would contain a Lipschitz curve
  on which `f` is constant.
-/

open Function Set Filter Module Metric Complex
open scoped Topology

noncomputable section

namespace LoewnerS0

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- **The degenerate case**: if `dim V ≥ 2` and `Df` is either `0` or injective at every point,
then `Df` vanishes nowhere. -/
theorem fderiv_ne_zero_of_dichotomy (hn : 2 ≤ finrank ℂ V) {f : V → V} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hdich : ∀ z ∈ U, fderiv ℂ f z ≠ 0 → Injective (fderiv ℂ f z)) {z₀ : V} (hz₀ : z₀ ∈ U) :
    fderiv ℂ f z₀ ≠ 0 := by
  intro hzero
  have hpos : 0 < finrank ℂ V := by omega
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  set J := jacDet f with hJdef
  have hJd : DifferentiableOn ℂ J U := differentiableOn_jacDet hU hf
  have hJzero : ∀ z ∈ U, J z = 0 → fderiv ℂ f z = 0 := by
    intro z hz hJ
    by_contra hne
    exact jacDet_ne_zero_iff.mpr (hdich z hz hne) hJ
  have hJz₀ : J z₀ = 0 := by
    by_contra hne
    have hinjD := jacDet_ne_zero_iff.mp hne
    rw [hzero] at hinjD
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    exact hx (hinjD (by simp))
  -- `J` does not vanish identically on any ball
  have hJnz : ∀ q : V, ∀ r > 0, ball q r ⊆ U → ∃ y ∈ ball q r, J y ≠ 0 := by
    intro q r hr hsub
    by_contra h
    push Not at h
    have hD : ∀ y ∈ ball q r, fderiv ℂ f y = 0 := fun y hy => hJzero y (hsub hy) (h y hy)
    obtain ⟨e, he⟩ := exists_ne (0 : V)
    have hen : 0 < ‖e‖ := norm_pos_iff.mpr he
    set y := q + ((r / 2 / ‖e‖ : ℝ) : ℂ) • e with hy
    have hye : y - q = ((r / 2 / ‖e‖ : ℝ) : ℂ) • e := by rw [hy]; abel
    have hyn : ‖y - q‖ = r / 2 := by
      rw [hye, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp
    have hyB : y ∈ ball q r := by rw [mem_ball, dist_eq_norm, hyn]; linarith
    have hconst : ‖f y - f q‖ ≤ 0 * ‖y - q‖ :=
      (convex_ball q r).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
        (fun x hx => hf.differentiableAt (hU.mem_nhds (hsub hx)))
        (fun x hx => by rw [hD x hx, norm_zero]) (mem_ball_self hr) hyB
    rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at hconst
    have hyq := hinj (hsub hyB) (hsub (mem_ball_self hr)) hconst
    rw [hyq, sub_self, norm_zero] at hyn
    linarith
  -- every point has a nonvanishing derivative of `J` along some line
  have hline : ∀ q ∈ U, ∃ k, ∃ w : V, iteratedDeriv k (fun ζ : ℂ => J (q + ζ • w)) 0 ≠ 0 := by
    intro q hq
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU q hq
    obtain ⟨y, hy, hJy⟩ := hJnz q r hr hrU
    by_contra h
    push Not at h
    apply hJy
    set w := y - q with hw
    have hwr : ‖w‖ < r := by rw [hw, ← dist_eq_norm]; exact mem_ball.mp hy
    rcases eq_or_ne w 0 with hw0 | hw0
    · have h0 := h 0 0
      simp only [iteratedDeriv_zero, zero_smul, add_zero] at h0
      have hyq : y = q := sub_eq_zero.mp hw0
      rw [hyq]
      exact h0
    · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      set R := r / ‖w‖ with hR
      have hR1 : 1 < R := by rw [hR, one_lt_div hwpos]; exact hwr
      have hdiff : DifferentiableOn ℂ (fun ζ : ℂ => J (q + ζ • w)) (ball 0 R) := by
        intro ζ hζ
        have hmem : q + ζ • w ∈ ball q r := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
          rw [mem_ball_zero_iff] at hζ
          calc ‖ζ‖ * ‖w‖ < R * ‖w‖ := mul_lt_mul_of_pos_right hζ hwpos
            _ = r := by rw [hR]; field_simp
        exact ((hJd.differentiableAt (hU.mem_nhds (hrU hmem))).comp ζ
          ((differentiableAt_const q).add (differentiableAt_id.smul_const w))).differentiableWithinAt
      have h1 := Complex.taylorSeries_eq_on_ball' (z := 1)
        (by rw [mem_ball_zero_iff, norm_one]; exact hR1) hdiff
      simp only [h, mul_zero, zero_mul, tsum_zero, one_smul] at h1
      rw [hw, add_sub_cancel] at h1
      exact h1.symm
  -- the minimal line order of the zeros of `J` near `z₀`
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hS : ∃ k, ∃ q ∈ ball z₀ R, J q = 0 ∧
      ∃ w : V, iteratedDeriv k (fun ζ : ℂ => J (q + ζ • w)) 0 ≠ 0 := by
    obtain ⟨k, w, hk⟩ := hline z₀ hz₀
    exact ⟨k, z₀, mem_ball_self hR, hJz₀, w, hk⟩
  classical
  have hmin : ∀ q ∈ ball z₀ R, J q = 0 → ∀ j < Nat.find hS, ∀ w : V,
      iteratedDeriv j (fun ζ : ℂ => J (q + ζ • w)) 0 = 0 := by
    intro q hq hJq j hj w
    by_contra h
    exact Nat.find_min hS hj ⟨q, hq, hJq, w, h⟩
  obtain ⟨p, hpB, hJp, v, hv⟩ := Nat.find_spec hS
  have hm0 : Nat.find hS ≠ 0 := by
    intro h0
    rw [h0] at hv
    simp [iteratedDeriv_zero, hJp] at hv
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hS = m + 1 := ⟨Nat.find hS - 1, by omega⟩
  rw [hm] at hv hmin
  have hpU : p ∈ U := hRU hpB
  -- `K = ∂_v^m J`
  set K : V → ℂ := fun x => iteratedFDeriv ℂ m J x (fun _ => v) with hK
  have hIt : DifferentiableOn ℂ (iteratedFDeriv ℂ m J) U := by
    have h1 := (hJd.contDiffOn_of_isOpen hU (m + 1)).differentiableOn_iteratedFDerivWithin
      (m := m) (by exact_mod_cast Nat.lt_succ_self m) hU.uniqueDiffOn
    exact h1.congr fun x hx => (iteratedFDerivWithin_of_isOpen m hU hx).symm
  have hKd : DifferentiableOn ℂ K U :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin m => V) ℂ (fun _ => v)).differentiable.comp_differentiableOn
      hIt
  have hKJ : ∀ q ∈ ball z₀ R, J q = 0 → K q = 0 := by
    intro q hq hJq
    show iteratedFDeriv ℂ m J q (fun _ => v) = 0
    rw [← iteratedDeriv_line hU hJd (hRU hq) v m]
    exact hmin q hq hJq m (Nat.lt_succ_self m) v
  have hKv : fderiv ℂ K p v ≠ 0 := by
    have hd := (hIt.differentiableAt (hU.mem_nhds hpU)).hasFDerivAt
    have hKder : HasFDerivAt K ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin m => V) ℂ
        (fun _ => v)).comp (fderiv ℂ (iteratedFDeriv ℂ m J) p)) p :=
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin m => V) ℂ (fun _ => v)).hasFDerivAt.comp p hd
    rw [hKder.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply]
    have h1 := iteratedFDeriv_succ_apply_left (𝕜 := ℂ) (f := J) (n := m) (x := p)
      (fun _ : Fin (m + 1) => v)
    rw [← iteratedDeriv_line hU hJd hpU v (m + 1)] at h1
    rw [show (Fin.tail fun _ : Fin (m + 1) => v) = fun _ => v from rfl] at h1
    rw [← h1]
    exact hv
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hKv (map_zero _)
  -- `ζ ↦ J(p + ζ v)` has an isolated zero at `0`
  have hφan : AnalyticAt ℂ (fun ζ : ℂ => J (p + ζ • v)) 0 := by
    have hDo : IsOpen ((fun ζ : ℂ => p + ζ • v) ⁻¹' U) :=
      hU.preimage (continuous_const.add (continuous_id.smul continuous_const))
    have h0D : (0 : ℂ) ∈ (fun ζ : ℂ => p + ζ • v) ⁻¹' U := by simp [hpU]
    have hd : DifferentiableOn ℂ (fun ζ : ℂ => J (p + ζ • v)) ((fun ζ : ℂ => p + ζ • v) ⁻¹' U) :=
      hJd.comp ((differentiable_const p).add (differentiable_id.smul_const v)).differentiableOn
        fun ζ hζ => hζ
    exact hd.analyticAt (hDo.mem_nhds h0D)
  obtain ⟨δ₀, hδ₀, hiso⟩ : ∃ δ₀ > 0, ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < δ₀ → J (p + ζ • v) ≠ 0 := by
    rcases hφan.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      apply hv
      have h1 : (fun ζ : ℂ => J (p + ζ • v)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := h
      rw [(h1.iteratedDeriv (m + 1)).self_of_nhds, iteratedDeriv_eq_iteratedFDeriv,
        iteratedFDeriv_fun_zero]
      rfl
    · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
      obtain ⟨ε, hε, hε'⟩ := h
      exact ⟨ε, hε, fun ζ hζ0 hζε => hε' (by rwa [dist_zero_right]) hζ0⟩
  -- a direction `w ∉ ℂ v`
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ Submodule.span ℂ {v} := by
    by_contra h
    push Not at h
    have htop : Submodule.span ℂ {v} = ⊤ := eq_top_iff.mpr fun x _ => h x
    have h1 := finrank_span_singleton (K := ℂ) hv0
    rw [htop, finrank_top] at h1
    omega
  -- the curve
  obtain ⟨ρ, hρ, hρB⟩ := Metric.isOpen_iff.mp isOpen_ball p hpB
  have hρU : ball p ρ ⊆ U := hρB.trans hRU
  obtain ⟨η, hη0, hηρ, s₀, hs₀, L, c, hc0, hcs₀, hc⟩ := exists_curve hρ (hJd.mono hρU)
    (hKd.mono hρU) hJp hδ₀ hiso (fun q hq hJq => hKJ q (hρB hq) hJq) hKv hw
  -- `f` is constant along the curve
  have hsub : closedBall p η ⊆ U := (closedBall_subset_ball hηρ).trans hρU
  obtain ⟨M, hM0, hM⟩ := exists_norm_sub_le_sq hU hf hsub
  have hfc : f (c s₀) = f (c 0) := by
    refine eq_of_norm_sub_le_mul_sq (g := fun s => f (c s)) hs₀.le
      (by positivity : 0 ≤ M * L ^ 2) fun s hs s' hs' => ?_
    obtain ⟨hcs, -, hlip⟩ := hc s hs
    obtain ⟨hcs', hJcs', -⟩ := hc s' hs'
    have hDf : fderiv ℂ f (c s') = 0 :=
      hJzero (c s') (hsub (ball_subset_closedBall hcs')) hJcs'
    have h1 := hM (c s') (ball_subset_closedBall hcs') (c s) (ball_subset_closedBall hcs) hDf
    have h2 : ‖c s - c s'‖ ^ 2 ≤ (L * |s - s'|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hlip s' hs') 2
    calc ‖f (c s) - f (c s')‖ ≤ M * ‖c s - c s'‖ ^ 2 := h1
      _ ≤ M * (L * |s - s'|) ^ 2 := mul_le_mul_of_nonneg_left h2 hM0
      _ = M * L ^ 2 * (s - s') ^ 2 := by rw [mul_pow, sq_abs]; ring
  have hcs₀U : c s₀ ∈ U := hsub (ball_subset_closedBall (hc s₀ ⟨hs₀.le, le_rfl⟩).1)
  rw [hc0] at hfc
  exact hcs₀ (hinj hcs₀U hpU hfc)

/-- **Osgood's theorem in dimension one.** -/
theorem injective_fderiv_of_finrank_one (hV : finrank ℂ V = 1) {f : V → V} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) {z : V} (hz : z ∈ U) :
    Injective (fderiv ℂ f z) := by
  set b := Module.finBasisOfFinrankEq ℂ V hV with hb
  set e := b 0 with he
  set ℓ : V →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (b.coord 0) with hℓ
  have hrepr : ∀ x : V, ℓ x • e = x := by
    intro x
    have := b.sum_repr x
    simpa [Fin.sum_univ_one, hℓ, he] using this
  have hℓinj : Injective ℓ := fun x y hxy => by rw [← hrepr x, ← hrepr y, hxy]
  have he0 : e ≠ 0 := b.ne_zero 0
  set D := (fun ζ : ℂ => z + ζ • e) ⁻¹' U with hD
  have hDo : IsOpen D := hU.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have h0D : (0 : ℂ) ∈ D := by simp [hD, hz]
  set φ : ℂ → ℂ := fun ζ => ℓ (f (z + ζ • e)) with hφ
  have hφd : DifferentiableOn ℂ φ D :=
    ℓ.differentiable.comp_differentiableOn
      (hf.comp ((differentiable_const z).add (differentiable_id.smul_const e)).differentiableOn
        fun ζ hζ => hζ)
  have hφi : InjOn φ D := by
    intro ζ₁ h₁ ζ₂ h₂ h12
    have h3 := hinj h₁ h₂ (hℓinj h12)
    exact smul_left_injective ℂ he0 (add_left_cancel h3)
  have hd := deriv_ne_zero_of_injOn hDo hφd hφi h0D
  have hφder : HasDerivAt φ (ℓ (fderiv ℂ f z e)) 0 := by
    have h1 : HasDerivAt (fun ζ : ℂ => z + ζ • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const e).const_add z
    have h2 : HasFDerivAt f (fderiv ℂ f z) (z + (0 : ℂ) • e) := by
      simpa using (hf.differentiableAt (hU.mem_nhds hz)).hasFDerivAt
    exact ℓ.hasFDerivAt.comp_hasDerivAt 0 (h2.comp_hasDerivAt 0 h1)
  rw [hφder.deriv] at hd
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← hrepr x, map_smul] at hx
  rcases smul_eq_zero.mp hx with h | h
  · rw [← hrepr x, h, zero_smul]
  · exact absurd (by rw [h, map_zero]) hd

universe u

/-- **Osgood's theorem**, by induction on the dimension: the derivative of an injective holomorphic
map of an open subset of an `n`-dimensional complex normed space is injective. -/
theorem osgoodInj_of_finrank (n : ℕ) :
    ∀ (W : Type u) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W],
      finrank ℂ W = n → OsgoodInj W := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W _ _ _ hW f U hU hf hinj z hz
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · have : Subsingleton W := Module.finrank_zero_iff.mp hW
      exact fun x y _ => Subsingleton.elim x y
    · exact injective_fderiv_of_finrank_one hW hU hf hinj hz
  · have IH : ∀ H : Submodule ℂ W, finrank ℂ H + 1 = finrank ℂ W → OsgoodInj H :=
      fun H hH => ih (finrank ℂ H) (by omega) H rfl
    have hdich : ∀ w ∈ U, fderiv ℂ f w ≠ 0 → Injective (fderiv ℂ f w) :=
      fun w hw hne => injective_fderiv_of_ne_zero IH hU hf hinj hw hne
    by_cases h0 : fderiv ℂ f z = 0
    · exact absurd h0 (fderiv_ne_zero_of_dichotomy (by omega) hU hf hinj hdich hz)
    · exact hdich z hz h0

/-- **Osgood's theorem** (W. F. Osgood, 1899): an injective holomorphic map of an open subset of a
finite-dimensional complex normed space `V` into `V` has nonvanishing Jacobian determinant. -/
theorem osgoodTheorem : OsgoodTheorem V := by
  intro f U hU hf hinj z hz
  exact jacDet_ne_zero_iff.mpr (osgoodInj_of_finrank _ V rfl f U hU hf hinj z hz)

end LoewnerS0
