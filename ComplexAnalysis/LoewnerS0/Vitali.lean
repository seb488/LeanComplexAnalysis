import LoewnerS0.SCV

/-!
# Pointwise limits of locally bounded holomorphic maps

A light version of **Vitali's theorem** for holomorphic maps of several variables, as needed for
the time derivative of a Loewner chain:

* `LoewnerS0.SCV.exists_tendsto_of_dense`: if a family of maps is eventually equi-Lipschitz on a
  set `S` and converges at the points of a dense subset of `S`, then it converges at every point
  of `S` (Cauchy criterion; the target is complete);
* `LoewnerS0.SCV.tendstoUniformlyOn_of_lipschitzOnWith`: an equi-Lipschitz family converging
  pointwise on a compact set converges uniformly there;
* `LoewnerS0.SCV.lipschitzOnWith_of_bound`: by the Cauchy estimate, a holomorphic map bounded by `M`
  on `closedBall 0 r'` is `M/(r' - r)`-Lipschitz on `closedBall 0 r`;
* `LoewnerS0.SCV.differentiableOn_of_tendsto_of_bounded`: a pointwise limit of holomorphic maps
  that are uniformly bounded on the closed balls `closedBall 0 r`, `r < R`, is holomorphic on
  `ball 0 R`.
-/

open Metric Set Filter
open scoped Topology NNReal

noncomputable section

namespace LoewnerS0.SCV

section Metric

variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]

/-- Convergence on a dense set of an eventually equi-Lipschitz family implies convergence
everywhere (the target being complete). -/
theorem exists_tendsto_of_dense [CompleteSpace β] {ι : Type*} {l : Filter ι} [l.NeBot]
    {Q : ι → α → β} {S D : Set α} {L : ℝ≥0}
    (hlip : ∀ᶠ i in l, LipschitzOnWith L (Q i) S) (hD : S ⊆ closure (D ∩ S))
    (hconv : ∀ d ∈ D ∩ S, ∃ y, Tendsto (fun i => Q i d) l (𝓝 y)) {z : α} (hz : z ∈ S) :
    ∃ y, Tendsto (fun i => Q i z) l (𝓝 y) := by
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  refine ⟨map_neBot, fun η hη => ?_⟩
  have hL : (0 : ℝ) < 4 * ((L : ℝ) + 1) := by positivity
  obtain ⟨d, hdDS, hdz⟩ := Metric.mem_closure_iff.mp (hD hz) (η / (4 * ((L : ℝ) + 1)))
    (div_pos hη hL)
  obtain ⟨y, hy⟩ := hconv d hdDS
  have h1 : ∀ᶠ i in l, dist (Q i d) y < η / 4 := (Metric.tendsto_nhds.mp hy) _ (by positivity)
  refine ⟨_, image_mem_map (h1.and hlip), ?_⟩
  rintro _ ⟨i, ⟨hi1, hi2⟩, rfl⟩ _ ⟨j, ⟨hj1, hj2⟩, rfl⟩
  have hLd : (L : ℝ) * dist z d ≤ η / 4 := by
    have h2 : (L : ℝ) * dist z d ≤ ((L : ℝ) + 1) * (η / (4 * ((L : ℝ) + 1))) := by
      apply mul_le_mul (by linarith) hdz.le dist_nonneg (by positivity)
    have h3 : ((L : ℝ) + 1) * (η / (4 * ((L : ℝ) + 1))) = η / 4 := by
      field_simp
    linarith
  have hi3 := hi2.dist_le_mul z hz d hdDS.2
  have hj3 := hj2.dist_le_mul z hz d hdDS.2
  calc dist (Q i z) (Q j z) ≤ dist (Q i z) (Q i d) + dist (Q i d) y + dist y (Q j d) +
        dist (Q j d) (Q j z) := by
          have := dist_triangle (Q i z) (Q i d) y
          have := dist_triangle (Q i z) y (Q j z)
          have := dist_triangle y (Q j d) (Q j z)
          linarith
    _ < η / 4 + η / 4 + η / 4 + η / 4 := by
        rw [dist_comm y (Q j d), dist_comm (Q j d) (Q j z)]
        have : dist (Q i z) (Q i d) ≤ η / 4 := hi3.trans hLd
        have : dist (Q j z) (Q j d) ≤ η / 4 := hj3.trans hLd
        linarith
    _ = η := by ring

/-- An equi-Lipschitz family that converges pointwise on a compact set converges uniformly
there. -/
theorem tendstoUniformlyOn_of_lipschitzOnWith {ι : Type*} {l : Filter ι} {Q : ι → α → β}
    {g : α → β} {K : Set α} {L : ℝ≥0} (hK : IsCompact K)
    (hQ : ∀ᶠ i in l, LipschitzOnWith L (Q i) K) (hg : LipschitzOnWith L g K)
    (hlim : ∀ w ∈ K, Tendsto (fun i => Q i w) l (𝓝 (g w))) : TendstoUniformlyOn Q g l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have hL : (0 : ℝ) < 3 * ((L : ℝ) + 1) := by positivity
  set δ := η / (3 * ((L : ℝ) + 1)) with hδ
  have hδ0 : 0 < δ := div_pos hη hL
  have hLδ : (L : ℝ) * δ < η / 3 := by
    have h1 : (L : ℝ) * δ < ((L : ℝ) + 1) * δ := by nlinarith
    have h2 : ((L : ℝ) + 1) * δ = η / 3 := by rw [hδ]; field_simp
    linarith
  obtain ⟨t, htK, htf, hcover⟩ := finite_cover_balls_of_compact hK hδ0
  have hev : ∀ᶠ i in l, ∀ x ∈ t, dist (g x) (Q i x) < η / 3 :=
    (htf.eventually_all).mpr fun x hx =>
      (Metric.tendsto_nhds.mp (hlim x (htK hx)) (η / 3) (by positivity)).mono fun i hi => by
        rw [dist_comm]; exact hi
  filter_upwards [hev, hQ] with i hi hiL w hw
  obtain ⟨x, hxt, hwx⟩ := mem_iUnion₂.mp (hcover hw)
  have h1 := hg.dist_le_mul w hw x (htK hxt)
  have h2 := hiL.dist_le_mul x (htK hxt) w hw
  have h3 : dist w x < δ := hwx
  have h4 : (L : ℝ) * dist w x ≤ (L : ℝ) * δ := mul_le_mul_of_nonneg_left h3.le L.2
  have h5 : (L : ℝ) * dist x w ≤ (L : ℝ) * δ := by rw [dist_comm]; exact h4
  calc dist (g w) (Q i w) ≤ dist (g w) (g x) + dist (g x) (Q i x) + dist (Q i x) (Q i w) :=
        dist_triangle4 _ _ _ _
    _ < η / 3 + η / 3 + η / 3 := by linarith [hi x hxt]
    _ = η := by ring

/-- A pointwise limit of `L`-Lipschitz maps is `L`-Lipschitz. -/
theorem lipschitzOnWith_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {Q : ι → α → β}
    {g : α → β} {S : Set α} {L : ℝ≥0} (hQ : ∀ᶠ i in l, LipschitzOnWith L (Q i) S)
    (hlim : ∀ w ∈ S, Tendsto (fun i => Q i w) l (𝓝 (g w))) : LipschitzOnWith L g S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := (hlim x hx).dist (hlim y hy)
  exact le_of_tendsto h (hQ.mono fun i hi => hi.dist_le_mul x hx y hy)

end Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- By the Cauchy estimate, a holomorphic map bounded by `M` on `closedBall 0 r'` is
`M / (r' - r)`-Lipschitz on `closedBall 0 r` (`r < r'`). -/
theorem lipschitzOnWith_of_bound {f : E → F} {U : Set E} {r r' M : ℝ} (hrr' : r < r')
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hsub : closedBall (0 : E) r' ⊆ U)
    (hM : ∀ w ∈ closedBall (0 : E) r', ‖f w‖ ≤ M) :
    LipschitzOnWith (M / (r' - r)).toNNReal f (closedBall 0 r) := by
  have hδ : 0 < r' - r := sub_pos.mpr hrr'
  have hball : ∀ x ∈ closedBall (0 : E) r, closedBall x (r' - r) ⊆ closedBall 0 r' := by
    intro x hx w hw
    rw [mem_closedBall_zero_iff] at hx ⊢
    rw [mem_closedBall, dist_eq_norm] at hw
    calc ‖w‖ = ‖(w - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ (r' - r) + r := add_le_add hw hx
      _ = r' := by ring
  apply (convex_closedBall (0 : E) r).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℂ)
  · intro x hx
    have hxU : x ∈ U := hsub (hball x hx (mem_closedBall_self hδ.le))
    exact hf.differentiableAt (hU.mem_nhds hxU)
  · intro x hx
    rw [← norm_toNNReal]
    apply Real.toNNReal_le_toNNReal
    exact norm_fderiv_le_of_forall_mem_closedBall_norm_le hδ hf hU ((hball x hx).trans hsub)
      fun w hw => hM w (hball x hx hw)

variable [FiniteDimensional ℂ E] [CompleteSpace F]

/-- **Vitali's theorem** (the version with pointwise convergence everywhere): a pointwise limit on
`ball 0 R` of holomorphic maps that are uniformly bounded on every `closedBall 0 r`, `r < R`, is
holomorphic on `ball 0 R`. -/
theorem differentiableOn_of_tendsto_of_bounded {Q : ℕ → E → F} {g : E → F} {R : ℝ}
    (hQ : ∀ n, DifferentiableOn ℂ (Q n) (ball 0 R))
    (hbd : ∀ r < R, ∃ M, ∀ n, ∀ w ∈ closedBall (0 : E) r, ‖Q n w‖ ≤ M)
    (hlim : ∀ w ∈ ball (0 : E) R, Tendsto (fun n => Q n w) atTop (𝓝 (g w))) :
    DifferentiableOn ℂ g (ball 0 R) := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  intro x hx
  have hxR : ‖x‖ < R := mem_ball_zero_iff.mp hx
  set r := (‖x‖ + R) / 2 with hr
  set r' := (r + R) / 2 with hr'
  have hxr : ‖x‖ < r := by rw [hr]; linarith
  have hrr' : r < r' := by rw [hr']; linarith
  have hr'R : r' < R := by rw [hr']; linarith
  obtain ⟨M, hM⟩ := hbd r' hr'R
  have hsub : closedBall (0 : E) r' ⊆ ball 0 R := closedBall_subset_ball hr'R
  have hlipQ : ∀ n, LipschitzOnWith (M / (r' - r)).toNNReal (Q n) (closedBall 0 r) := fun n =>
    lipschitzOnWith_of_bound hrr' isOpen_ball (hQ n) hsub (hM n)
  have hsubr : closedBall (0 : E) r ⊆ ball 0 R := closedBall_subset_ball (hrr'.trans hr'R)
  have hlimr : ∀ w ∈ closedBall (0 : E) r, Tendsto (fun n => Q n w) atTop (𝓝 (g w)) :=
    fun w hw => hlim w (hsubr hw)
  have hlipg := lipschitzOnWith_of_tendsto (Eventually.of_forall hlipQ) hlimr
  have hunif := tendstoUniformlyOn_of_lipschitzOnWith (isCompact_closedBall 0 r)
    (Eventually.of_forall hlipQ) hlipg hlimr
  have hd := differentiableOn_of_tendstoUniformlyOn isOpen_ball
    (fun n => (hQ n).mono (ball_subset_ball (hrr'.trans hr'R).le))
    (hunif.mono ball_subset_closedBall)
  exact ((hd x (mem_ball_zero_iff.mpr hxr)).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hxr))).differentiableWithinAt

end LoewnerS0.SCV
