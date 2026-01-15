module
public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Tactic

/-!
# Uniqueness of the Herglotz–Riesz measure

## Main Results

Theorem `HerglotzRiesz_representation_uniqueness`:

If for two probability measures `μ₁` and `μ₂` on the unit circle Metric.sphere (0 : ℂ) 1
the two functions ∫ x, (x + z) / (x - z) ∂μ₁ and ∫ x, (x + z) / (x - z) ∂μ₂ are
identical on the unit disc Metric.ball (0 : ℂ) 1, then `μ₁` = `μ₂`.
-/

public section

open MeasureTheory Metric

/-- We expand the Herglotz–Riesz kernel into a power series at 0 by using that
 1/(1 - z/w) = Σ_{n=0}^∞ (z/w)^n. -/
lemma kernel_expansion (z : ℂ) (hz : ‖z‖ < 1) (w : ℂ) (hw : ‖w‖ = 1) :
    (w + z) / (w - z) = 1 + 2 * ∑' n : ℕ, z ^ (n + 1) * star (w ^ (n + 1)) := by
  field_simp
  have h_expand : (1 : ℂ) + 2 * z / (w - z) = 1 + 2 * ∑' n : ℕ, (z / w) ^ (n + 1) := by
    have h_expand : ∑' n : ℕ, (z / w) ^ (n + 1) = z / w / (1 - z / w) := by
      have h_geo_series : (∑' n : ℕ, (z / w) ^ (n + 1)) =
        (z / w) * (∑' n : ℕ, (z / w) ^ n) := by
        rw [← tsum_mul_left] ; exact tsum_congr fun _ => by ring
      rw [h_geo_series, tsum_geometric_of_norm_lt_one]
      · aesop
      simp_all
    by_cases h : w = 0 <;> simp_all [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    · left ; field_simp [h]
  convert h_expand using 1
  · rw [one_add_div]
    · ring
    · exact sub_ne_zero_of_ne <| by rintro rfl; exact absurd hz <| by simpa using hw.ge
  · norm_num [div_pow, mul_div]
    congr! 2
    rw [div_eq_mul_inv] ; rw [Complex.inv_def] ; simp [Complex.normSq_eq_norm_sq]
    erw [hw] ; norm_num

/-- The expansion kernel_expansion is used to rewrite the integral. -/
lemma integral_kernel_expansion
    (μ : ProbabilityMeasure (sphere (0 : ℂ) 1)) (z : ℂ) (hz : ‖z‖ < 1) :
    ∫ x : (sphere (0 : ℂ) 1), (x + z) / (x - z) ∂μ = 1 + 2 * ∑' n : ℕ,
      z ^ (n + 1) * ∫ x : (sphere (0 : ℂ) 1), star (x.val ^ (n + 1)) ∂μ := by
  have h_integral : ∫ x : (sphere (0 : ℂ) 1), (x + z) / (x - z) ∂μ =
     ∫ x : (sphere (0 : ℂ) 1), (1 + 2 * ∑' n : ℕ, z ^ (n + 1) * star ((x : ℂ) ^ (n + 1))) ∂μ := by
    apply integral_congr_ae (by filter_upwards with x; apply kernel_expansion z hz; simp)
  rw [h_integral, integral_add, integral_const_mul] <;> norm_num
  · rw [integral_tsum]
    · exact tsum_congr fun _ => integral_const_mul _ _
    · fun_prop (disch := norm_num)
    · refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum
        (g := fun n => ENNReal.ofReal (‖z‖ ^ (n + 1))) fun n => ?_) ?_)
      · refine le_trans (lintegral_mono_ae (g := fun _ => ENNReal.ofReal (‖z‖ ^ (n + 1))) ?_) ?_
        · simp [ENorm.enorm]
          filter_upwards with a
          have ha : ‖(a : ℂ)‖ = 1 := by simp
          have ha_norm : ‖(a : ℂ)‖₊ = 1 := by
            have : ‖(a : ℂ)‖ = 1 := by simp
            ext ; exact this
          rw [ha_norm]
          simp
        · norm_num
      · rw [← ENNReal.ofReal_tsum_of_nonneg] <;> norm_num
        exact Summable.comp_injective (summable_geometric_of_lt_one (norm_nonneg _) hz)
          (Nat.succ_injective)
  · /- The series Σ_{n=1}^∞ z^n conj{x^n} is absolutely convergent,
    so the function is integrable. -/
    refine (MeasureTheory.Integrable.const_mul (c := (2 : ℂ)) ?_)
    refine Integrable.mono' (g := fun x => ∑' n : ℕ, ‖z‖ ^ (n + 1) *
      ‖starRingEnd ℂ (x : ℂ)‖ ^ (n + 1)) ?_ ?_ ?_
    · norm_num
    · refine Continuous.aestronglyMeasurable ?_
      refine continuous_tsum (u := fun n => ‖z‖ ^ (n + 1)) ?_ ?_ ?_
      · fun_prop
      · exact Summable.comp_injective (summable_geometric_of_lt_one (norm_nonneg _) hz)
          (Nat.succ_injective)
      · simp [sphere]
    · refine Filter.Eventually.of_forall fun x => ?_;
      refine le_trans (norm_tsum_le_tsum_norm ?_) ?_;
      · simpa using summable_nat_add_iff 1 |>.2 <| summable_geometric_of_lt_one (by positivity) hz
      · aesop

/-- Equal moments with natural exponents imply equal moments with integer exponents. -/
lemma moments_eq_integers (μ₁ μ₂ : ProbabilityMeasure (sphere (0 : ℂ) 1))
    (h : ∀ n : ℕ, ∫ x : (sphere (0 : ℂ) 1), x.val ^ n ∂μ₁ =
      ∫ x : (sphere (0 : ℂ) 1), x.val ^ n ∂μ₂) :
    ∀ n : ℤ, ∫ x : (sphere (0 : ℂ) 1), x.val ^ n ∂μ₁ = ∫ x : (sphere (0 : ℂ) 1), x.val ^ n ∂μ₂ := by
  -- For n < 0, let m = -n > 0. Then z^n = z^{-m} = (z^m)^{-1}.
  intro n
  by_cases h_neg : n < 0
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -m := by
      exact ⟨Int.toNat (-n), by rw [Int.toNat_of_nonneg (neg_nonneg.mpr h_neg.le)] ; ring⟩
    -- Since |z|=1 for `z` in the unit circle, we have z^{-m} = conj{z^m}.
    have h_inv : ∀ x : (sphere (0 : ℂ) 1), x ^ (-m : ℤ) = starRingEnd ℂ (x ^ m) := by
      norm_num
      intro x hx
      rw [inv_eq_of_mul_eq_one_right]
      simp [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, hx]
    /- Since |z|=1 for `z` in the unit circle, we have
    ∫ z^{-m} dμ₁ = ∫ conj{z^m} dμ₁. -/
    have h_inv_integral : ∫ x : (sphere (0 : ℂ) 1), (x : ℂ) ^ (-m : ℤ) ∂μ₁ =
      starRingEnd ℂ (∫ x : (sphere (0 : ℂ) 1), (x : ℂ) ^ m ∂μ₁) ∧ ∫ x : (sphere (0 : ℂ) 1),
        (x : ℂ) ^ (-m : ℤ) ∂μ₂ = starRingEnd ℂ (∫ x : (sphere (0 : ℂ) 1), (x : ℂ) ^ m ∂μ₂) := by
      simp only [h_inv, integral_conj]; simp
    aesop
  · cases n <;> aesop

/-- The power function is continuous on the unit circle. -/
lemma continuous_zpow_on_unit_circle (n : ℤ) :
    Continuous (fun x : (sphere (0 : ℂ) 1) => x.val ^ n) := by
  fun_prop (disch := norm_num)

/-- The span of moments is dense in the space of continuous functions on the unit circle. -/
lemma span_moments_dense : (Submodule.span ℂ (Set.range (fun n : ℤ => ContinuousMap.mk (
    fun x : (sphere (0 : ℂ) 1) => x.val ^ n)
      (continuous_zpow_on_unit_circle n)))).topologicalClosure = ⊤ := by
  -- Let `A` be the subalgebra generated by {z^n | n ∈ ℤ}.
  set A : StarSubalgebra ℂ (ContinuousMap (sphere (0 : ℂ) 1) ℂ) := StarAlgebra.adjoin ℂ
    {ContinuousMap.mk fun x : (sphere (0 : ℂ) 1) => x.val}
  rw [eq_top_iff]
  /- By the Stone-Weierstrass theorem, since `A` is a subalgebra of
  C(∂𝔻, ℂ) that separates points and contains the constant functions,
  `A` is dense in C(∂𝔻, ℂ). -/
  have h_dense : Dense (A : Set (ContinuousMap (sphere (0 : ℂ) 1) ℂ)) := by
    have h_stone_weierstrass : ∀ (A : StarSubalgebra ℂ (ContinuousMap (sphere (0 : ℂ) 1) ℂ)),
      (∀ x y : (sphere (0 : ℂ) 1), x ≠ y → ∃ f ∈ A, f x ≠ f y) →
        (∀ c : ℂ, ContinuousMap.const (sphere (0 : ℂ) 1) c ∈ A) →
          Dense (A : Set (ContinuousMap (sphere (0 : ℂ) 1) ℂ)) := by
      intro A hA hA'
      have := @ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints ℂ
        (sphere (0 : ℂ) 1)
      simp_all [SetLike.ext_iff]
      convert this A _ using 2
      · intro x y hxy
        have hx_norm : ‖(x : ℂ)‖ = 1 := by simp
        have hy_norm : ‖(y : ℂ)‖ = 1 := by simp
        specialize hA x.1 hx_norm y.1 hy_norm; aesop
    apply h_stone_weierstrass A
    · simp
      intro a ha b hb hab; use ContinuousMap.mk (fun x : (sphere (0 : ℂ) 1) => x.val)
      simp_all
      exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · intro c
      convert Subalgebra.algebraMap_mem _ c
  intro x hx
  refine closure_mono ?_ (h_dense x)
  intro f hf
  induction hf using StarAlgebra.adjoin_induction with
  | mem =>
      exact Submodule.subset_span ⟨1, by aesop⟩
  | algebraMap r =>
    refine Submodule.mem_span.mpr ?_
    intro p hp
    have h1 : (1 : C((sphere (0 : ℂ) 1), ℂ)) ∈ p := hp ⟨0, by ext x; simp⟩
    have hsmul : r • (1 : C((sphere (0 : ℂ) 1), ℂ)) ∈ p := p.smul_mem r h1
    convert hsmul using 1
    simp [Algebra.smul_def]
  | add => exact AddMemClass.add_mem ‹_› ‹_›
  | mul =>
    rename_i hx hy
    norm_num at *
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hx hy
    obtain ⟨c₁, hc₁⟩ := hx; obtain ⟨c₂, hc₂⟩ := hy; rw [← hc₁, ← hc₂]
    simp [Finsupp.sum, Finset.sum_mul _ _ _]
    simp [Finset.mul_sum _ _ _]
    refine Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j hj => ?_)
    -- We use that the product of two Laurent polynomials is also a Laurent polynomial.
    have h_prod : (c₁ i • ContinuousMap.mk (fun x : (sphere (0 : ℂ) 1) => x.val ^ i)
      (continuous_zpow_on_unit_circle i)) *
        (c₂ j • ContinuousMap.mk (fun x : (sphere (0 : ℂ) 1) => x.val ^ j)
          (continuous_zpow_on_unit_circle j)) = (c₁ i * c₂ j) • ContinuousMap.mk
            (fun x : (sphere (0 : ℂ) 1) => x.val ^ (i + j)) (
              continuous_zpow_on_unit_circle (i + j)) := by
     -- By the properties of exponents, we can combine the terms on the left-hand side.
      have h_exp : ∀ x : (sphere (0 : ℂ) 1), (x.val ^ i) * (x.val ^ j) = x.val ^ (i + j) := by
        intros x
        have hx : ‖(x : ℂ)‖ = 1 := by simp
        rw [zpow_add₀]
        exact norm_ne_zero_iff.mp (by simp [hx])
      ext x; simp [h_exp, mul_assoc, mul_left_comm, smul_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i + j, ?_⟩)
    ext x; simp; rw [zpow_add₀]
    unfold sphere at x
    obtain ⟨x, hx⟩ := x
    dsimp at hx
    convert (zero_lt_one (α := ℝ)).trans_eq hx.symm using 1
    simp
  | star =>
    rename_i h₁ h₂ h₃
    refine Submodule.span_induction ?_ ?_ ?_ ?_ h₃
    · simp [ContinuousMap.ext_iff]
      intro f n hn; refine Submodule.subset_span ⟨-n, ?_⟩; ext ⟨y, hy⟩
      have hy' : ‖y‖ = 1 := by simpa [sphere, dist_eq_norm] using hy
      simp [hn y hy']
      rw [← hn y hy', Complex.inv_def]
      simp [Complex.normSq_eq_norm_sq, hy']
    · simp [star_zero]
    · simp
      exact fun x y hx hy hx' hy' => Submodule.add_mem _ hx' hy'
    · simp +contextual [Submodule.smul_mem]

/-- If two finite measures agree on a dense subspace of continuous functions,
then they agree on all continuous functions. -/
lemma integral_eq_on_dense_set {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (S : Submodule ℂ C(X, ℂ)) (hS : S.topologicalClosure = ⊤)
    (h : ∀ f ∈ S, ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    ∀ f : C(X, ℂ), ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
  /- Since the integrals are continuous linear maps and agree on a dense subspace,
  they must agree everywhere. -/
  have h_cont : Continuous (fun f : C(X, ℂ) => ∫ x, f x ∂μ) ∧
    Continuous (fun f : C(X, ℂ) => ∫ x, f x ∂ν) := by
    constructor <;> refine continuous_iff_continuousAt.2 fun f => ?_
    · refine tendsto_integral_filter_of_dominated_convergence ?_ ?_ ?_ ?_ ?_
      · refine fun x => (‖f‖ + 1)
      · exact Filter.Eventually.of_forall fun g => g.continuous.aestronglyMeasurable
      · rw [Metric.eventually_nhds_iff]
        refine ⟨1, zero_lt_one, fun g hg => Filter.Eventually.of_forall fun x => ?_⟩
        have := ContinuousMap.norm_coe_le_norm g x
        exact le_trans this (le_trans (norm_le_of_mem_closedBall <| by simpa using hg.le) <|
          by linarith)
      · norm_num
      · exact Filter.Eventually.of_forall fun x => Continuous.tendsto (by continuity) _
    · refine tendsto_integral_filter_of_norm_le_const ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun g => g.continuous.aestronglyMeasurable
      · refine ⟨‖f‖ + 1, ?_⟩
        rw [Metric.eventually_nhds_iff]
        refine ⟨1, zero_lt_one, fun g hg => Filter.Eventually.of_forall fun x => ?_⟩
        have := ContinuousMap.norm_coe_le_norm g x
        exact le_trans this (by linarith [norm_sub_norm_le g f,
          show ‖g - f‖ < 1 from by simpa [dist_eq_norm] using hg])
      · exact Filter.Eventually.of_forall fun x => Continuous.tendsto (by continuity) _
  intro f
  /- Since `S` is dense in `C(X, ℂ)`, there exists a sequence `f_n` in `S`
  such that `f_n` converges to `f` uniformly. -/
  obtain ⟨f_n, hf_n⟩ : ∃ f_n : ℕ → C(X, ℂ), (∀ n, f_n n ∈ S) ∧
    Filter.Tendsto f_n Filter.atTop (nhds f) := by
    have h_dense : f ∈ S.topologicalClosure := by aesop
    exact mem_closure_iff_seq_limit.mp h_dense
  exact tendsto_nhds_unique (h_cont.1.continuousAt.tendsto.comp hf_n.2)
    (h_cont.2.continuousAt.tendsto.comp hf_n.2 |> Filter.Tendsto.congr (by aesop))

/-- If two probability measures on the unit circle have the same moments, then they are equal. -/
lemma measure_eq_of_moments (μ₁ μ₂ : Measure (sphere (0 : ℂ) 1))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h : ∀ n : ℕ, ∫ x, x.val ^ n ∂μ₁ = ∫ x, x.val ^ n ∂μ₂) : μ₁ = μ₂ := by
  -- The integrals of continuous functions with respect to `μ₁` and `μ₂` agree.
  have h_integrals : ∀ f : C((sphere (0 : ℂ) 1), ℂ), ∫ x, f x ∂μ₁ = ∫ x, f x ∂μ₂ := by
    apply_rules [integral_eq_on_dense_set]
    · convert span_moments_dense
    · intro f hf
      have h_integrals : ∀ n : ℤ, ∫ x, x.val ^ n ∂μ₁ = ∫ x, x.val ^ n ∂μ₂ := by
        exact fun n ↦ moments_eq_integers ⟨μ₁, inferInstance⟩ ⟨μ₂, inferInstance⟩ h n
      rw [Finsupp.mem_span_range_iff_exists_finsupp] at hf
      obtain ⟨c, rfl⟩ := hf; simp_all [Finsupp.sum]
      rw [integral_finset_sum, integral_finset_sum]
      · simp only [integral_const_mul, h_integrals]
      · intro n hn; apply_rules [Integrable.const_mul, integrable_const]
        refine Integrable.mono' (g := fun _ => 1) ?_ ?_ ?_
        · norm_num
        · exact Continuous.aestronglyMeasurable (by exact continuous_zpow_on_unit_circle n)
        · filter_upwards with x
          have hx : ‖(x : ℂ)‖ = 1 := by simp
          simp [hx]
      · intro n hn; apply_rules [Integrable.const_mul, integrable_const]
        refine Integrable.mono' (g := fun _ => 1) ?_ ?_ ?_
        · norm_num
        · exact Continuous.aestronglyMeasurable (by exact continuous_zpow_on_unit_circle n)
        · filter_upwards with x
          have hx : ‖(x : ℂ)‖ = 1 := by simp
          simp [hx]
  /- Since the integrals of continuous functions with respect to `μ₁` and `μ₂` agree,
  we can conclude that the measures are equal. -/
  have h_eq : ∀ f : C((sphere (0 : ℂ) 1), ℝ), ∫ x, f x ∂μ₁ = ∫ x, f x ∂μ₂ := by
    intro f
    convert congr_arg Complex.re (h_integrals (ContinuousMap.mk (fun x =>
      f x : (sphere (0 : ℂ) 1) → ℂ)
      (by continuity))) using 1 <;> norm_num [Complex.ext_iff, integral_sub, integral_const_mul]
    · exact Eq.symm (by erw [integral_ofReal] ; norm_cast)
    · exact Eq.symm (by erw [integral_ofReal] ; norm_cast)

  exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ h_eq f.toContinuousMap

/-- If two power series are equal on the unit disc, then their coefficients are equal. -/
lemma coeffs_eq_of_series_eq (c1 c2 : ℕ → ℂ)
    (hc1 : ∃ M, ∀ n, ‖c1 n‖ ≤ M) (hc2 : ∃ M, ∀ n, ‖c2 n‖ ≤ M)
    (h : ∀ z : ℂ, ‖z‖ < 1 → ∑' n, z ^ (n + 1) * c1 n = ∑' n, z ^ (n + 1) * c2 n) : c1 = c2 := by
  /- By the uniqueness of power series expansions, if two power series are equal
  for all `z` in some open set, then their coefficients must be equal. -/
  have h_unique (n : ℕ) : c1 n = c2 n := by
    have h_eq : ∀ z : ℂ, ‖z‖ < 1 → ∑' k, z ^ (k + 1) * (c1 k - c2 k) = 0 := by
      intro z hz; simp_all [mul_sub]
      field_simp
      convert sub_eq_zero.mpr (h z hz) using 1
      rw [← Summable.tsum_sub] ; focus congr ; ext n ; ring
      · /- Since `‖z‖ < 1`, the series Σ_{n=0}^∞ |z|^{n+1} |c1 n| converges by
        the comparison test with the geometric series Σ_{n=0}^∞ |z|^n. -/
        have h_summable : Summable (fun n => ‖z‖ ^ (n + 1) * ‖c1 n‖) := by
          exact Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (norm_nonneg _) _)
            (norm_nonneg _)) (fun n => mul_le_mul_of_nonneg_left (hc1.choose_spec n)
              (pow_nonneg (norm_nonneg _) _))
                (Summable.mul_right _ <| summable_geometric_of_lt_one (norm_nonneg _)
                  hz |> Summable.comp_injective <| Nat.succ_injective)
        exact Summable.of_norm <| by simpa using h_summable
      · have h_summable : Summable (fun n => ‖z‖ ^ (n + 1) * ‖c2 n‖) := by
          exact Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (norm_nonneg _) _)
            (norm_nonneg _))
              (fun n => mul_le_mul_of_nonneg_left (hc2.choose_spec n)
                (pow_nonneg (norm_nonneg _) _))
                  (Summable.mul_right _ <| summable_geometric_of_lt_one (norm_nonneg _)
                    hz |> Summable.comp_injective <| Nat.succ_injective)
        exact Summable.of_norm <| by simpa using h_summable
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    -- Consider the limit of the difference as z approaches 0.
    have h_limit : Filter.Tendsto (fun z : ℂ => (∑' k, z ^ (k + 1) * (c1 k - c2 k)) / z ^ (n + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds ((c1 n - c2 n))) := by
      have h_limit : Filter.Tendsto (fun z : ℂ => (∑' k, z ^ (k + 1) * (c1 k - c2 k)) / z ^ (n + 1))
        (nhdsWithin 0 {0}ᶜ) (nhds ((c1 n - c2 n))) := by
        have h_series : ∀ z : ℂ, ‖z‖ < 1 → (∑' k, z ^ (k + 1) * (c1 k - c2 k)) =
          z^(n + 1) * (c1 n - c2 n) + ∑' k, z^(k + n + 2) * (c1 (k + n + 1) - c2 (k + n + 1)) := by
          intro z hz
          rw [← Summable.sum_add_tsum_nat_add]
          rotate_left
          · use n + 1
          · have h_summable : Summable (fun k => z ^ (k + 1) * (c1 k)) ∧
              Summable (fun k => z ^ (k + 1) * (c2 k)) := by
              have h_summable : Summable (fun k => ‖z‖ ^ (k + 1) * ‖c1 k‖) ∧
                Summable (fun k => ‖z‖ ^ (k + 1) * ‖c2 k‖) := by
                exact ⟨Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (norm_nonneg _) _)
                  (norm_nonneg _)) (fun n => mul_le_mul_of_nonneg_left (hc1.choose_spec n)
                    (pow_nonneg (norm_nonneg _) _))
                      (Summable.mul_right _ <| summable_geometric_of_lt_one (norm_nonneg _)
                      hz |> Summable.comp_injective <| Nat.succ_injective),
                      Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (norm_nonneg _) _)
                      (norm_nonneg _)) (fun n => mul_le_mul_of_nonneg_left (hc2.choose_spec n)
                      (pow_nonneg (norm_nonneg _) _))
                      (Summable.mul_right _ <| summable_geometric_of_lt_one (norm_nonneg _)
                      hz |> Summable.comp_injective <| Nat.succ_injective)⟩
              exact ⟨Summable.of_norm <| by simpa using h_summable.1,
                Summable.of_norm <| by simpa using h_summable.2⟩
            simpa only [mul_sub] using h_summable.1.sub h_summable.2
          · simp [add_assoc, Finset.sum_range_succ]
            exact Finset.sum_eq_zero fun i hi => by rw [ih i (Finset.mem_range.mp hi)] ; ring
        /- We can factor out `z^(k + 1)` from the series and use the fact that the remaining series
        converges uniformly. -/
        have h_factor : Filter.Tendsto (fun z : ℂ => (c1 n - c2 n) + ∑' k,
          z ^ (k + 1) * (c1 (k + n + 1) - c2 (k + n + 1))) (nhdsWithin 0 {0}ᶜ)
            (nhds ((c1 n - c2 n))) := by
          have h_factor : ContinuousOn (fun z : ℂ => ∑' k,
            z ^ (k + 1) * (c1 (k + n + 1) - c2 (k + n + 1))) (Metric.closedBall 0 (1 / 2)) := by
            refine continuousOn_tsum (u := fun k =>
              (1 / 2) ^ (k + 1) * (hc1.choose + hc2.choose)) ?_ ?_ ?_
            · exact fun i => Continuous.continuousOn (by continuity)
            · exact Summable.mul_right _ (summable_geometric_two.mul_right _)
            · norm_num
              exact fun k z hz => mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz _)
                (le_trans (norm_sub_le _ _) (add_le_add (hc1.choose_spec _) (hc2.choose_spec _)))
                  (by positivity) (by positivity)
          exact tendsto_nhdsWithin_of_tendsto_nhds
            (by simpa using
              Filter.Tendsto.add tendsto_const_nhds (h_factor.continuousAt
                (Metric.closedBall_mem_nhds _ <| by norm_num) |> fun h => h.tendsto))
        refine Filter.Tendsto.congr' ?_ h_factor
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
          (Metric.ball_mem_nhds _ zero_lt_one)]
        with z hz hz'; rw[h_series z <| by simpa using hz']; rw[eq_div_iff <| pow_ne_zero _ hz];
          ring_nf
        rw [← tsum_mul_left] ; congr ; ext k ; ring_nf
      convert h_limit using 1
    /- Since the difference is zero for all `z` in a neighborhood of `0`,
    its limit must also be zero. -/
    have h_zero_limit : Filter.Tendsto (fun z : ℂ =>
      (∑' k, z ^ (k + 1) * (c1 k - c2 k)) / z ^ (n + 1)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      exact tendsto_const_nhds.congr' (
        by filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ zero_lt_one)]
            with z hz hz'; aesop)
    exact eq_of_sub_eq_zero (tendsto_nhds_unique h_limit h_zero_limit)
  exact funext h_unique

/-- If two probability measures on the unit circle yield the same Herglotz–Riesz functions,
then they are equal. -/
theorem HerglotzRiesz_representation_uniqueness
    (μ₁ μ₂ : ProbabilityMeasure (sphere (0 : ℂ) 1))
    (h : ∀ z ∈ (ball (0 : ℂ) 1), ∫ x : (sphere (0 : ℂ) 1), (x + z) / (x - z) ∂μ₁ =
      ∫ x : (sphere (0 : ℂ) 1), (x + z) / (x - z) ∂μ₂) :
    μ₁ = μ₂ := by
  let unitCircle := sphere (0 : ℂ) 1
  -- By Lemma `coeffs_eq_of_series_eq`, we can conclude that the coefficients are equal.
  have h_coeffs : ∀ k : ℕ, ∫ x : (sphere (0 : ℂ) 1), star (x.val ^ (k + 1)) ∂μ₁ =
    ∫ x : (sphere (0 : ℂ) 1), star (x.val ^ (k + 1)) ∂μ₂ := by
    /- By Lemma `integral_kernel_expansion`, we can rewrite
    the integrals in terms of the coefficients. -/
    have h_integral_expansion : ∀ z : ℂ, ‖z‖ < 1 →
      (∑' n : ℕ, z ^ (n + 1) * ∫ x : (sphere (0 : ℂ) 1),
      star (x.val ^ (n + 1)) ∂μ₁) = (∑' n : ℕ, z ^ (n + 1) * ∫ x : (sphere (0 : ℂ) 1),
        star (x.val ^ (n + 1)) ∂μ₂) := by
      intro z hz
      have h_integral_expansion : (∫ x : (sphere (0 : ℂ) 1), ((x.val + z) / (x.val - z)) ∂μ₁) =
        1 + 2 * (∑' n : ℕ, z ^ (n + 1) * ∫ x : (sphere (0 : ℂ) 1),
          star (x.val ^ (n + 1)) ∂μ₁) := by
        exact integral_kernel_expansion μ₁ z hz
      have h_integral_expansion' : (∫ x : (sphere (0 : ℂ) 1), ((x.val + z) / (x.val - z)) ∂μ₂) =
        1 + 2 * (∑' n : ℕ, z ^ (n + 1) * ∫ x : (sphere (0 : ℂ) 1),
          star (x.val ^ (n + 1)) ∂μ₂) := by
        exact integral_kernel_expansion μ₂ z hz
      have hz' : z ∈ ball 0 1 := by
        rw [Metric.mem_ball, Complex.dist_eq]
        simp [hz]
      linear_combination' h z hz' / 2 - h_integral_expansion / 2 + h_integral_expansion' / 2
    have h_coeffs : ∀ n : ℕ, ‖∫ x : (sphere (0 : ℂ) 1), star (x.val ^ (n + 1)) ∂μ₁‖ ≤ 1 ∧
      ‖∫ x : (sphere (0 : ℂ) 1), star (x.val ^ (n + 1)) ∂μ₂‖ ≤ 1 := by
      intro n
      refine ⟨?_, ?_⟩ <;> refine le_trans (norm_integral_le_integral_norm _) ?_ <;> norm_num
    apply_rules [coeffs_eq_of_series_eq]
    · exact ⟨1, fun n => h_coeffs n |>.1⟩
    · exact ⟨1, fun n => h_coeffs n |>.2⟩
  have h : μ₁.toMeasure = μ₂.toMeasure := by
    apply measure_eq_of_moments
    apply_rules [measure_eq_of_moments]
    ext (_ | k) <;> simp_all
    convert congr_arg Star.star (h_coeffs k) using 1
    · norm_num [← integral_conj]
    · simp
      rw [← integral_conj]
      simp
  exact Subtype.ext h
