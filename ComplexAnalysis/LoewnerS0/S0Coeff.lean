import LoewnerS0.S0Univalent

/-!
# The second coefficient of maps in `S⁰(𝔹)`

For `f ∈ S⁰(𝔹)` and `P(w) = D²f(0)(w, w)/2` we prove `|⟨P(w), w⟩| ≤ 2‖w‖³`
[Graham–Hamada–Kohr–Kohr 2009]. The proof is an infinitesimal version of the growth theorem
`‖z‖/(1+‖z‖)² ≤ ‖f(z)‖ ≤ ‖z‖/(1-‖z‖)²`: for a unit vector `x` and small `t > 0`,
`‖f(tx)‖² = t² + 2t³ Re ⟨P(x), x⟩ + O(t⁴)`, while `t²/(1-t)⁴ = t² + 4t³ + O(t⁴)` and
`t²/(1+t)⁴ = t² - 4t³ + O(t⁴)`; hence `|Re ⟨P(x), x⟩| ≤ 2`. Rotating `x` by a unimodular
factor `λ` multiplies `⟨P(x), x⟩` by `λ`, which gives the bound for the modulus.

(The stronger norm bound `‖P(w)‖ ≤ 2‖w‖²` is false in dimension two, see
`LoewnerS0.SecondCoeff`.)
-/

open Complex Metric Set Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace LoewnerS0

/-- An elementary estimate: if `|a| ≤ 2 + K t` for all small `t > 0`, then `|a| ≤ 2`. -/
lemma le_of_forall_small {a K δ : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (h : ∀ t, 0 < t → t < δ → a ≤ 2 + K * t) : a ≤ 2 := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set t := min (δ / 2) (ε / (K + 1)) with htdef
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hKt : K * t < ε := by
    have h1 : t ≤ ε / (K + 1) := min_le_right _ _
    have h2 : K * t ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left h1 hK
    have h3 : K * (ε / (K + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  linarith [h t ht0 htδ]

/-- `1/(1-t)⁴ ≤ 1 + 4t + 40t²` for `0 ≤ t ≤ 1/4`. -/
lemma inv_one_sub_pow_four_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) :
    1 / (1 - t) ^ 4 ≤ 1 + 4 * t + 40 * t ^ 2 := by
  have h1 : 0 < 1 - t := by linarith
  rw [div_le_iff₀ (by positivity)]
  have h2 : 0 ≤ t ^ 2 := sq_nonneg t
  have h3 : t ^ 2 ≤ t / 4 := by nlinarith
  nlinarith [mul_nonneg ht0 h2, mul_nonneg h2 h2, mul_nonneg (mul_nonneg ht0 h2) h2,
    mul_nonneg (mul_nonneg h2 h2) h2, mul_nonneg ht0 (mul_nonneg h2 h2)]

/-- `1/(1+t)⁴ ≥ 1 - 4t` for `t ≥ 0`. -/
lemma one_sub_le_inv_one_add_pow_four {t : ℝ} (ht0 : 0 ≤ t) :
    1 - 4 * t ≤ 1 / (1 + t) ^ 4 := by
  rw [le_div_iff₀ (by positivity)]
  have h2 : 0 ≤ t ^ 2 := sq_nonneg t
  nlinarith [mul_nonneg ht0 h2, mul_nonneg h2 h2, mul_nonneg (mul_nonneg ht0 h2) h2,
    mul_nonneg (mul_nonneg h2 h2) h2, mul_nonneg ht0 (mul_nonneg h2 h2),
    mul_nonneg (mul_nonneg ht0 h2) (mul_nonneg h2 h2)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] {f : E → E}

/-- The real part of the second coefficient in a unit direction is at most `2` in modulus. -/
theorem classS0_abs_re_second_coeff_le (hf : f ∈ classS0 E) {x : E} (hx : ‖x‖ = 1) :
    |(⟪x, homPart f 2 x⟫_ℂ).re| ≤ 2 := by
  obtain ⟨h, v, hrep⟩ := hf
  have hN := hrep.isNormalized
  have hgrowth := fun z (hz : z ∈ unitBall E) => classS0_norm_bounds ⟨h, v, hrep⟩ hz
  set P := homPart f 2 x with hP
  -- Taylor expansion of `ζ ↦ f(ζx)` to order 3
  have hφ : DifferentiableOn ℂ (fun ζ : ℂ => f (ζ • x)) (ball 0 1) :=
    hN.differentiableOn.comp (differentiable_id.smul_const x).differentiableOn
      (mapsTo_smul_unitBall hx.le)
  obtain ⟨C₀, ε, hε, hT₀⟩ := exists_taylor_bound hφ (ball_mem_nhds 0 one_pos) 3
  set C := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hT : ∀ ζ : ℂ, ‖ζ‖ < ε → ‖f (ζ • x) - ∑ k ∈ Finset.range 3,
      ((k.factorial : ℂ)⁻¹ * ζ ^ k) • iteratedDeriv k (fun ζ : ℂ => f (ζ • x)) 0‖ ≤
        C * ‖ζ‖ ^ 3 := fun ζ hζ =>
    (hT₀ ζ hζ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  simp only [taylor_sum_three] at hT
  have hd1 : iteratedDeriv 1 (fun ζ : ℂ => f (ζ • x)) 0 = x := by
    rw [iteratedDeriv_comp_smul isOpen_unitBall zero_mem_unitBall hN.differentiableOn x 1]
    simp [hN.fderiv_zero]
  have hd2 : ((2 : ℂ)⁻¹ * 1) • iteratedDeriv 2 (fun ζ : ℂ => f (ζ • x)) 0 = P := by
    rw [iteratedDeriv_comp_smul isOpen_unitBall zero_mem_unitBall hN.differentiableOn x 2, hP,
      homPart]
    norm_num
  set a := (⟪x, P⟫_ℂ).re with ha
  set p := ‖P‖ with hp
  set K := p ^ 2 + 2 * C * (1 + p) + C ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set δ := min ε (1 / 4) with hδ
  have hδ0 : 0 < δ := lt_min hε (by norm_num)
  -- the expansion `f(tx) = t x + t² P + R` with `‖R‖ ≤ C t³`, and its consequence for `‖f(tx)‖²`
  have hexp : ∀ t : ℝ, 0 < t → t < δ →
      |‖f ((t : ℂ) • x)‖ ^ 2 - (t ^ 2 + 2 * t ^ 3 * a)| ≤ K * t ^ 4 := by
    intro t ht htδ
    have htε : ‖(t : ℂ)‖ < ε := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      exact lt_of_lt_of_le htδ (min_le_left _ _)
    have ht1 : t ≤ 1 := by linarith [min_le_right ε (1 / 4 : ℝ)]
    have hR := hT t htε
    rw [zero_smul, hN.map_zero, zero_add, hd1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht] at hR
    have hR' : ((2 : ℂ)⁻¹ * (t : ℂ) ^ 2) • iteratedDeriv 2 (fun ζ : ℂ => f (ζ • x)) 0 =
        (t : ℂ) ^ 2 • P := by
      rw [← hd2, smul_smul]; ring_nf
    rw [hR'] at hR
    set R := f ((t : ℂ) • x) - ((t : ℂ) • x + (t : ℂ) ^ 2 • P) with hRdef
    have hfx : f ((t : ℂ) • x) = (t : ℂ) • x + (t : ℂ) ^ 2 • P + R := by rw [hRdef]; abel
    set y := (t : ℂ) • x + (t : ℂ) ^ 2 • P with hy
    have hy2 : ‖y‖ ^ 2 = t ^ 2 + 2 * t ^ 3 * a + t ^ 4 * p ^ 2 := by
      have e1 : ‖y‖ ^ 2 = (⟪y, y⟫_ℂ).re := by
        simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) y).symm
      rw [e1, hy]
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        Complex.add_re, map_pow, Complex.conj_ofReal]
      have e2 : (⟪x, x⟫_ℂ) = 1 := by rw [inner_self_eq_norm_sq_to_K, hx]; simp
      have e3 : (⟪P, P⟫_ℂ).re = p ^ 2 := by
        simpa using inner_self_eq_norm_sq (𝕜 := ℂ) P
      have e4 : (⟪P, x⟫_ℂ).re = a := by rw [ha, ← inner_conj_symm, Complex.conj_re]
      rw [e2]
      simp only [← Complex.ofReal_pow, Complex.re_ofReal_mul]
      simp only [Complex.add_re, Complex.re_ofReal_mul, mul_one, Complex.ofReal_re]
      rw [e3, e4, ← ha]
      ring
    have hyn : ‖y‖ ≤ t + t ^ 2 * p := by
      rw [hy]
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_smul, norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
        hx, mul_one]
    have hfx2 : ‖f ((t : ℂ) • x)‖ ^ 2 = ‖y‖ ^ 2 + 2 * (⟪y, R⟫_ℂ).re + ‖R‖ ^ 2 := by
      rw [hfx]
      have := @norm_add_sq ℂ E _ _ _ y R
      simpa using this
    have hcross : |2 * (⟪y, R⟫_ℂ).re| ≤ 2 * ((t + t ^ 2 * p) * (C * t ^ 3)) := by
      rw [abs_mul, abs_two]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
      exact mul_le_mul hyn hR (norm_nonneg _) (by positivity)
    have hRR : ‖R‖ ^ 2 ≤ (C * t ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR 2
    rw [hfx2, hy2]
    have ht4 : t ^ 5 ≤ t ^ 4 := pow_le_pow_of_le_one ht.le ht1 (by norm_num)
    have ht6 : t ^ 6 ≤ t ^ 4 := pow_le_pow_of_le_one ht.le ht1 (by norm_num)
    have hp0 : 0 ≤ p := norm_nonneg _
    rw [abs_le] at hcross ⊢
    have e5 : (t + t ^ 2 * p) * (C * t ^ 3) = C * t ^ 4 + C * p * t ^ 5 := by ring
    have e6 : (C * t ^ 3) ^ 2 = C ^ 2 * t ^ 6 := by ring
    have i1 : C * p * t ^ 5 ≤ C * p * t ^ 4 := mul_le_mul_of_nonneg_left ht4 (mul_nonneg hC0 hp0)
    have i2 : C ^ 2 * t ^ 6 ≤ C ^ 2 * t ^ 4 := mul_le_mul_of_nonneg_left ht6 (sq_nonneg C)
    have i3 : 0 ≤ p ^ 2 * t ^ 4 := by positivity
    have i4 : 0 ≤ ‖R‖ ^ 2 := by positivity
    have i5 : 0 ≤ C * p * t ^ 5 := by positivity
    have i6 : 0 ≤ C ^ 2 * t ^ 4 := by positivity
    have i7 : 0 ≤ C * p * t ^ 4 := by positivity
    have eK : K * t ^ 4 = p ^ 2 * t ^ 4 + 2 * (C * t ^ 4) + 2 * (C * p * t ^ 4) +
        C ^ 2 * t ^ 4 := by rw [hK]; ring
    rw [e5] at hcross
    rw [e6] at hRR
    constructor
    · nlinarith
    · nlinarith
  -- the growth theorem
  have hgr : ∀ t : ℝ, 0 < t → t < δ →
      t ^ 2 / (1 + t) ^ 4 ≤ ‖f ((t : ℂ) • x)‖ ^ 2 ∧
        ‖f ((t : ℂ) • x)‖ ^ 2 ≤ t ^ 2 / (1 - t) ^ 4 := by
    intro t ht htδ
    have ht1 : t < 1 := by linarith [min_le_right ε (1 / 4 : ℝ)]
    have hz : ((t : ℂ) • x) ∈ unitBall E := by
      rw [mem_unitBall, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, hx,
        mul_one]
      exact ht1
    have hn : ‖(t : ℂ) • x‖ = t := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, hx, mul_one]
    obtain ⟨h1, h2⟩ := hgrowth _ hz
    rw [hn] at h1 h2
    constructor
    · have := pow_le_pow_left₀ (by positivity) h1 2
      rw [div_pow, ← pow_mul] at this
      exact this
    · have := pow_le_pow_left₀ (by positivity) h2 2
      rw [div_pow, ← pow_mul] at this
      exact this
  -- upper bound for `a`
  have hupper : a ≤ 2 := by
    refine le_of_forall_small hδ0 (K := (40 + K) / 2) (by positivity) fun t ht htδ => ?_
    have ht4 : t ≤ 1 / 4 := le_trans htδ.le (min_le_right _ _)
    obtain ⟨-, hup⟩ := hgr t ht htδ
    have he := (abs_le.mp (hexp t ht htδ)).1
    have hq := inv_one_sub_pow_four_le ht.le ht4
    have h1 : t ^ 2 / (1 - t) ^ 4 ≤ t ^ 2 * (1 + 4 * t + 40 * t ^ 2) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hq (sq_nonneg t)
    have h2 : 2 * t ^ 3 * a ≤ 4 * t ^ 3 + (40 + K) * t ^ 4 := by nlinarith
    have ht3 : 0 < t ^ 3 := by positivity
    have : 2 * a ≤ 4 + (40 + K) * t := by
      have h3 : t ^ 3 * (2 * a) ≤ t ^ 3 * (4 + (40 + K) * t) := by nlinarith
      exact le_of_mul_le_mul_left h3 ht3
    linarith
  -- lower bound for `a`
  have hlower : -a ≤ 2 := by
    refine le_of_forall_small hδ0 (K := K / 2) (by positivity) fun t ht htδ => ?_
    obtain ⟨hlo, -⟩ := hgr t ht htδ
    have he := (abs_le.mp (hexp t ht htδ)).2
    have hq := one_sub_le_inv_one_add_pow_four ht.le
    have h1 : t ^ 2 * (1 - 4 * t) ≤ t ^ 2 / (1 + t) ^ 4 := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hq (sq_nonneg t)
    have ht3 : 0 < t ^ 3 := by positivity
    have h3 : t ^ 3 * (-(2 * a)) ≤ t ^ 3 * (4 + K * t) := by nlinarith
    have : -(2 * a) ≤ 4 + K * t := le_of_mul_le_mul_left h3 ht3
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- **Second coefficient bound for `S⁰(𝔹)`** [Graham–Hamada–Kohr–Kohr 2009]:
`|⟨D²f(0)(w, w)/2, w⟩| ≤ 2‖w‖³`. -/
theorem classS0_norm_inner_second_coeff_le (hf : f ∈ classS0 E) (w : E) :
    ‖⟪w, (2 : ℂ)⁻¹ • iteratedFDeriv ℂ 2 f 0 (fun _ => w)⟫_ℂ‖ ≤ 2 * ‖w‖ ^ 3 := by
  have hP : ∀ y : E, (2 : ℂ)⁻¹ • iteratedFDeriv ℂ 2 f 0 (fun _ => y) = homPart f 2 y := by
    intro y; rw [homPart]; norm_num
  rw [hP]
  -- unit vectors first
  have hunit : ∀ u : E, ‖u‖ = 1 → ‖⟪u, homPart f 2 u⟫_ℂ‖ ≤ 2 := by
    intro u hu
    set A := ⟪u, homPart f 2 u⟫_ℂ with hA
    rcases eq_or_ne A 0 with h0 | h0
    · rw [h0, norm_zero]; norm_num
    set l : ℂ := (starRingEnd ℂ) A / (‖A‖ : ℂ) with hl
    have hAn : (‖A‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr h0).ne'
    have hl1 : ‖l‖ = 1 := by
      rw [hl, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_pos_iff.mpr h0).ne']
    have hx : ‖l • u‖ = 1 := by rw [norm_smul, hl1, hu, one_mul]
    have key := classS0_abs_re_second_coeff_le hf hx
    have hrot : ⟪l • u, homPart f 2 (l • u)⟫_ℂ = (‖A‖ : ℂ) := by
      rw [homPart_smul, inner_smul_left, inner_smul_right, ← hA]
      have hll : (starRingEnd ℂ) l * l = 1 := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hl1]; norm_num
      calc (starRingEnd ℂ) l * (l ^ 2 * A) = ((starRingEnd ℂ) l * l) * (l * A) := by ring
        _ = l * A := by rw [hll, one_mul]
        _ = (‖A‖ : ℂ) := by
            rw [hl, div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
            push_cast
            field_simp
    rw [hrot, Complex.ofReal_re, abs_of_nonneg (norm_nonneg _)] at key
    exact key
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [homPart_zero_right f two_ne_zero]; simp
  set r := ‖w‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr hw0
  set u : E := ((r : ℂ)⁻¹) • w with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      inv_mul_cancel₀ hr0.ne']
  have hwu : w = (r : ℂ) • u := by
    rw [hudef, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hr0.ne'), one_smul]
  rw [hwu, homPart_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, norm_mul,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have := hunit u hu
  calc r * (r ^ 2 * ‖⟪u, homPart f 2 u⟫_ℂ‖) ≤ r * (r ^ 2 * 2) := by gcongr
    _ = 2 * r ^ 3 := by ring

end LoewnerS0
