import LoewnerS0.Cex.Positivity
import LoewnerS0.Sphere
import LoewnerS0.Unitary

/-!
# The generator `h` of the counterexample belongs to `M(𝔹²)`

`H(w) = N(w)/(1 - r w₁)` with the polynomial map `N` of `LoewnerS0.Cex.NT` and `r = 19999/20000`,
and `h(z) = U* H(U z)` with the rotation `U = (1/221) [[220, 21], [-21, 220]]` (Theorem 1.1 of
`disproof_starlike.tex`). By `Ffun_ge` and the sphere criterion, `H ∈ M(𝔹²)`, and `h ∈ M(𝔹²)`
by unitary invariance.

(Coordinates are numbered `0, 1` here, `w = (w 0, w 1)`; in the paper they are `w₁, w₂`.)
-/

open Complex Metric Set Filter Asymptotics
open scoped InnerProductSpace Topology

noncomputable section

namespace LoewnerS0.Cex

/-- `ℂ²` with the Euclidean norm -/
abbrev E2 := EuclideanSpace ℂ (Fin 2)

/-- the standard basis vector `e₀` -/
abbrev ea : E2 := EuclideanSpace.single 0 1

/-- the standard basis vector `e₁` -/
abbrev eb : E2 := EuclideanSpace.single 1 1

lemma E2_eq (w : E2) : w = w 0 • ea + w 1 • eb := by
  ext i
  fin_cases i <;> simp

lemma E2_norm_sq (w : E2) : ‖w‖ ^ 2 = ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

lemma E2_inner (w v : E2) :
    ⟪w, v⟫_ℂ = starRingEnd ℂ (w 0) * v 0 + starRingEnd ℂ (w 1) * v 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [mul_comm]

lemma E2_norm_le (w : E2) : ‖w‖ ≤ ‖w 0‖ + ‖w 1‖ := by
  have h := E2_norm_sq w
  have h0 := norm_nonneg (w 0)
  have h1 := norm_nonneg (w 1)
  nlinarith [norm_nonneg w, sq_nonneg (‖w‖ - ‖w 0‖ - ‖w 1‖)]

lemma differentiable_coord (i : Fin 2) : Differentiable ℂ (fun w : E2 => w i) :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) i).differentiable

/-! ### The polynomial map `N` -/

lemma differentiable_N1of : ∀ l : List (ℕ × ℕ × ℕ × ℤ),
    Differentiable ℂ (fun w : E2 => N1of l (w 0) (w 1))
  | [] => by simp [N1of]
  | (comp, a, b, c) :: rest => by
    simp only [N1of]
    refine Differentiable.add ?_ (differentiable_N1of rest)
    split_ifs
    · exact ((differentiable_const _).mul ((differentiable_coord 0).pow a)).mul
        ((differentiable_coord 1).pow b)
    · exact differentiable_const _

lemma differentiable_N2of : ∀ l : List (ℕ × ℕ × ℕ × ℤ),
    Differentiable ℂ (fun w : E2 => N2of l (w 0) (w 1))
  | [] => by simp [N2of]
  | (comp, a, b, c) :: rest => by
    simp only [N2of]
    refine Differentiable.add ?_ (differentiable_N2of rest)
    split_ifs
    · exact differentiable_const _
    · exact ((differentiable_const _).mul ((differentiable_coord 0).pow a)).mul
        ((differentiable_coord 1).pow b)

/-- the sum of the absolute values of the coefficients -/
def coefSum (l : List (ℕ × ℕ × ℕ × ℤ)) : ℝ := (l.map fun t => |(t.2.2.2 : ℝ)| / 10000).sum

lemma coefSum_nonneg (l : List (ℕ × ℕ × ℕ × ℤ)) : 0 ≤ coefSum l := by
  unfold coefSum
  exact List.sum_nonneg fun x hx => by
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    positivity

lemma norm_term_le (m a b : ℕ) (hm : m ≤ a + b) (c : ℤ) (z₁ z₂ : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (h1 : ‖z₁‖ ≤ ρ) (h2 : ‖z₂‖ ≤ ρ) :
    ‖(c : ℂ) / 10000 * z₁ ^ a * z₂ ^ b‖ ≤ |(c : ℝ)| / 10000 * ρ ^ m := by
  rw [norm_mul, norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_intCast]
  have e1 : ‖z₁‖ ^ a ≤ ρ ^ a := pow_le_pow_left₀ (norm_nonneg _) h1 a
  have e2 : ‖z₂‖ ^ b ≤ ρ ^ b := pow_le_pow_left₀ (norm_nonneg _) h2 b
  have e3 : ρ ^ (a + b) ≤ ρ ^ m := pow_le_pow_of_le_one hρ hρ1 hm
  have e4 : ‖z₁‖ ^ a * ‖z₂‖ ^ b ≤ ρ ^ m := by
    calc ‖z₁‖ ^ a * ‖z₂‖ ^ b ≤ ρ ^ a * ρ ^ b :=
          mul_le_mul e1 e2 (by positivity) (by positivity)
      _ = ρ ^ (a + b) := (pow_add ρ a b).symm
      _ ≤ ρ ^ m := e3
  have : ‖(10000 : ℂ)‖ = 10000 := by norm_num
  rw [this, mul_assoc]
  have hc : 0 ≤ |(c : ℝ)| / 10000 := by positivity
  calc |(c : ℝ)| / 10000 * (‖z₁‖ ^ a * ‖z₂‖ ^ b) ≤ |(c : ℝ)| / 10000 * ρ ^ m :=
        mul_le_mul_of_nonneg_left e4 hc
    _ = _ := rfl

lemma norm_N1of_le (m : ℕ) : ∀ l : List (ℕ × ℕ × ℕ × ℤ), (∀ t ∈ l, m ≤ t.2.1 + t.2.2.1) →
    ∀ (z₁ z₂ : ℂ) (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 → ‖z₁‖ ≤ ρ → ‖z₂‖ ≤ ρ →
      ‖N1of l z₁ z₂‖ ≤ coefSum l * ρ ^ m
  | [], _, z₁, z₂, ρ, _, _, _, _ => by simp [N1of, coefSum]
  | (comp, a, b, c) :: rest, hl, z₁, z₂, ρ, hρ, hρ1, h1, h2 => by
    simp only [N1of, coefSum, List.map_cons, List.sum_cons]
    have ih := norm_N1of_le m rest (fun t ht => hl t (List.mem_cons_of_mem _ ht)) z₁ z₂ ρ hρ
      hρ1 h1 h2
    have hm := hl (comp, a, b, c) (List.mem_cons_self)
    have ht : ‖(if comp = 1 then (c : ℂ) / 10000 * z₁ ^ a * z₂ ^ b else 0)‖ ≤
        |(c : ℝ)| / 10000 * ρ ^ m := by
      split_ifs
      · exact norm_term_le m a b hm c z₁ z₂ ρ hρ hρ1 h1 h2
      · simp only [norm_zero]; positivity
    calc _ ≤ ‖(if comp = 1 then (c : ℂ) / 10000 * z₁ ^ a * z₂ ^ b else 0)‖ +
          ‖N1of rest z₁ z₂‖ := norm_add_le _ _
      _ ≤ |(c : ℝ)| / 10000 * ρ ^ m + coefSum rest * ρ ^ m := add_le_add ht ih
      _ = _ := by simp [coefSum]; ring

lemma norm_N2of_le (m : ℕ) : ∀ l : List (ℕ × ℕ × ℕ × ℤ), (∀ t ∈ l, m ≤ t.2.1 + t.2.2.1) →
    ∀ (z₁ z₂ : ℂ) (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 → ‖z₁‖ ≤ ρ → ‖z₂‖ ≤ ρ →
      ‖N2of l z₁ z₂‖ ≤ coefSum l * ρ ^ m
  | [], _, z₁, z₂, ρ, _, _, _, _ => by simp [N2of, coefSum]
  | (comp, a, b, c) :: rest, hl, z₁, z₂, ρ, hρ, hρ1, h1, h2 => by
    simp only [N2of, coefSum, List.map_cons, List.sum_cons]
    have ih := norm_N2of_le m rest (fun t ht => hl t (List.mem_cons_of_mem _ ht)) z₁ z₂ ρ hρ
      hρ1 h1 h2
    have hm := hl (comp, a, b, c) (List.mem_cons_self)
    have ht : ‖(if comp = 1 then 0 else (c : ℂ) / 10000 * z₁ ^ a * z₂ ^ b)‖ ≤
        |(c : ℝ)| / 10000 * ρ ^ m := by
      split_ifs
      · simp only [norm_zero]; positivity
      · exact norm_term_le m a b hm c z₁ z₂ ρ hρ hρ1 h1 h2
    calc _ ≤ ‖(if comp = 1 then 0 else (c : ℂ) / 10000 * z₁ ^ a * z₂ ^ b)‖ +
          ‖N2of rest z₁ z₂‖ := norm_add_le _ _
      _ ≤ |(c : ℝ)| / 10000 * ρ ^ m + coefSum rest * ρ ^ m := add_le_add ht ih
      _ = _ := by simp [coefSum]; ring

/-- the terms of `N` of degree `≥ 2` -/
def NTrest : List (ℕ × ℕ × ℕ × ℤ) := NT.drop 2

lemma NT_eq : NT = (1, 1, 0, 10000) :: (2, 0, 1, 10000) :: NTrest := rfl

lemma NTrest_deg : ∀ t ∈ NTrest, 2 ≤ t.2.1 + t.2.2.1 := by decide

lemma N1_eq (z₁ z₂ : ℂ) : N1 z₁ z₂ = z₁ + N1of NTrest z₁ z₂ := by
  rw [N1, NT_eq]
  simp [N1of]

lemma N2_eq (z₁ z₂ : ℂ) : N2 z₁ z₂ = z₂ + N2of NTrest z₁ z₂ := by
  rw [N2, NT_eq]
  simp [N2of]

/-- the numerator `N : ℂ² → ℂ²` -/
def Nmap (w : E2) : E2 := N1 (w 0) (w 1) • ea + N2 (w 0) (w 1) • eb

@[simp] lemma Nmap_apply_zero (w : E2) : Nmap w 0 = N1 (w 0) (w 1) := by simp [Nmap]

@[simp] lemma Nmap_apply_one (w : E2) : Nmap w 1 = N2 (w 0) (w 1) := by simp [Nmap]

lemma differentiable_Nmap : Differentiable ℂ Nmap := by
  unfold Nmap N1 N2
  exact ((differentiable_N1of NT).smul_const _).add ((differentiable_N2of NT).smul_const _)

/-- the part of `N` of degree `≥ 2` -/
def Nrem (w : E2) : E2 := N1of NTrest (w 0) (w 1) • ea + N2of NTrest (w 0) (w 1) • eb

lemma Nmap_eq (w : E2) : Nmap w = w + Nrem w := by
  ext i
  fin_cases i <;> simp [Nmap, Nrem, N1_eq, N2_eq]

lemma norm_Nrem_le (w : E2) (hw : ‖w‖ ≤ 1) : ‖Nrem w‖ ≤ 2 * coefSum NTrest * ‖w‖ ^ 2 := by
  have h0 := PiLp.norm_apply_le w 0
  have h1 := PiLp.norm_apply_le w 1
  have a1 := norm_N1of_le 2 NTrest NTrest_deg (w 0) (w 1) ‖w‖ (norm_nonneg _) hw h0 h1
  have a2 := norm_N2of_le 2 NTrest NTrest_deg (w 0) (w 1) ‖w‖ (norm_nonneg _) hw h0 h1
  calc ‖Nrem w‖ ≤ ‖N1of NTrest (w 0) (w 1) • ea‖ + ‖N2of NTrest (w 0) (w 1) • eb‖ :=
        norm_add_le _ _
    _ = ‖N1of NTrest (w 0) (w 1)‖ + ‖N2of NTrest (w 0) (w 1)‖ := by simp [norm_smul]
    _ ≤ 2 * coefSum NTrest * ‖w‖ ^ 2 := by linarith

/-- a function bounded by `C ‖w‖²` near `0` has derivative `0` at `0` -/
lemma hasFDerivAt_zero_of_sq {F : E2 → E2} {C : ℝ}
    (hF : ∀ w : E2, ‖w‖ ≤ 1 → ‖F w‖ ≤ C * ‖w‖ ^ 2) : HasFDerivAt F (0 : E2 →L[ℂ] E2) 0 := by
  have hF0 : F 0 = 0 := by
    have := hF 0 (by simp)
    simpa using this
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, hF0, sub_zero]
  have hO : F =O[𝓝 0] fun w : E2 => ‖w‖ ^ 2 := by
    refine IsBigO.of_bound C ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : E2) one_pos] with w hw
    rw [mem_closedBall_zero_iff] at hw
    calc ‖F w‖ ≤ C * ‖w‖ ^ 2 := hF w hw
      _ ≤ C * ‖‖w‖ ^ 2‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have e : (fun h : E2 => F h - (0 : E2 →L[ℂ] E2) h) = F := by funext h; simp
  rw [e]
  exact hO.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)

lemma hasFDerivAt_Nmap : HasFDerivAt Nmap (ContinuousLinearMap.id ℂ E2) 0 := by
  have h1 : HasFDerivAt Nrem (0 : E2 →L[ℂ] E2) 0 :=
    hasFDerivAt_zero_of_sq (C := 2 * coefSum NTrest) norm_Nrem_le
  have h2 := (hasFDerivAt_id (𝕜 := ℂ) (0 : E2)).add h1
  rw [add_zero] at h2
  have : Nmap = fun w => id w + Nrem w := funext fun w => Nmap_eq w
  rw [this]
  exact h2

lemma Nmap_zero : Nmap 0 = 0 := by
  rw [Nmap_eq, zero_add]
  have := norm_Nrem_le 0 (by simp)
  simpa using this

/-! ### The generator `H` -/

/-- the generator `H(w) = N(w)/(1 - r w₁)` -/
def Hgen (w : E2) : E2 := (1 - (rr : ℂ) * w 0)⁻¹ • Nmap w

lemma rr_pos : (0 : ℝ) < rr := by norm_num [rr]

lemma rr_lt_one : rr < 1 := by norm_num [rr]

lemma one_sub_ne_zero (w : E2) (hw : ‖w‖ < 20000 / 19999) : 1 - (rr : ℂ) * w 0 ≠ 0 := by
  intro h
  have h1 : (rr : ℂ) * w 0 = 1 := by linear_combination -h
  have h2 : ‖(rr : ℂ) * w 0‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos rr_pos] at h2
  have h3 := PiLp.norm_apply_le w 0
  have : rr * ‖w 0‖ < 1 := by
    calc rr * ‖w 0‖ ≤ rr * ‖w‖ := mul_le_mul_of_nonneg_left h3 rr_pos.le
      _ < rr * (20000 / 19999) := mul_lt_mul_of_pos_left hw rr_pos
      _ = 1 := by norm_num [rr]
  linarith

lemma differentiableOn_Hgen : DifferentiableOn ℂ Hgen (ball 0 (20000 / 19999)) := by
  intro w hw
  rw [mem_ball_zero_iff] at hw
  apply DifferentiableAt.differentiableWithinAt
  show DifferentiableAt ℂ (fun w : E2 => (1 - (rr : ℂ) * w 0)⁻¹ • Nmap w) w
  apply DifferentiableAt.fun_smul _ (differentiable_Nmap w)
  have hf : DifferentiableAt ℂ (fun i : E2 => 1 - (rr : ℂ) * i 0) w :=
    (differentiableAt_const _).sub ((differentiableAt_const _).mul ((differentiable_coord 0) w))
  exact hf.fun_inv (one_sub_ne_zero w hw)

lemma Hgen_zero : Hgen 0 = 0 := by simp [Hgen, Nmap_zero]

lemma hasFDerivAt_Hgen : HasFDerivAt Hgen (ContinuousLinearMap.id ℂ E2) 0 := by
  have hg : DifferentiableAt ℂ (fun w : E2 => (1 - (rr : ℂ) * w 0)⁻¹) 0 := by
    have hf : DifferentiableAt ℂ (fun i : E2 => 1 - (rr : ℂ) * i 0) 0 :=
      (differentiableAt_const _).sub ((differentiableAt_const _).mul ((differentiable_coord 0) 0))
    exact hf.fun_inv (by simp)
  have h := hg.hasFDerivAt.smul hasFDerivAt_Nmap
  have e : Hgen = (fun w : E2 => (1 - (rr : ℂ) * w 0)⁻¹) • Nmap := by
    funext w; rfl
  rw [e]
  convert h using 1
  rw [Nmap_zero]
  simp

lemma fderiv_Hgen : fderiv ℂ Hgen 0 = ContinuousLinearMap.id ℂ E2 := hasFDerivAt_Hgen.fderiv

/-- `Re ⟨H(w), w⟩ = F(w)/|1 - r w₁|²` -/
lemma re_inner_Hgen (w : E2) :
    (⟪w, Hgen w⟫_ℂ).re = Ffun (w 0) (w 1) / normSq (1 - (rr : ℂ) * w 0) := by
  set D : ℂ := 1 - (rr : ℂ) * w 0 with hD
  have hinner : ⟪w, Hgen w⟫_ℂ = D⁻¹ * (N1 (w 0) (w 1) * starRingEnd ℂ (w 0) +
      N2 (w 0) (w 1) * starRingEnd ℂ (w 1)) := by
    rw [E2_inner]
    simp only [Hgen, PiLp.smul_apply, smul_eq_mul, Nmap_apply_zero, Nmap_apply_one]
    ring
  have hconjD : starRingEnd ℂ D = 1 - (rr : ℂ) * starRingEnd ℂ (w 0) := by
    simp [hD, Complex.conj_ofReal]
  rw [hinner, Complex.inv_def, Ffun, ← hconjD]
  rw [show starRingEnd ℂ D * ((normSq D)⁻¹ : ℝ) * (N1 (w 0) (w 1) * starRingEnd ℂ (w 0) +
      N2 (w 0) (w 1) * starRingEnd ℂ (w 1)) = (((normSq D)⁻¹ : ℝ) : ℂ) *
      ((N1 (w 0) (w 1) * starRingEnd ℂ (w 0) + N2 (w 0) (w 1) * starRingEnd ℂ (w 1)) *
        starRingEnd ℂ D) by ring]
  rw [Complex.re_ofReal_mul, div_eq_inv_mul]

lemma re_inner_Hgen_ge (w : E2) (hw : ‖w‖ = 1) : 1 / (4 * 10 ^ 6) ≤ (⟪w, Hgen w⟫_ℂ).re := by
  have hne := one_sub_ne_zero w (by rw [hw]; norm_num)
  rw [re_inner_Hgen w]
  have hsph : normSq (w 0) + normSq (w 1) = 1 := by
    have := E2_norm_sq w
    rw [hw, one_pow] at this
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    linarith
  have hF := Ffun_ge (w 0) (w 1) hsph
  have hpos : 0 < normSq (1 - (rr : ℂ) * w 0) := Complex.normSq_pos.mpr hne
  have hle : normSq (1 - (rr : ℂ) * w 0) ≤ 4 := by
    rw [Complex.normSq_eq_norm_sq]
    have h0 : ‖w 0‖ ≤ 1 := hw ▸ PiLp.norm_apply_le w 0
    have : ‖1 - (rr : ℂ) * w 0‖ ≤ 2 := by
      calc ‖1 - (rr : ℂ) * w 0‖ ≤ ‖(1 : ℂ)‖ + ‖(rr : ℂ) * w 0‖ := norm_sub_le _ _
        _ = 1 + rr * ‖w 0‖ := by
          rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos rr_pos]
        _ ≤ 2 := by nlinarith [rr_lt_one, rr_pos, norm_nonneg (w 0)]
    nlinarith [norm_nonneg (1 - (rr : ℂ) * w 0)]
  rw [le_div_iff₀ hpos]
  nlinarith

/-- **`H ∈ M(𝔹²)`.** -/
theorem isCaratheodory_Hgen : IsCaratheodory Hgen :=
  isCaratheodory_of_sphere (R := 20000 / 19999) (by norm_num) differentiableOn_Hgen Hgen_zero
    fderiv_Hgen (c := 1 / (4 * 10 ^ 6)) (by norm_num) re_inner_Hgen_ge

/-! ### The rotation `U` and the generator `h` -/

/-- `U z = (1/221) (220 z₁ + 21 z₂, -21 z₁ + 220 z₂)` -/
def Ufun (z : E2) : E2 := !₂[(220 * z 0 + 21 * z 1) / 221, (-21 * z 0 + 220 * z 1) / 221]

/-- `Uᵀ w = (1/221) (220 w₁ - 21 w₂, 21 w₁ + 220 w₂)` -/
def Uinv (w : E2) : E2 := !₂[(220 * w 0 - 21 * w 1) / 221, (21 * w 0 + 220 * w 1) / 221]

/-- `U` as a linear equivalence -/
def Ulin : E2 ≃ₗ[ℂ] E2 where
  toFun := Ufun
  invFun := Uinv
  map_add' x y := by
    ext i; fin_cases i <;> simp [Ufun] <;> ring
  map_smul' c x := by
    ext i; fin_cases i <;> simp [Ufun] <;> ring
  left_inv z := by
    ext i; fin_cases i <;> simp [Ufun, Uinv] <;> ring
  right_inv w := by
    ext i; fin_cases i <;> simp [Ufun, Uinv] <;> ring

/-- the rotation `U` as a unitary map of `ℂ²` -/
def Uiso : E2 ≃ₗᵢ[ℂ] E2 :=
  Ulin.isometryOfInner fun x y => by
    simp only [E2_inner]
    simp [Ulin, Ufun, map_div₀, map_add, map_mul, map_neg, map_ofNat]
    ring

@[simp] lemma Uiso_apply (z : E2) : Uiso z = Ufun z := rfl

@[simp] lemma Uiso_symm_apply (w : E2) : Uiso.symm w = Uinv w := rfl

/-- **The generator of Theorem 1.1**: `h(z) = U* H(U z)`. -/
def hgen (z : E2) : E2 := Uiso.symm (Hgen (Uiso z))

/-- **`h ∈ M(𝔹²)`.** -/
theorem isCaratheodory_hgen : IsCaratheodory hgen :=
  isCaratheodory_Hgen.conj Uiso

end LoewnerS0.Cex
