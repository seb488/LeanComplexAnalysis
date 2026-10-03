import LoewnerS0.Cex.Generator

/-!
# The Taylor expansion of the generator up to order 3

We write `H(w) = w + B_H(w, w) + C_H(w, w, w) + O(‖w‖⁴)` with explicit continuous bilinear and
trilinear maps `B_H`, `C_H` (Section 4 of `disproof_starlike.tex`: `H^[2] = N^[2] + r w₁ w`,
`H^[3] = N^[3] + r w₁ N^[2] + r² w₁² w`), prove the remainder estimate, and transport everything
to `h(z) = U* H(U z)`.
-/

open Complex Metric Set Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace LoewnerS0.Cex

/-! ### Elementary multilinear maps on `ℂ²` -/

/-- the coordinate projection `w ↦ wᵢ` -/
abbrev proj (i : Fin 2) : E2 →L[ℂ] ℂ := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) i

/-- the bilinear monomial `(v₀, v₁) ↦ (v₀)ᵢ (v₁)ⱼ e_k` -/
def mono2 (i j k : Fin 2) : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => E2) E2 :=
  ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin 2) ℂ).compContinuousLinearMap
    ![proj i, proj j]).smulRight (EuclideanSpace.single k (1 : ℂ))

/-- the trilinear monomial `(v₀, v₁, v₂) ↦ (v₀)ᵢ (v₁)ⱼ (v₂)ₗ e_k` -/
def mono3 (i j l k : Fin 2) : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E2) E2 :=
  ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin 3) ℂ).compContinuousLinearMap
    ![proj i, proj j, proj l]).smulRight (EuclideanSpace.single k (1 : ℂ))

lemma mono2_apply (i j k : Fin 2) (v : Fin 2 → E2) (m : Fin 2) :
    mono2 i j k v m = if m = k then v 0 i * v 1 j else 0 := by
  simp [mono2, Fin.prod_univ_two, PiLp.single_apply]

lemma mono3_apply (i j l k : Fin 2) (v : Fin 3 → E2) (m : Fin 2) :
    mono3 i j l k v m = if m = k then v 0 i * v 1 j * v 2 l else 0 := by
  simp [mono3, Fin.prod_univ_three, PiLp.single_apply]

/-! ### The Taylor maps of `H` -/

/-- the quadratic part `H^[2](w) = B_H(w, w)` -/
def BH : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => E2) E2 :=
  (39939 / 20000 : ℂ) • mono2 0 0 0 + (-611 / 5000 : ℂ) • mono2 0 1 0 +
    (-16513 / 10000 : ℂ) • mono2 1 1 0 + (359 / 2500 : ℂ) • mono2 0 0 1 +
    (-68299 / 20000 : ℂ) • mono2 0 1 1 + (-31 / 2000 : ℂ) • mono2 1 1 1

/-- the cubic part `H^[3](w) = C_H(w, w, w)` -/
def CH : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E2) E2 :=
  (795860061 / 400000000 : ℂ) • mono3 0 0 0 0 + (-22129389 / 100000000 : ℂ) • mono3 0 0 1 0 +
    (204536513 / 200000000 : ℂ) • mono3 0 1 1 0 + (327 / 2500 : ℂ) • mono3 1 1 1 0 +
    (14329641 / 50000000 : ℂ) • mono3 0 0 0 1 + (367808299 / 400000000 : ℂ) • mono3 0 0 1 1 +
    (-2779969 / 40000000 : ℂ) • mono3 0 1 1 1 + (8287 / 10000 : ℂ) • mono3 1 1 1 1

lemma BH_apply_zero (v : Fin 2 → E2) : BH v 0 = 39939 / 20000 * (v 0 0 * v 1 0) +
    -611 / 5000 * (v 0 0 * v 1 1) + -16513 / 10000 * (v 0 1 * v 1 1) := by
  simp [BH, mono2_apply]

lemma BH_apply_one (v : Fin 2 → E2) : BH v 1 = 359 / 2500 * (v 0 0 * v 1 0) +
    -68299 / 20000 * (v 0 0 * v 1 1) + -31 / 2000 * (v 0 1 * v 1 1) := by
  simp [BH, mono2_apply]

lemma CH_apply_zero (v : Fin 3 → E2) : CH v 0 =
    795860061 / 400000000 * (v 0 0 * v 1 0 * v 2 0) +
      -22129389 / 100000000 * (v 0 0 * v 1 0 * v 2 1) +
      204536513 / 200000000 * (v 0 0 * v 1 1 * v 2 1) + 327 / 2500 * (v 0 1 * v 1 1 * v 2 1) := by
  simp [CH, mono3_apply]

lemma CH_apply_one (v : Fin 3 → E2) : CH v 1 =
    14329641 / 50000000 * (v 0 0 * v 1 0 * v 2 0) +
      367808299 / 400000000 * (v 0 0 * v 1 0 * v 2 1) +
      -2779969 / 40000000 * (v 0 0 * v 1 1 * v 2 1) + 8287 / 10000 * (v 0 1 * v 1 1 * v 2 1) := by
  simp [CH, mono3_apply]

/-! ### Splitting `N` by degree -/

lemma N1of_filter (p : ℕ × ℕ × ℕ × ℤ → Bool) : ∀ (l : List (ℕ × ℕ × ℕ × ℤ)) (z₁ z₂ : ℂ),
    N1of l z₁ z₂ = N1of (l.filter p) z₁ z₂ + N1of (l.filter fun t => !p t) z₁ z₂
  | [], _, _ => by simp [N1of]
  | t :: rest, z₁, z₂ => by
    obtain ⟨comp, a, b, c⟩ := t
    have ih := N1of_filter p rest z₁ z₂
    cases h : p (comp, a, b, c) <;> simp [h, N1of, ih] <;> ring

lemma N2of_filter (p : ℕ × ℕ × ℕ × ℤ → Bool) : ∀ (l : List (ℕ × ℕ × ℕ × ℤ)) (z₁ z₂ : ℂ),
    N2of l z₁ z₂ = N2of (l.filter p) z₁ z₂ + N2of (l.filter fun t => !p t) z₁ z₂
  | [], _, _ => by simp [N2of]
  | t :: rest, z₁, z₂ => by
    obtain ⟨comp, a, b, c⟩ := t
    have ih := N2of_filter p rest z₁ z₂
    cases h : p (comp, a, b, c) <;> simp [h, N2of, ih] <;> ring

/-- terms of degree at most 3 -/
def lowDeg (t : ℕ × ℕ × ℕ × ℤ) : Bool := decide (t.2.1 + t.2.2.1 ≤ 3)

/-- the terms of `N` of degree 2 and 3 -/
def NTlow : List (ℕ × ℕ × ℕ × ℤ) :=
  [(1, 2, 0, 9970), (1, 3, 0, -72), (1, 1, 1, -1222), (1, 2, 1, -991), (1, 0, 2, -16513),
   (1, 1, 2, 26739), (1, 0, 3, 1308), (2, 2, 0, 1436), (2, 3, 0, 1430), (2, 1, 1, -44149),
   (2, 2, 1, 43343), (2, 0, 2, -155), (2, 1, 2, -540), (2, 0, 3, 8287)]

/-- the terms of `N` of degree `≥ 4` -/
def NThigh : List (ℕ × ℕ × ℕ × ℤ) := NTrest.filter fun t => !lowDeg t

lemma NTrest_low : NTrest.filter lowDeg = NTlow := by decide

lemma NThigh_deg : ∀ t ∈ NThigh, 4 ≤ t.2.1 + t.2.2.1 := by decide

lemma coefSum_eq (l : List (ℕ × ℕ × ℕ × ℤ)) :
    coefSum l = (((l.map fun t => t.2.2.2.natAbs).sum : ℕ) : ℝ) / 10000 := by
  induction l with
  | nil => simp [coefSum]
  | cons t rest ih =>
    simp only [coefSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Nat.cast_add, Nat.cast_natAbs, Int.cast_abs]
    ring

lemma coefSum_NThigh : coefSum NThigh ≤ 30 := by
  rw [coefSum_eq]
  have : (NThigh.map fun t => t.2.2.2.natAbs).sum = 296017 := by decide
  rw [this]
  norm_num

lemma N1_split (z₁ z₂ : ℂ) : N1 z₁ z₂ = z₁ + N1of NTlow z₁ z₂ + N1of NThigh z₁ z₂ := by
  rw [N1_eq, N1of_filter lowDeg NTrest, NTrest_low, NThigh]
  ring

lemma N2_split (z₁ z₂ : ℂ) : N2 z₁ z₂ = z₂ + N2of NTlow z₁ z₂ + N2of NThigh z₁ z₂ := by
  rw [N2_eq, N2of_filter lowDeg NTrest, NTrest_low, NThigh]
  ring

lemma rr_cast : (rr : ℂ) = 19999 / 20000 := by
  simp [rr]

/-! ### The remainder of `H` -/

/-- the remainder of the Taylor expansion of `H` to order 3 -/
def remH (w : E2) : E2 := Hgen w - w - BH ![w, w] - CH ![w, w, w]

lemma remH_key_zero (w : E2) :
    N1 (w 0) (w 1) - (1 - (rr : ℂ) * w 0) * (w 0 + BH ![w, w] 0 + CH ![w, w, w] 0) =
      N1of NThigh (w 0) (w 1) + (rr : ℂ) * w 0 * CH ![w, w, w] 0 := by
  rw [N1_split, BH_apply_zero, CH_apply_zero, rr_cast]
  norm_num [NTlow, N1of]
  ring

lemma remH_key_one (w : E2) :
    N2 (w 0) (w 1) - (1 - (rr : ℂ) * w 0) * (w 1 + BH ![w, w] 1 + CH ![w, w, w] 1) =
      N2of NThigh (w 0) (w 1) + (rr : ℂ) * w 0 * CH ![w, w, w] 1 := by
  rw [N2_split, BH_apply_one, CH_apply_one, rr_cast]
  norm_num [NTlow, N2of]
  ring

lemma remH_zero (w : E2) (hD : 1 - (rr : ℂ) * w 0 ≠ 0) :
    remH w 0 = (1 - (rr : ℂ) * w 0)⁻¹ *
      (N1of NThigh (w 0) (w 1) + (rr : ℂ) * w 0 * CH ![w, w, w] 0) := by
  have e : remH w 0 = (1 - (rr : ℂ) * w 0)⁻¹ * N1 (w 0) (w 1) - w 0 - BH ![w, w] 0 - CH ![w, w, w] 0 := by
    simp [remH, Hgen]
  rw [e, ← remH_key_zero, mul_sub, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  ring

lemma remH_one (w : E2) (hD : 1 - (rr : ℂ) * w 0 ≠ 0) :
    remH w 1 = (1 - (rr : ℂ) * w 0)⁻¹ *
      (N2of NThigh (w 0) (w 1) + (rr : ℂ) * w 0 * CH ![w, w, w] 1) := by
  have e : remH w 1 = (1 - (rr : ℂ) * w 0)⁻¹ * N2 (w 0) (w 1) - w 1 - BH ![w, w] 1 - CH ![w, w, w] 1 := by
    simp [remH, Hgen]
  rw [e, ← remH_key_one, mul_sub, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  ring

lemma norm_CH_le (w : E2) (k : Fin 2) : ‖CH ![w, w, w] k‖ ≤ 4 * ‖w‖ ^ 3 := by
  have h0 := PiLp.norm_apply_le w 0
  have h1 := PiLp.norm_apply_le w 1
  have hm : ∀ i j l : Fin 2, ‖w i * w j * w l‖ ≤ ‖w‖ ^ 3 := by
    intro i j l
    rw [norm_mul, norm_mul, pow_three]
    have hi := PiLp.norm_apply_le w i
    have hj := PiLp.norm_apply_le w j
    have hl := PiLp.norm_apply_le w l
    calc ‖w i‖ * ‖w j‖ * ‖w l‖ ≤ ‖w‖ * ‖w‖ * ‖w‖ := by gcongr
      _ = ‖w‖ * (‖w‖ * ‖w‖) := by ring
  have key : ∀ (a b c d : ℂ), ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ ≤ 4 →
      ‖a * (w 0 * w 0 * w 0) + b * (w 0 * w 0 * w 1) + c * (w 0 * w 1 * w 1) +
        d * (w 1 * w 1 * w 1)‖ ≤ 4 * ‖w‖ ^ 3 := by
    intro a b c d habcd
    have e1 := hm 0 0 0
    have e2 := hm 0 0 1
    have e3 := hm 0 1 1
    have e4 := hm 1 1 1
    have hw3 : 0 ≤ ‖w‖ ^ 3 := by positivity
    calc _ ≤ ‖a * (w 0 * w 0 * w 0)‖ + ‖b * (w 0 * w 0 * w 1)‖ + ‖c * (w 0 * w 1 * w 1)‖ +
          ‖d * (w 1 * w 1 * w 1)‖ := norm_add₄_le
      _ = ‖a‖ * ‖w 0 * w 0 * w 0‖ + ‖b‖ * ‖w 0 * w 0 * w 1‖ + ‖c‖ * ‖w 0 * w 1 * w 1‖ +
          ‖d‖ * ‖w 1 * w 1 * w 1‖ := by
          rw [norm_mul a, norm_mul b, norm_mul c, norm_mul d]
      _ ≤ ‖a‖ * ‖w‖ ^ 3 + ‖b‖ * ‖w‖ ^ 3 + ‖c‖ * ‖w‖ ^ 3 + ‖d‖ * ‖w‖ ^ 3 :=
          add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left e1 (norm_nonneg a))
            (mul_le_mul_of_nonneg_left e2 (norm_nonneg b)))
            (mul_le_mul_of_nonneg_left e3 (norm_nonneg c)))
            (mul_le_mul_of_nonneg_left e4 (norm_nonneg d))
      _ = (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) * ‖w‖ ^ 3 := by ring
      _ ≤ 4 * ‖w‖ ^ 3 := by gcongr
  fin_cases k
  · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, CH_apply_zero]
    apply key
    norm_num [Complex.norm_div]
  · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, CH_apply_one]
    apply key
    norm_num [Complex.norm_div]

lemma norm_inv_one_sub_le (w : E2) (hw : ‖w‖ ≤ 1 / 2) : ‖(1 - (rr : ℂ) * w 0)⁻¹‖ ≤ 2 := by
  have h0 : ‖w 0‖ ≤ 1 / 2 := (PiLp.norm_apply_le w 0).trans hw
  have hD : 1 / 2 ≤ ‖1 - (rr : ℂ) * w 0‖ := by
    have : ‖(rr : ℂ) * w 0‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos rr_pos]
      nlinarith [rr_lt_one, rr_pos, norm_nonneg (w 0)]
    have := norm_sub_norm_le (1 : ℂ) ((rr : ℂ) * w 0)
    rw [norm_one] at this
    linarith
  rw [norm_inv]
  have hpos : 0 < ‖1 - (rr : ℂ) * w 0‖ := by linarith
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

lemma norm_remH_comp_le (w : E2) (hw : ‖w‖ ≤ 1 / 2) (k : Fin 2) :
    ‖remH w k‖ ≤ 68 * ‖w‖ ^ 4 := by
  have hD : 1 - (rr : ℂ) * w 0 ≠ 0 := one_sub_ne_zero w (by linarith)
  have hinv := norm_inv_one_sub_le w hw
  have hw1 : ‖w‖ ≤ 1 := by linarith
  have h0 := PiLp.norm_apply_le w 0
  have h1 := PiLp.norm_apply_le w 1
  have hC := norm_CH_le w k
  have hrw : ‖(rr : ℂ) * w 0‖ ≤ ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos rr_pos]
    nlinarith [rr_lt_one, rr_pos, norm_nonneg (w 0)]
  have hrC : ‖(rr : ℂ) * w 0 * CH ![w, w, w] k‖ ≤ 4 * ‖w‖ ^ 4 := by
    rw [norm_mul]
    calc ‖(rr : ℂ) * w 0‖ * ‖CH ![w, w, w] k‖ ≤ ‖w‖ * (4 * ‖w‖ ^ 3) :=
          mul_le_mul hrw hC (norm_nonneg _) (norm_nonneg _)
      _ = 4 * ‖w‖ ^ 4 := by ring
  have hN : ∀ x : ℂ, ‖x‖ ≤ 30 * ‖w‖ ^ 4 →
      ‖(1 - (rr : ℂ) * w 0)⁻¹ * (x + (rr : ℂ) * w 0 * CH ![w, w, w] k)‖ ≤ 68 * ‖w‖ ^ 4 := by
    intro x hx
    rw [norm_mul]
    calc ‖(1 - (rr : ℂ) * w 0)⁻¹‖ * ‖x + (rr : ℂ) * w 0 * CH ![w, w, w] k‖ ≤
          2 * (30 * ‖w‖ ^ 4 + 4 * ‖w‖ ^ 4) := by
          apply mul_le_mul hinv _ (norm_nonneg _) (by norm_num)
          exact (norm_add_le _ _).trans (add_le_add hx hrC)
      _ = 68 * ‖w‖ ^ 4 := by ring
  fin_cases k
  · show ‖remH w 0‖ ≤ _
    rw [remH_zero w hD]
    apply hN
    calc ‖N1of NThigh (w 0) (w 1)‖ ≤ coefSum NThigh * ‖w‖ ^ 4 :=
          norm_N1of_le 4 NThigh NThigh_deg _ _ _ (norm_nonneg _) hw1 h0 h1
      _ ≤ 30 * ‖w‖ ^ 4 := by gcongr; exact coefSum_NThigh
  · show ‖remH w 1‖ ≤ _
    rw [remH_one w hD]
    apply hN
    calc ‖N2of NThigh (w 0) (w 1)‖ ≤ coefSum NThigh * ‖w‖ ^ 4 :=
          norm_N2of_le 4 NThigh NThigh_deg _ _ _ (norm_nonneg _) hw1 h0 h1
      _ ≤ 30 * ‖w‖ ^ 4 := by gcongr; exact coefSum_NThigh

/-- **The Taylor estimate for `H`.** -/
lemma norm_remH_le (w : E2) (hw : ‖w‖ ≤ 1 / 2) : ‖remH w‖ ≤ 136 * ‖w‖ ^ 4 := by
  have h0 := norm_remH_comp_le w hw 0
  have h1 := norm_remH_comp_le w hw 1
  calc ‖remH w‖ ≤ ‖remH w 0‖ + ‖remH w 1‖ := E2_norm_le _
    _ ≤ 136 * ‖w‖ ^ 4 := by linarith

/-! ### The Taylor maps of `h = U* H(U ·)` -/

/-- `U` as a continuous linear map -/
abbrev Ucl : E2 →L[ℂ] E2 := (Uiso.toContinuousLinearEquiv : E2 →L[ℂ] E2)

/-- `U* = U⁻¹` as a continuous linear map -/
abbrev Utcl : E2 →L[ℂ] E2 := (Uiso.symm.toContinuousLinearEquiv : E2 →L[ℂ] E2)

/-- the quadratic Taylor map of `h`: `B_h(z, z') = U* B_H(U z, U z')` -/
def Bh : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => E2) E2 :=
  Utcl.compContinuousMultilinearMap (BH.compContinuousLinearMap fun _ => Ucl)

/-- the cubic Taylor map of `h`: `C_h(z, z', z'') = U* C_H(U z, U z', U z'')` -/
def Ch : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E2) E2 :=
  Utcl.compContinuousMultilinearMap (CH.compContinuousLinearMap fun _ => Ucl)

lemma Bh_apply (v : Fin 2 → E2) : Bh v = Uiso.symm (BH fun i => Uiso (v i)) := by
  simp [Bh]

lemma Ch_apply (v : Fin 3 → E2) : Ch v = Uiso.symm (CH fun i => Uiso (v i)) := by
  simp [Ch]

/-- **The Taylor estimate for `h`.** -/
theorem norm_hgen_taylor_le (z : E2) (hz : ‖z‖ < 1 / 2) :
    ‖hgen z - z - Bh ![z, z] - Ch ![z, z, z]‖ ≤ 136 * ‖z‖ ^ 4 := by
  have e1 : (fun i => Uiso (![z, z] i)) = ![Uiso z, Uiso z] := by
    ext i : 1; fin_cases i <;> rfl
  have e2 : (fun i => Uiso (![z, z, z] i)) = ![Uiso z, Uiso z, Uiso z] := by
    ext i : 1; fin_cases i <;> rfl
  have e : hgen z - z - Bh ![z, z] - Ch ![z, z, z] = Uiso.symm (remH (Uiso z)) := by
    rw [remH, map_sub, map_sub, map_sub, Bh_apply, Ch_apply, e1, e2,
      LinearIsometryEquiv.symm_apply_apply]
    rfl
  rw [e, LinearIsometryEquiv.norm_map]
  have := norm_remH_le (Uiso z) (by rw [LinearIsometryEquiv.norm_map]; linarith)
  rwa [LinearIsometryEquiv.norm_map] at this

/-! ### The value of the third coefficient -/

/-- `½ (B_h(e, B_h(e,e)) + B_h(B_h(e,e), e) - C_h(e,e,e))` in the first coordinate,
`e = e₁` -/
theorem taylor_value :
    ((2 : ℂ)⁻¹ • (Bh ![ea, Bh ![ea, ea]] + Bh ![Bh ![ea, ea], ea] - Ch ![ea, ea, ea])) 0 =
      (2863108143393914687 / 954177312400000000 : ℂ) := by
  have hU : Uiso ea = !₂[220 / 221, -21 / 221] := by
    ext i; fin_cases i <;> simp [Ufun]
  have hBee : Bh ![ea, ea] = !₂[41500777221 / 21587722000, 70247673047 / 107938610000] := by
    rw [Bh_apply]
    have : (fun i => Uiso (![ea, ea] i)) = ![Uiso ea, Uiso ea] := by
      ext i : 1; fin_cases i <;> rfl
    rw [this, hU]
    ext i; fin_cases i <;> simp [Uinv, BH_apply_zero, BH_apply_one] <;> norm_num
  have h1 : Bh ![ea, Bh ![ea, ea]] 0 =
      Uinv (BH ![!₂[220 / 221, -21 / 221], Ufun !₂[41500777221 / 21587722000,
        70247673047 / 107938610000]]) 0 := by
    rw [Bh_apply, hBee]
    have : (fun i => Uiso (![ea, !₂[41500777221 / 21587722000, 70247673047 / 107938610000]] i)) =
        ![Uiso ea, Uiso !₂[41500777221 / 21587722000, 70247673047 / 107938610000]] := by
      ext i : 1; fin_cases i <;> rfl
    rw [this, hU]
    rfl
  have h2 : Bh ![Bh ![ea, ea], ea] 0 =
      Uinv (BH ![Ufun !₂[41500777221 / 21587722000, 70247673047 / 107938610000],
        !₂[220 / 221, -21 / 221]]) 0 := by
    rw [Bh_apply, hBee]
    have : (fun i => Uiso (![!₂[41500777221 / 21587722000, 70247673047 / 107938610000], ea] i)) =
        ![Uiso !₂[41500777221 / 21587722000, 70247673047 / 107938610000], Uiso ea] := by
      ext i : 1; fin_cases i <;> rfl
    rw [this, hU]
    rfl
  have h3 : Ch ![ea, ea, ea] 0 =
      Uinv (CH ![!₂[220 / 221, -21 / 221], !₂[220 / 221, -21 / 221], !₂[220 / 221, -21 / 221]]) 0 := by
    rw [Ch_apply]
    have : (fun i => Uiso (![ea, ea, ea] i)) = ![Uiso ea, Uiso ea, Uiso ea] := by
      ext i : 1; fin_cases i <;> rfl
    rw [this, hU]
    rfl
  simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul, h1, h2, h3]
  simp [Uinv, Ufun, BH_apply_zero, BH_apply_one, CH_apply_zero, CH_apply_one]
  norm_num

end LoewnerS0.Cex
