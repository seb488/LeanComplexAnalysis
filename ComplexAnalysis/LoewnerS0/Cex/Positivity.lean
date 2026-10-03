import LoewnerS0.Cex.SoundGen
import LoewnerS0.Cex.CheckId
import LoewnerS0.Cex.CheckPD

/-!
# `F ≥ 10⁻⁶` on the unit sphere

This is Proposition 5.1 of `disproof_starlike.tex`. With `N` the polynomial map of the generator
(`N1`, `N2`) and `r = 19999/20000`,

  `F(w) = Re((N₁(w) w̄₁ + N₂(w) w̄₂)(1 - r w̄₁))`

satisfies `F(w) ≥ 10⁻⁶` for `|w₁|² + |w₂|² = 1`. The proof combines the kernel checks
(`LoewnerS0.Cex.CheckId`, `LoewnerS0.Cex.CheckPD`) with their soundness theorems.
-/

open Complex Finset

noncomputable section

namespace LoewnerS0.Cex

/-- `r = 19999/20000` -/
def rr : ℝ := 19999 / 20000

/-- the components of `N` given by a term list -/
def N1of : List (ℕ × ℕ × ℕ × ℤ) → ℂ → ℂ → ℂ
  | [], _, _ => 0
  | (comp, a, b, c) :: rest, z₁, z₂ =>
    (if comp = 1 then (c : ℂ) / 10000 * z₁ ^ a * z₂ ^ b else 0) + N1of rest z₁ z₂

def N2of : List (ℕ × ℕ × ℕ × ℤ) → ℂ → ℂ → ℂ
  | [], _, _ => 0
  | (comp, a, b, c) :: rest, z₁, z₂ =>
    (if comp = 1 then 0 else (c : ℂ) / 10000 * z₁ ^ a * z₂ ^ b) + N2of rest z₁ z₂

/-- the first component of `N` -/
def N1 (z₁ z₂ : ℂ) : ℂ := N1of NT z₁ z₂

/-- the second component of `N` -/
def N2 (z₁ z₂ : ℂ) : ℂ := N2of NT z₁ z₂

/-- `F(w) = Re((N₁ w̄₁ + N₂ w̄₂)(1 - r w̄₁))` -/
def Ffun (z₁ z₂ : ℂ) : ℝ :=
  ((N1 z₁ z₂ * starRingEnd ℂ z₁ + N2 z₁ z₂ * starRingEnd ℂ z₂) * (1 - (rr : ℂ) * starRingEnd ℂ z₁)).re

lemma Pval_eq (z₁ z₂ : ℂ) (KP KR : ℤ) : ∀ l : List (ℕ × ℕ × ℕ × ℤ),
    Pval z₁ z₂ KP KR l = (10000 * KP - 10000 * KR * starRingEnd ℂ z₁) *
      (N1of l z₁ z₂ * starRingEnd ℂ z₁ + N2of l z₁ z₂ * starRingEnd ℂ z₂)
  | [] => by simp [Pval, N1of, N2of]
  | (comp, a, b, c) :: rest => by
    rw [Pval, N1of, N2of, Pval_eq z₁ z₂ KP KR rest]
    split_ifs <;> ring

lemma KP_eq : (10000 * KP : ℂ) = (LC : ℂ) := by
  simp only [KP, LC]; norm_num

lemma KR_eq : (10000 * KR : ℂ) = (LC : ℂ) * (rr : ℂ) := by
  simp only [KR, LC, rr]; push_cast; norm_num

lemma Pval_NT (z₁ z₂ : ℂ) : Pval z₁ z₂ KP KR NT = (LC : ℂ) *
    ((N1 z₁ z₂ * starRingEnd ℂ z₁ + N2 z₁ z₂ * starRingEnd ℂ z₂) * (1 - (rr : ℂ) * starRingEnd ℂ z₁)) := by
  rw [Pval_eq, N1, N2]
  linear_combination (N1of NT z₁ z₂ * starRingEnd ℂ z₁ + N2of NT z₁ z₂ * starRingEnd ℂ z₂) * KP_eq -
    (starRingEnd ℂ z₁ * (N1of NT z₁ z₂ * starRingEnd ℂ z₁ + N2of NT z₁ z₂ * starRingEnd ℂ z₂)) * KR_eq

/-! ### The matrices -/

lemma ent_Ball (l : ℕ) (hl : l < 15) (i j : ℕ) :
    ent (Ball.map (·.map (·.getD l 0))) i j = ent (Bmat l) i j := by
  rw [ent_map_getD]
  simp only [ent, Bmat, Ball, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases BallData[i]? with _ | row
  · simp
  · simp only [Option.map_some, Option.getD_some, List.getElem?_map]
    rcases row[j]? with _ | x
    · simp
    · simp only [Option.map_some, Option.getD_some, unpack, List.getElem?_map,
        List.getElem?_range hl]

lemma hform_Ball (l : ℕ) (hl : l < 15) (x : ℕ → ℂ) :
    hform 52 (Ball.map (·.map (·.getD l 0))) x = hform 52 (Bmat l) x := by
  unfold hform symEnt
  simp only [ent_Ball l hl]

lemma binom14_spec : ∀ l < 15, binom14.getD l 0 = Nat.choose 14 l := by decide

lemma binom14_eq (l : ℕ) (hl : l < 15) : binom14.getD l 0 = Nat.choose 14 l := binom14_spec l hl

/-- the positive definiteness of `Bₗ`, in the form used below -/
lemma pd_bound (l : ℕ) (hl : l < 15) (x : ℕ → ℂ) :
    (Nat.choose 14 l : ℝ) * (LC6 : ℝ) * ∑ i ∈ range 52, ‖x i‖ ^ 2 ≤
      (hform 52 (Bmat l) x).re := by
  have h := pdCheck_sound (n := 52) (K := (binom14.getD l 0 * LC : ℕ))
    (E := (Epow : ℕ)) (DE := (binom14.getD l 0 * LC6 * Epow : ℕ)) (by positivity)
    (by simpa [pdOK] using pdOK_all l hl) x
  rw [binom14_eq l hl] at h
  have hE : (0 : ℝ) < (Epow : ℝ) := by norm_num [Epow]
  push_cast at h
  have : (Nat.choose 14 l : ℝ) * (LC6 : ℝ) * (Epow : ℝ) * ∑ i ∈ range 52, ‖x i‖ ^ 2 ≤
      (Epow : ℝ) * (hform 52 (Bmat l) x).re := by linarith
  nlinarith

/-! ### The vector `V` -/

lemma Vvec_25 (z₁ z₂ : ℂ) : Vvec z₁ z₂ 25 = 1 := by
  simp [Vvec, idxJ, idxK]

lemma one_le_normV (z₁ z₂ : ℂ) : 1 ≤ ∑ i ∈ range 52, ‖Vvec z₁ z₂ i‖ ^ 2 := by
  have h25 : ‖Vvec z₁ z₂ 25‖ ^ 2 = 1 := by rw [Vvec_25]; simp
  calc (1 : ℝ) = ‖Vvec z₁ z₂ 25‖ ^ 2 := h25.symm
    _ ≤ ∑ i ∈ range 52, ‖Vvec z₁ z₂ i‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ‖Vvec z₁ z₂ i‖ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_range.mpr (by norm_num))

/-! ### The main estimate -/

/-- **Proposition 5.1.** `F ≥ 10⁻⁶` on the unit sphere of `ℂ²`. -/
theorem Ffun_ge (z₁ z₂ : ℂ) (hz : normSq z₁ + normSq z₂ = 1) :
    (1 / 10 ^ 6 : ℝ) ≤ Ffun z₁ z₂ := by
  -- the identity
  have hid := identity_of_pieces z₁ z₂ Ball 52 ball_length ball_shape NT KP KR piece1
    (fun t => decide (t.key < cut2)) identity_piece1 identity_piece2 identity_piece3 hz
  rw [Pval_NT] at hid
  set W : ℂ := (N1 z₁ z₂ * starRingEnd ℂ z₁ + N2 z₁ z₂ * starRingEnd ℂ z₂) *
    (1 - (rr : ℂ) * starRingEnd ℂ z₁) with hW
  have hconj : (LC : ℂ) * W + starRingEnd ℂ ((LC : ℂ) * W) = ((2 * (LC : ℝ) * W.re : ℝ) : ℂ) := by
    rw [map_mul, map_natCast, ← mul_add, Complex.add_conj]
    push_cast
    ring
  rw [hconj] at hid
  -- real parts
  have hre := congrArg Complex.re hid
  rw [Complex.ofReal_re, Complex.re_sum] at hre
  set S : ℝ := normSq z₁
  set T : ℝ := normSq z₂
  have hS : 0 ≤ S := normSq_nonneg _
  have hT : 0 ≤ T := normSq_nonneg _
  have hterm : ∀ l ∈ range 15, ((S : ℂ) ^ l * (T : ℂ) ^ (14 - l) *
      (2 * hform 52 (Ball.map (·.map (·.getD l 0))) (Vvec z₁ z₂))).re =
      S ^ l * T ^ (14 - l) * (2 * (hform 52 (Bmat l) (Vvec z₁ z₂)).re) := by
    intro l hl
    rw [hform_Ball l (Finset.mem_range.mp hl)]
    rw [show (S : ℂ) ^ l * (T : ℂ) ^ (14 - l) = ((S ^ l * T ^ (14 - l) : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
    simp
  rw [Finset.sum_congr rfl hterm] at hre
  -- lower bound for each term
  set nV : ℝ := ∑ i ∈ range 52, ‖Vvec z₁ z₂ i‖ ^ 2
  have hlow : ∀ l ∈ range 15, S ^ l * T ^ (14 - l) * (2 * ((Nat.choose 14 l : ℝ) * LC6 * nV)) ≤
      S ^ l * T ^ (14 - l) * (2 * (hform 52 (Bmat l) (Vvec z₁ z₂)).re) := by
    intro l hl
    have := pd_bound l (Finset.mem_range.mp hl) (Vvec z₁ z₂)
    have hST : 0 ≤ S ^ l * T ^ (14 - l) := by positivity
    nlinarith
  have hsum := Finset.sum_le_sum hlow
  rw [hre] at hsum
  -- the binomial sum
  have hbin : ∑ l ∈ range 15, S ^ l * T ^ (14 - l) * (Nat.choose 14 l : ℝ) = 1 := by
    have := add_pow S T 14
    have hST : S + T = 1 := hz
    rw [hST, one_pow] at this
    rw [this]
  have hlhs : ∑ l ∈ range 15, S ^ l * T ^ (14 - l) * (2 * ((Nat.choose 14 l : ℝ) * LC6 * nV)) =
      2 * LC6 * nV := by
    rw [show ∑ l ∈ range 15, S ^ l * T ^ (14 - l) * (2 * ((Nat.choose 14 l : ℝ) * LC6 * nV)) =
        (∑ l ∈ range 15, S ^ l * T ^ (14 - l) * (Nat.choose 14 l : ℝ)) * (2 * LC6 * nV) by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun l _ => ?_; ring]
    rw [hbin, one_mul]
  rw [hlhs] at hsum
  have hnV : 1 ≤ nV := one_le_normV z₁ z₂
  have hLC : (LC : ℝ) = 40305583718400000000 := by simp [LC]
  have hLC6 : (LC6 : ℝ) = 40305583718400 := by simp [LC6]
  rw [hLC, hLC6] at hsum
  have hF : Ffun z₁ z₂ = W.re := rfl
  rw [hF]
  nlinarith

end LoewnerS0.Cex
