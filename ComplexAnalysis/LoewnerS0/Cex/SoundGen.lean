import Mathlib.Data.List.GetD
import LoewnerS0.Cex.SoundTerms
import LoewnerS0.Cex.SoundPD

/-!
# Soundness of the identity checker: the two sides

We identify the sums of the terms produced by `genAll` (the sum-of-squares side) and by `pTerms`
(the side of `F`).
-/

open Complex Finset

noncomputable section

namespace LoewnerS0.Cex

/-! ### Sums over the lower triangle -/

lemma sum_square_eq_lower (n : ℕ) (g : ℕ → ℕ → ℂ) :
    ∑ i ∈ range n, ∑ j ∈ range n, g i j =
      ∑ i ∈ range n, ∑ j ∈ range (i + 1), (if i = j then g i i else g i j + g j i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hL : ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), g i j =
        ∑ i ∈ range n, ∑ j ∈ range n, g i j + ∑ i ∈ range n, g i n +
          (∑ j ∈ range n, g n j + g n n) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    rw [hL, ih, Finset.sum_range_succ (fun i => ∑ j ∈ range (i + 1), _) n,
      Finset.sum_range_succ (fun j => if n = j then _ else _) n]
    simp only [ite_true]
    have : ∑ j ∈ range n, (if n = j then g n n else g n j + g j n) =
        ∑ j ∈ range n, (g n j + g j n) :=
      Finset.sum_congr rfl fun j hj => by
        rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
    rw [this, Finset.sum_add_distrib]
    ring

lemma two_hform (n : ℕ) (A : List (List ℤ)) (x : ℕ → ℂ) :
    2 * hform n A x = ∑ i ∈ range n, ∑ j ∈ range (i + 1),
      ((if i = j then 1 else 2 : ℤ) : ℂ) * (ent A i j : ℂ) *
        (starRingEnd ℂ (x i) * x j + starRingEnd ℂ (x j) * x i) := by
  unfold hform
  rw [sum_square_eq_lower, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  by_cases hij : i = j
  · subst hij
    simp [symEnt]
    ring
  · have h1 : symEnt A i j = ent A i j := by simp [symEnt, hji]
    have h2 : symEnt A j i = ent A i j := by simp [symEnt, show ¬ i ≤ j by omega]
    rw [ite_eq_right hij, ite_eq_right hij, h1, h2]
    push_cast
    ring

/-! ### The sum-of-squares side -/

variable (z₁ z₂ : ℂ)

/-- the vector `V(z) = (χ_j(z₁) χ_k(z₂))_{(j,k)}` -/
def Vvec (i : ℕ) : ℂ := chi (idxJ i) z₁ * chi (idxK i) z₂

lemma cTerm_eval (i j : ℕ) (v : List ℤ) (hv : v.length ≤ 15) :
    (cTerm i j v).eval z₁ z₂ = ((if i = j then 1 else 2 : ℤ) : ℂ) *
      evalVec (normSq z₁) (normSq z₂) 14 v *
      (starRingEnd ℂ (Vvec z₁ z₂ i) * Vvec z₁ z₂ j +
        starRingEnd ℂ (Vvec z₁ z₂ j) * Vvec z₁ z₂ i) := by
  simp only [cTerm, Term.eval]
  rw [symChi_canonMode, evalVec_replicate_zero,
    show 14 + mm (idxJ i) (idxJ j) + mm (idxK i) (idxK j) - mm (idxJ i) (idxJ j) =
      14 + mm (idxK i) (idxK j) by omega,
    evalVec_add_deg _ _ _ 14 _ (by simpa using hv), evalVec_map_mul]
  have e1 : starRingEnd ℂ (Vvec z₁ z₂ i) * Vvec z₁ z₂ j =
      (normSq z₁ : ℂ) ^ mm (idxJ i) (idxJ j) * chi (idxJ j - idxJ i) z₁ *
        ((normSq z₂ : ℂ) ^ mm (idxK i) (idxK j) * chi (idxK j - idxK i) z₂) := by
    rw [← conj_chi_mul_chi, ← conj_chi_mul_chi]
    simp only [Vvec, map_mul]
    ring
  have e2 : starRingEnd ℂ (Vvec z₁ z₂ j) * Vvec z₁ z₂ i =
      (normSq z₁ : ℂ) ^ mm (idxJ i) (idxJ j) * chi (idxJ i - idxJ j) z₁ *
        ((normSq z₂ : ℂ) ^ mm (idxK i) (idxK j) * chi (idxK i - idxK j) z₂) := by
    rw [mm_comm (idxJ i), mm_comm (idxK i), ← conj_chi_mul_chi, ← conj_chi_mul_chi]
    simp only [Vvec, map_mul]
    ring
  rw [e1, e2, symChi, show -(idxJ j - idxJ i) = idxJ i - idxJ j by ring,
    show -(idxK j - idxK i) = idxK i - idxK j by ring]
  ring

lemma sumEval_genRow (i : ℕ) : ∀ (j₀ : ℕ) (row : List (List ℤ)),
    sumEval z₁ z₂ (genRow i j₀ row) =
      ∑ j ∈ range row.length, (cTerm i (j₀ + j) (row.getD j [])).eval z₁ z₂
  | j₀, [] => by simp [genRow]
  | j₀, v :: vs => by
    rw [genRow, sumEval_cons, sumEval_genRow i (j₀ + 1) vs, List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show j₀ + 1 + j = j₀ + (j + 1) by omega]

lemma sumEval_genAll : ∀ (i₀ : ℕ) (rows : List (List (List ℤ))),
    sumEval z₁ z₂ (genAll i₀ rows) =
      ∑ i ∈ range rows.length, sumEval z₁ z₂ (genRow (i₀ + i) 0 (rows.getD i []))
  | i₀, [] => by simp [genAll]
  | i₀, row :: rows => by
    rw [genAll, sumEval_append, sumEval_genAll (i₀ + 1) rows, List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show i₀ + 1 + i = i₀ + (i + 1) by omega]

lemma shapeOK_spec (L : ℕ) : ∀ (i₀ : ℕ) (rows : List (List (List ℤ))),
    shapeOK L i₀ rows = true → ∀ i < rows.length,
      (rows.getD i []).length = i₀ + i + 1 ∧ ∀ v ∈ rows.getD i [], v.length = L
  | _, [], _ => fun i hi => absurd hi (by simp)
  | i₀, row :: rows, h => by
    simp only [shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
    intro i hi
    cases i with
    | zero => exact ⟨by simpa using h.1.1, by simpa using h.1.2⟩
    | succ i =>
      have := shapeOK_spec L (i₀ + 1) rows h.2 i (by simpa using hi)
      simpa [show i₀ + (i + 1) + 1 = i₀ + 1 + i + 1 by omega] using this

lemma ent_map_getD (A : List (List (List ℤ))) (i j l : ℕ) :
    ent (A.map (·.map (·.getD l 0))) i j = ((A.getD i []).getD j []).getD l 0 := by
  simp only [ent, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases A[i]? with _ | row
  · simp
  · simp only [Option.map_some, Option.getD_some, List.getElem?_map]
    rcases row[j]? with _ | v
    · simp
    · simp

/-- **The sum-of-squares side.** For the entry-major data `Ball`, the terms of `genAll` add up
to `∑ₗ Sˡ T^(14-l) · 2 V* Bₗ V`. -/
theorem sumEval_genAll_eq (Ball : List (List (List ℤ))) (n : ℕ) (hlen : Ball.length = n)
    (hshape : shapeOK 15 0 Ball = true) :
    sumEval z₁ z₂ (genAll 0 Ball) = ∑ l ∈ range 15,
      (normSq z₁ : ℂ) ^ l * (normSq z₂ : ℂ) ^ (14 - l) *
        (2 * hform n (Ball.map (·.map (·.getD l 0))) (Vvec z₁ z₂)) := by
  have hsh := shapeOK_spec 15 0 Ball hshape
  rw [sumEval_genAll, hlen]
  simp only [zero_add]
  -- each row
  have hrow : ∀ i ∈ range n, sumEval z₁ z₂ (genRow i 0 (Ball.getD i [])) =
      ∑ j ∈ range (i + 1), ((if i = j then 1 else 2 : ℤ) : ℂ) *
        (∑ l ∈ range 15, (((Ball.getD i []).getD j []).getD l 0 : ℂ) *
          (normSq z₁ : ℂ) ^ l * (normSq z₂ : ℂ) ^ (14 - l)) *
        (starRingEnd ℂ (Vvec z₁ z₂ i) * Vvec z₁ z₂ j +
          starRingEnd ℂ (Vvec z₁ z₂ j) * Vvec z₁ z₂ i) := by
    intro i hi
    have hi' : i < Ball.length := by rw [hlen]; exact Finset.mem_range.mp hi
    obtain ⟨hl, hv⟩ := hsh i hi'
    rw [sumEval_genRow, hl]
    simp only [zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < (Ball.getD i []).length := by rw [hl]; simpa using hj
    have hvj : ((Ball.getD i []).getD j []).length = 15 := by
      apply hv
      rw [getD_eq_getElem' _ _ hj']
      exact List.getElem_mem hj'
    rw [cTerm_eval z₁ z₂ i j _ (by omega), evalVec_eq_sum _ _ 14 _ (by omega), hvj]
  rw [Finset.sum_congr rfl hrow]
  -- the right-hand side
  have hrhs : ∀ l ∈ range 15, (normSq z₁ : ℂ) ^ l * (normSq z₂ : ℂ) ^ (14 - l) *
      (2 * hform n (Ball.map (·.map (·.getD l 0))) (Vvec z₁ z₂)) =
      ∑ i ∈ range n, ∑ j ∈ range (i + 1), ((if i = j then 1 else 2 : ℤ) : ℂ) *
        ((((Ball.getD i []).getD j []).getD l 0 : ℂ) * (normSq z₁ : ℂ) ^ l *
          (normSq z₂ : ℂ) ^ (14 - l)) *
        (starRingEnd ℂ (Vvec z₁ z₂ i) * Vvec z₁ z₂ j +
          starRingEnd ℂ (Vvec z₁ z₂ j) * Vvec z₁ z₂ i) := by
    intro l _
    rw [two_hform, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hent : ent (Ball.map (·.map (·.getD l 0))) i j =
        ((Ball.getD i []).getD j []).getD l 0 := ent_map_getD Ball i j l
    rw [hent]
    ring
  rw [Finset.sum_congr rfl hrhs, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]

/-! ### The side of `F` -/

/-- the value of the monomials produced by `pTerms` -/
def Pval (KP KR : ℤ) : List (ℕ × ℕ × ℕ × ℤ) → ℂ
  | [] => 0
  | (comp, a, b, c) :: rest =>
    (if comp = 1 then
      (KP * c : ℂ) * (z₁ ^ a * starRingEnd ℂ z₁ ^ 1 * (z₂ ^ b * starRingEnd ℂ z₂ ^ 0)) -
        (KR * c : ℂ) * (z₁ ^ a * starRingEnd ℂ z₁ ^ 2 * (z₂ ^ b * starRingEnd ℂ z₂ ^ 0))
    else
      (KP * c : ℂ) * (z₁ ^ a * starRingEnd ℂ z₁ ^ 0 * (z₂ ^ b * starRingEnd ℂ z₂ ^ 1)) -
        (KR * c : ℂ) * (z₁ ^ a * starRingEnd ℂ z₁ ^ 1 * (z₂ ^ b * starRingEnd ℂ z₂ ^ 1))) +
      Pval KP KR rest

lemma monoTerm_eval (a a' b b' : ℕ) (κ : ℤ) :
    (monoTerm a a' b b' κ).eval z₁ z₂ =
      (κ : ℂ) * (z₁ ^ a * starRingEnd ℂ z₁ ^ a' * (z₂ ^ b * starRingEnd ℂ z₂ ^ b')) +
        starRingEnd ℂ ((κ : ℂ) * (z₁ ^ a * starRingEnd ℂ z₁ ^ a' *
          (z₂ ^ b * starRingEnd ℂ z₂ ^ b'))) := by
  simp only [monoTerm, Term.eval]
  rw [symChi_canonMode, evalVec_replicate_zero,
    show min a a' + min b b' - min a a' = min b b' by omega]
  simp only [evalVec_cons, evalVec_nil, mul_zero, add_zero]
  simp only [map_mul, map_pow, Complex.conj_conj, map_intCast]
  rw [pow_mul_conj_pow a a' z₁, pow_mul_conj_pow b b' z₂,
    show (starRingEnd ℂ z₁) ^ a * z₁ ^ a' = z₁ ^ a' * (starRingEnd ℂ z₁) ^ a by ring,
    show (starRingEnd ℂ z₂) ^ b * z₂ ^ b' = z₂ ^ b' * (starRingEnd ℂ z₂) ^ b by ring,
    pow_mul_conj_pow a' a z₁, pow_mul_conj_pow b' b z₂, min_comm a' a, min_comm b' b, symChi,
    show -((a : ℤ) - a') = (a' : ℤ) - a by ring, show -((b : ℤ) - b') = (b' : ℤ) - b by ring]
  ring

lemma sumEval_pTerms (KP KR : ℤ) : ∀ NT : List (ℕ × ℕ × ℕ × ℤ),
    sumEval z₁ z₂ (pTerms KP KR NT) = Pval z₁ z₂ KP KR NT + starRingEnd ℂ (Pval z₁ z₂ KP KR NT)
  | [] => by simp [pTerms, Pval]
  | (comp, a, b, c) :: rest => by
    rw [pTerms, sumEval_append, sumEval_pTerms KP KR rest, Pval]
    split_ifs with h
    · simp only [sumEval_cons, sumEval_nil, add_zero, monoTerm_eval, map_add, map_sub, map_mul,
        map_intCast, map_pow, Complex.conj_conj]
      push_cast
      ring
    · simp only [sumEval_cons, sumEval_nil, add_zero, monoTerm_eval, map_add, map_sub, map_mul,
        map_intCast, map_pow, Complex.conj_conj]
      push_cast
      ring

/-! ### The identity -/

lemma sumEval_three_pieces (ts : List Term) (p q : Term → Bool) :
    sumEval z₁ z₂ ts = sumEval z₁ z₂ (ts.filter p) +
      sumEval z₁ z₂ (ts.filter fun t => !p t && q t) +
        sumEval z₁ z₂ (ts.filter fun t => !p t && !q t) := by
  rw [sumEval_filter z₁ z₂ p ts, sumEval_filter z₁ z₂ q (ts.filter fun t => !p t),
    List.filter_filter, List.filter_filter]
  simp only [Bool.and_comm]
  ring

/-- **The identity.** If the three pieces of the identity check succeed, then on the sphere
`∑ₗ Sˡ T^(14-l) · 2 V* Bₗ V = P + P̄`. -/
theorem identity_of_pieces (Ball : List (List (List ℤ))) (n : ℕ) (hlen : Ball.length = n)
    (hshape : shapeOK 15 0 Ball = true) (NT : List (ℕ × ℕ × ℕ × ℤ)) (KP KR : ℤ)
    (p q : Term → Bool) (h1 : pieceOK Ball NT KP KR p = true)
    (h2 : pieceOK Ball NT KP KR (fun t => !p t && q t) = true)
    (h3 : pieceOK Ball NT KP KR (fun t => !p t && !q t) = true)
    (hz : normSq z₁ + normSq z₂ = 1) :
    ∑ l ∈ range 15, (normSq z₁ : ℂ) ^ l * (normSq z₂ : ℂ) ^ (14 - l) *
        (2 * hform n (Ball.map (·.map (·.getD l 0))) (Vvec z₁ z₂)) =
      Pval z₁ z₂ KP KR NT + starRingEnd ℂ (Pval z₁ z₂ KP KR NT) := by
  have h0 : sumEval z₁ z₂ (allTerms Ball NT KP KR) = 0 := by
    rw [sumEval_three_pieces z₁ z₂ _ p q, sumEval_filter_eq_zero z₁ z₂ hz _ _ h1,
      sumEval_filter_eq_zero z₁ z₂ hz _ _ h2, sumEval_filter_eq_zero z₁ z₂ hz _ _ h3]
    ring
  rw [allTerms, sumEval_append, sumEval_map_neg, sumEval_genAll_eq z₁ z₂ Ball n hlen hshape,
    sumEval_pTerms] at h0
  linear_combination h0

end LoewnerS0.Cex
