import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import LoewnerS0.Cex.Checker

/-!
# Soundness of the identity checker: symmetric terms

We give the terms of `LoewnerS0.Cex.Checker` their meaning at a point `(z₁, z₂) ∈ ℂ²` and show
that sorting, merging and degree elevation do not change the sum of the terms, provided
`|z₁|² + |z₂|² = 1`.
-/

open Complex

noncomputable section

namespace LoewnerS0.Cex

/-! ### Coefficient vectors -/

section evalVec

variable (S T : ℂ)

/-- `∑ₖ v[k] Sᵏ T^(d-k)` -/
def evalVec : ℕ → List ℤ → ℂ
  | _, [] => 0
  | d, x :: xs => (x : ℂ) * T ^ d + S * evalVec (d - 1) xs

@[simp] lemma evalVec_nil (d : ℕ) : evalVec S T d [] = 0 := rfl

@[simp] lemma evalVec_cons (d : ℕ) (x : ℤ) (xs : List ℤ) :
    evalVec S T d (x :: xs) = (x : ℂ) * T ^ d + S * evalVec S T (d - 1) xs := rfl

lemma evalVec_padAdd : ∀ (d : ℕ) (u v : List ℤ),
    evalVec S T d (padAdd u v) = evalVec S T d u + evalVec S T d v
  | d, [], v => by simp [padAdd]
  | d, x :: xs, [] => by simp [padAdd]
  | d, x :: xs, y :: ys => by
    simp only [padAdd, evalVec_cons, evalVec_padAdd (d - 1) xs ys]
    push_cast
    ring

lemma evalVec_neg : ∀ (d : ℕ) (v : List ℤ), evalVec S T d (v.map (- ·)) = - evalVec S T d v
  | d, [] => by simp
  | d, x :: xs => by
    simp only [List.map_cons, evalVec_cons, evalVec_neg (d - 1) xs]
    push_cast
    ring

lemma evalVec_map_mul (c : ℤ) : ∀ (d : ℕ) (v : List ℤ),
    evalVec S T d (v.map (c * ·)) = c * evalVec S T d v
  | d, [] => by simp
  | d, x :: xs => by
    simp only [List.map_cons, evalVec_cons, evalVec_map_mul c (d - 1) xs]
    push_cast
    ring

lemma evalVec_eq_zero : ∀ (d : ℕ) (v : List ℤ), (v.all fun x => x == 0) = true →
    evalVec S T d v = 0
  | d, [] , _ => rfl
  | d, x :: xs, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, evalVec_eq_zero (d - 1) xs h.2]

lemma evalVec_addHead (x : ℤ) (d : ℕ) (v : List ℤ) :
    evalVec S T d (addHead x v) = (x : ℂ) * T ^ d + evalVec S T d v := by
  cases v with
  | nil => simp [addHead]
  | cons y ys => simp only [addHead, evalVec_cons]; push_cast; ring

lemma length_addHead (x : ℤ) (v : List ℤ) : (addHead x v).length = max v.length 1 := by
  cases v <;> simp [addHead]

lemma length_elev_le : ∀ v : List ℤ, (elev v).length ≤ v.length + 1
  | [] => by simp [elev]
  | x :: xs => by
    have := length_elev_le xs
    simp only [elev, List.length_cons, length_addHead]
    omega

/-- degree elevation does not change the value on `S + T = 1` -/
lemma evalVec_elev (hST : S + T = 1) : ∀ (d : ℕ) (v : List ℤ), v.length ≤ d + 1 →
    evalVec S T (d + 1) (elev v) = evalVec S T d v
  | _, [], _ => rfl
  | 0, x :: xs, h => by
    have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst hxs
    simp only [elev, addHead, evalVec_cons, evalVec_nil]
    linear_combination (x : ℂ) * hST
  | d + 1, x :: xs, h => by
    have ih := evalVec_elev hST d xs (by simpa using h)
    simp only [elev, evalVec_cons, evalVec_addHead, Nat.add_sub_cancel, ih]
    linear_combination (x : ℂ) * T ^ (d + 1) * hST

lemma evalVec_elevN (hST : S + T = 1) : ∀ (n d : ℕ) (v : List ℤ), v.length ≤ d + 1 →
    evalVec S T (d + n) (elevN n v) = evalVec S T d v
  | 0, d, v, _ => rfl
  | n + 1, d, v, h => by
    have h' : (elev v).length ≤ d + 1 + 1 := (length_elev_le v).trans (by omega)
    rw [elevN, show d + (n + 1) = d + 1 + n by omega, evalVec_elevN hST n (d + 1) (elev v) h',
      evalVec_elev S T hST d v h]

lemma evalVec_replicate_zero : ∀ (m d : ℕ) (w : List ℤ),
    evalVec S T d (List.replicate m 0 ++ w) = S ^ m * evalVec S T (d - m) w
  | 0, d, w => by simp
  | m + 1, d, w => by
    rw [List.replicate_succ, List.cons_append, evalVec_cons, evalVec_replicate_zero m (d - 1) w,
      show d - 1 - m = d - (m + 1) by omega]
    push_cast
    ring

lemma evalVec_add_deg (n : ℕ) : ∀ (d : ℕ) (w : List ℤ), w.length ≤ d + 1 →
    evalVec S T (d + n) w = T ^ n * evalVec S T d w
  | _, [], _ => by simp
  | 0, x :: xs, h => by
    have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst hxs
    simp [mul_comm]
  | d + 1, x :: xs, h => by
    have ih := evalVec_add_deg n d xs (by simpa using h)
    simp only [evalVec_cons, show d + 1 + n - 1 = d + n by omega, ih, Nat.add_sub_cancel]
    ring

/-- the closed form of `evalVec` -/
lemma evalVec_eq_sum : ∀ (d : ℕ) (v : List ℤ), v.length ≤ d + 1 →
    evalVec S T d v = ∑ k ∈ Finset.range v.length, (v.getD k 0 : ℂ) * S ^ k * T ^ (d - k)
  | _, [], _ => by simp
  | d, x :: xs, h => by
    rw [evalVec_cons, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, pow_zero, mul_one, Nat.sub_zero, List.getD_cons_succ]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hxs
      simp
    · rw [evalVec_eq_sum (d - 1) xs (by simp at h; omega), Finset.mul_sum]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [show d - (k + 1) = d - 1 - k by omega]
      ring

end evalVec

/-! ### The functions `χ` -/

/-- `χ_a(z) = z^a` for `a ≥ 0` and `χ_a(z) = z̄^|a|` for `a < 0` -/
def chi (a : ℤ) (z : ℂ) : ℂ := if 0 ≤ a then z ^ a.toNat else (starRingEnd ℂ z) ^ a.natAbs

@[simp] lemma chi_zero (z : ℂ) : chi 0 z = 1 := by simp [chi]

lemma chi_of_nonneg {a : ℤ} (ha : 0 ≤ a) (z : ℂ) : chi a z = z ^ a.toNat := by simp [chi, ha]

lemma chi_of_neg {a : ℤ} (ha : a < 0) (z : ℂ) : chi a z = (starRingEnd ℂ z) ^ a.natAbs := by
  simp [chi, not_le.mpr ha]

lemma chi_natCast (n : ℕ) (z : ℂ) : chi n z = z ^ n := by simp [chi]

lemma chi_neg_natCast (n : ℕ) (z : ℂ) : chi (-(n : ℤ)) z = (starRingEnd ℂ z) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [chi_of_neg (by omega)]
    simp

lemma conj_chi (a : ℤ) (z : ℂ) : starRingEnd ℂ (chi a z) = chi (-a) z := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
  · rw [chi_natCast, chi_neg_natCast, map_pow]
  · rw [chi_neg_natCast, neg_neg, chi_natCast, map_pow, Complex.conj_conj]

/-- `z^p z̄^q = |z|^(2 min(p,q)) χ_{p-q}(z)` -/
lemma pow_mul_conj_pow (p q : ℕ) (z : ℂ) :
    z ^ p * (starRingEnd ℂ z) ^ q = (normSq z : ℂ) ^ min p q * chi ((p : ℤ) - q) z := by
  rw [← Complex.mul_conj]
  rcases le_total p q with hpq | hpq
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpq
    rw [min_eq_left hpq, show ((p : ℤ) - (p + k : ℕ)) = -(k : ℤ) by push_cast; ring,
      chi_neg_natCast]
    ring
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpq
    rw [min_eq_right hpq, show (((q + k : ℕ) : ℤ) - q) = (k : ℤ) by push_cast; ring,
      chi_natCast]
    ring

/-- `χ_a(z) = z^(a⁺) z̄^(a⁻)` -/
lemma chi_eq_pow_mul (a : ℤ) (z : ℂ) :
    chi a z = z ^ a.toNat * (starRingEnd ℂ z) ^ (-a).toNat := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
  · simp [chi_natCast]
  · simp [chi_neg_natCast]

lemma mm_eq (a b : ℤ) : mm a b = min ((-a).toNat + b.toNat) (a.toNat + (-b).toNat) := by
  unfold mm
  split_ifs with h1 h2 <;> omega

lemma mm_comm (a b : ℤ) : mm a b = mm b a := by
  rw [mm_eq, mm_eq]
  omega

/-- `conj(χ_a z) χ_b z = |z|^(2 mm(a,b)) χ_{b-a}(z)` -/
lemma conj_chi_mul_chi (a b : ℤ) (z : ℂ) :
    starRingEnd ℂ (chi a z) * chi b z = (normSq z : ℂ) ^ mm a b * chi (b - a) z := by
  rw [chi_eq_pow_mul a, chi_eq_pow_mul b, map_mul, map_pow, map_pow, Complex.conj_conj,
    show (starRingEnd ℂ z) ^ a.toNat * z ^ (-a).toNat * (z ^ b.toNat * (starRingEnd ℂ z) ^ (-b).toNat)
      = z ^ ((-a).toNat + b.toNat) * (starRingEnd ℂ z) ^ (a.toNat + (-b).toNat) by ring,
    pow_mul_conj_pow, mm_eq]
  congr 2
  push_cast
  omega

/-! ### Symmetric terms -/

variable (z₁ z₂ : ℂ)

/-- `χ_Δ + χ_{-Δ}` -/
def symChi (d1 d2 : ℤ) : ℂ := chi d1 z₁ * chi d2 z₂ + chi (-d1) z₁ * chi (-d2) z₂

lemma symChi_neg (d1 d2 : ℤ) : symChi z₁ z₂ (-d1) (-d2) = symChi z₁ z₂ d1 d2 := by
  simp [symChi, add_comm]

lemma symChi_canonMode (d1 d2 : ℤ) :
    symChi z₁ z₂ (canonMode d1 d2).1 (canonMode d1 d2).2 = symChi z₁ z₂ d1 d2 := by
  unfold canonMode
  split_ifs
  · rfl
  · exact symChi_neg z₁ z₂ d1 d2

/-- the value of a symmetric term at `(z₁, z₂)` -/
def Term.eval (t : Term) : ℂ :=
  evalVec (normSq z₁) (normSq z₂) t.deg t.vec * symChi z₁ z₂ t.d1 t.d2

/-- the sum of a list of terms -/
def sumEval (ts : List Term) : ℂ := (ts.map (Term.eval z₁ z₂)).sum

@[simp] lemma sumEval_nil : sumEval z₁ z₂ [] = 0 := rfl

@[simp] lemma sumEval_cons (t : Term) (ts : List Term) :
    sumEval z₁ z₂ (t :: ts) = t.eval z₁ z₂ + sumEval z₁ z₂ ts := by
  simp [sumEval]

@[simp] lemma sumEval_append (xs ys : List Term) :
    sumEval z₁ z₂ (xs ++ ys) = sumEval z₁ z₂ xs + sumEval z₁ z₂ ys := by
  simp [sumEval]

lemma sumEval_map_neg (ts : List Term) :
    sumEval z₁ z₂ (ts.map Term.neg) = - sumEval z₁ z₂ ts := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, sumEval_cons, ih, Term.eval, Term.neg, evalVec_neg]
    ring

lemma sumEval_filter (p : Term → Bool) (ts : List Term) :
    sumEval z₁ z₂ ts = sumEval z₁ z₂ (ts.filter p) + sumEval z₁ z₂ (ts.filter fun t => !p t) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    cases h : p t <;> simp [h, ih] <;> ring

/-- terms with the same mode and degree can be added -/
lemma eval_merge {x y : Term} (h : x.same y = true) :
    Term.eval z₁ z₂ ⟨x.d1, x.d2, x.deg, padAdd x.vec y.vec⟩ = x.eval z₁ z₂ + y.eval z₁ z₂ := by
  simp only [Term.same, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [Term.eval, evalVec_padAdd, h1, h2, h3]
  ring

lemma sumEval_mergeT : ∀ (f : ℕ) (xs ys : List Term),
    sumEval z₁ z₂ (mergeT f xs ys) = sumEval z₁ z₂ xs + sumEval z₁ z₂ ys
  | 0, xs, ys => by simp [mergeT]
  | _ + 1, [], ys => by simp [mergeT]
  | _ + 1, x :: xs, [] => by simp [mergeT]
  | f + 1, x :: xs, y :: ys => by
    unfold mergeT
    split_ifs with h1 h2
    · rw [sumEval_cons, sumEval_mergeT f xs ys, eval_merge z₁ z₂ h1]
      simp only [sumEval_cons]
      ring
    · rw [sumEval_cons, sumEval_mergeT f xs (y :: ys)]
      simp only [sumEval_cons]
      ring
    · rw [sumEval_cons, sumEval_mergeT f (x :: xs) ys]
      simp only [sumEval_cons]
      ring

/-- the sum over a list of lists of terms -/
def sumEvalLL (ls : List (List Term)) : ℂ := (ls.map (sumEval z₁ z₂)).sum

lemma sumEvalLL_mergePairs : ∀ ls : List (List Term),
    sumEvalLL z₁ z₂ (mergePairs ls) = sumEvalLL z₁ z₂ ls
  | [] => by simp [mergePairs]
  | [a] => by simp [mergePairs]
  | a :: b :: rest => by
    simp only [mergePairs, sumEvalLL, List.map_cons, List.sum_cons, sumEval_mergeT]
    have := sumEvalLL_mergePairs rest
    simp only [sumEvalLL] at this
    rw [this]
    ring

lemma sumEval_msortAux : ∀ (f : ℕ) (ls : List (List Term)),
    sumEval z₁ z₂ (msortAux f ls) = sumEvalLL z₁ z₂ ls
  | 0, ls => by
    simp only [msortAux, sumEvalLL]
    induction ls with
    | nil => simp
    | cons l ls ih => simp [ih]
  | _ + 1, [] => by simp [msortAux, sumEvalLL]
  | _ + 1, [l] => by simp [msortAux, sumEvalLL]
  | f + 1, a :: b :: rest => by
    rw [msortAux, sumEval_msortAux f, sumEvalLL_mergePairs]

lemma sumEval_msort (ts : List Term) : sumEval z₁ z₂ (msort ts) = sumEval z₁ z₂ ts := by
  rw [msort, sumEval_msortAux]
  induction ts with
  | nil => simp [sumEvalLL]
  | cons t ts ih => simpa [sumEvalLL] using ih

/-- `combineMode` does not change the sum, on `|z₁|² + |z₂|² = 1` -/
lemma sumEval_combineMode (hz : normSq z₁ + normSq z₂ = 1) : ∀ ts : List Term,
    sumEval z₁ z₂ (combineMode ts) = sumEval z₁ z₂ ts
  | [] => rfl
  | t :: ts => by
    have ih := sumEval_combineMode hz ts
    have hST : (normSq z₁ : ℂ) + normSq z₂ = 1 := by exact_mod_cast hz
    rw [combineMode]
    rcases hc : combineMode ts with _ | ⟨u, us⟩
    · rw [hc] at ih
      simp [← ih]
    · rw [hc] at ih
      simp only
      split_ifs with h
      · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Term.wf] at h
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
        rw [sumEval_cons, sumEval_cons, ← ih, sumEval_cons]
        simp only [Term.eval, evalVec_padAdd, ← h1, ← h2]
        have := evalVec_elevN (normSq z₁ : ℂ) (normSq z₂) hST (t.deg - u.deg) u.deg u.vec h4
        rw [show u.deg + (t.deg - u.deg) = t.deg by omega] at this
        rw [this]
        ring
      · rw [sumEval_cons, ih, sumEval_cons]

lemma sumEval_eq_zero (ts : List Term) (h : (ts.all fun t => t.vec.all (· == 0)) = true) :
    sumEval z₁ z₂ ts = 0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [Term.eval, evalVec_eq_zero _ _ _ _ h.1, ih h.2]

/-- a successful piece of the identity check -/
lemma sumEval_filter_eq_zero (hz : normSq z₁ + normSq z₂ = 1) (ts : List Term)
    (p : Term → Bool)
    (h : ((combineMode (msort (ts.filter p))).all fun t => t.vec.all (· == 0)) = true) :
    sumEval z₁ z₂ (ts.filter p) = 0 := by
  rw [← sumEval_msort, ← sumEval_combineMode z₁ z₂ hz]
  exact sumEval_eq_zero z₁ z₂ _ h

end LoewnerS0.Cex
