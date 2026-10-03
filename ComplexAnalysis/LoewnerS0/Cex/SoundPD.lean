import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import LoewnerS0.Cex.Checker

/-!
# Soundness of the positive definiteness checker

`pdCheck n K E DE B L = true` implies `DE · ∑ |xᵢ|² ≤ E · Re (x* B x)` for every `x`, where `B` is
the symmetric matrix with lower triangle `B` (`hform`). The proof: `R = E·B - K·L Lᵀ` is
diagonally dominant with margin `DE`, so `Re (x* R x) ≥ DE ∑ |xᵢ|²`, and `x* L Lᵀ x ≥ 0`.
-/

open Complex Finset

noncomputable section

namespace LoewnerS0.Cex

/-! ### List matrices -/

/-- the entry `(i, j)` of a matrix given by its rows -/
def ent (A : List (List ℤ)) (i j : ℕ) : ℤ := (A.getD i []).getD j 0

/-- the symmetric matrix whose lower triangle is `A` -/
def symEnt (A : List (List ℤ)) (i j : ℕ) : ℤ := if j ≤ i then ent A i j else ent A j i

lemma symEnt_comm (A : List (List ℤ)) (i j : ℕ) : symEnt A i j = symEnt A j i := by
  unfold symEnt
  split_ifs with h1 h2 <;> first | rfl | (have : i = j := le_antisymm h2 h1; subst this; rfl) | omega

/-- the Hermitian form `∑_{i,j<n} A_ij conj(xᵢ) xⱼ` of the symmetric matrix with lower
triangle `A` -/
def hform (n : ℕ) (A : List (List ℤ)) (x : ℕ → ℂ) : ℂ :=
  ∑ i ∈ range n, ∑ j ∈ range n, (symEnt A i j : ℂ) * (starRingEnd ℂ (x i) * x j)

/-! ### A Gershgorin-type estimate -/

lemma re_conj_mul_le (a b : ℂ) : -(‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 ≤ (starRingEnd ℂ a * b).re := by
  have h1 : |(starRingEnd ℂ a * b).re| ≤ ‖a‖ * ‖b‖ := by
    calc |(starRingEnd ℂ a * b).re| ≤ ‖starRingEnd ℂ a * b‖ := Complex.abs_re_le_norm _
      _ = ‖a‖ * ‖b‖ := by rw [norm_mul, Complex.norm_conj]
  have h2 : ‖a‖ * ‖b‖ ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  linarith [neg_abs_le (starRingEnd ℂ a * b).re]

lemma re_conj_mul_self (a : ℂ) : (starRingEnd ℂ a * a).re = ‖a‖ ^ 2 := by
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- a real symmetric matrix that is diagonally dominant with margin `c` satisfies
`Re (x* M x) ≥ c |x|²` -/
lemma re_form_ge_of_diagDom (n : ℕ) (M : ℕ → ℕ → ℝ) (hM : ∀ i j, M i j = M j i) (c : ℝ)
    (hdd : ∀ i < n, ∑ j ∈ range n, (if i = j then 0 else |M i j|) ≤ M i i - c) (x : ℕ → ℂ) :
    c * ∑ i ∈ range n, ‖x i‖ ^ 2 ≤
      (∑ i ∈ range n, ∑ j ∈ range n, (M i j : ℂ) * (starRingEnd ℂ (x i) * x j)).re := by
  have hre : (∑ i ∈ range n, ∑ j ∈ range n, (M i j : ℂ) * (starRingEnd ℂ (x i) * x j)).re =
      ∑ i ∈ range n, ∑ j ∈ range n, M i j * (starRingEnd ℂ (x i) * x j).re := by
    simp only [Complex.re_sum, Complex.re_ofReal_mul]
  rw [hre]
  -- termwise lower bound
  have hterm : ∀ i j, (if i = j then M i i * ‖x i‖ ^ 2 else
      -(|M i j| * (‖x i‖ ^ 2 + ‖x j‖ ^ 2) / 2)) ≤ M i j * (starRingEnd ℂ (x i) * x j).re := by
    intro i j
    split_ifs with h
    · subst h; rw [re_conj_mul_self]
    · have h1 := re_conj_mul_le (x i) (x j)
      have h2 : |(starRingEnd ℂ (x i) * x j).re| ≤ (‖x i‖ ^ 2 + ‖x j‖ ^ 2) / 2 := by
        have := re_conj_mul_le (x i) (x j)
        have h3 : (starRingEnd ℂ (x i) * x j).re ≤ ‖x i‖ * ‖x j‖ := by
          calc (starRingEnd ℂ (x i) * x j).re ≤ ‖starRingEnd ℂ (x i) * x j‖ :=
                Complex.re_le_norm _
            _ = ‖x i‖ * ‖x j‖ := by rw [norm_mul, Complex.norm_conj]
        have h4 : ‖x i‖ * ‖x j‖ ≤ (‖x i‖ ^ 2 + ‖x j‖ ^ 2) / 2 := by
          nlinarith [sq_nonneg (‖x i‖ - ‖x j‖)]
        rw [abs_le]; constructor <;> linarith
      have h5 : -(|M i j| * ((‖x i‖ ^ 2 + ‖x j‖ ^ 2) / 2)) ≤
          M i j * (starRingEnd ℂ (x i) * x j).re := by
        have := abs_mul (M i j) (starRingEnd ℂ (x i) * x j).re
        have h6 : |M i j * (starRingEnd ℂ (x i) * x j).re| ≤
            |M i j| * ((‖x i‖ ^ 2 + ‖x j‖ ^ 2) / 2) := by
          rw [this]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        linarith [neg_abs_le (M i j * (starRingEnd ℂ (x i) * x j).re)]
      linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ range n) =>
    Finset.sum_le_sum fun j (_ : j ∈ range n) => hterm i j
  refine le_trans ?_ hsum
  -- evaluate the lower bound
  set a : ℕ → ℝ := fun i => ‖x i‖ ^ 2 with ha
  set m : ℕ → ℕ → ℝ := fun i j => if i = j then 0 else |M i j| with hm
  have hsplit : ∀ i j, (if i = j then M i i * ‖x i‖ ^ 2 else
      -(|M i j| * (‖x i‖ ^ 2 + ‖x j‖ ^ 2) / 2)) =
      (if i = j then M i i * a i else 0) - m i j * a i / 2 - m i j * a j / 2 := by
    intro i j
    by_cases h : i = j
    · subst h; simp [hm, ha]
    · simp [h, hm, ha]; ring
  simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_range]
  have hswap : ∑ i ∈ range n, ∑ j ∈ range n, m i j * a j / 2 =
      ∑ i ∈ range n, ∑ j ∈ range n, m i j * a i / 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hm]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h, hM j i]
  rw [hswap]
  have hrow : ∀ i ∈ range n, ∑ j ∈ range n, m i j * a i / 2 = (∑ j ∈ range n, m i j) * a i / 2 := by
    intro i _
    rw [Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_congr rfl hrow]
  have hfinal : ∀ i ∈ range n, c * a i ≤
      (if i < n then M i i * a i else 0) - (∑ j ∈ range n, m i j) * a i / 2 -
        (∑ j ∈ range n, m i j) * a i / 2 := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have := hdd i hi'
    have hai : 0 ≤ a i := sq_nonneg _
    simp only [hi', ite_true]
    nlinarith
  calc c * ∑ i ∈ range n, ‖x i‖ ^ 2 = ∑ i ∈ range n, c * a i := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ range n, ((if i < n then M i i * a i else 0) - (∑ j ∈ range n, m i j) * a i / 2 -
        (∑ j ∈ range n, m i j) * a i / 2) := Finset.sum_le_sum hfinal
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

/-! ### The checker -/

lemma lowerShape_spec : ∀ (i₀ : ℕ) (A : List (List ℤ)), lowerShape i₀ A = true →
    ∀ i < A.length, (A.getD i []).length = i₀ + i + 1
  | _, [], _ => fun i hi => absurd hi (by simp)
  | i₀, r :: rs, h => by
    simp only [lowerShape, Bool.and_eq_true, decide_eq_true_eq] at h
    intro i hi
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := lowerShape_spec (i₀ + 1) rs h.2 i (by simpa using hi)
      simpa [show i₀ + (i + 1) + 1 = i₀ + 1 + i + 1 by omega] using this

lemma dot_eq_sum : ∀ (u v : List ℤ) (N : ℕ), u.length ≤ N →
    dot u v = ∑ k ∈ range N, u.getD k 0 * v.getD k 0
  | [], v, N, _ => by simp [dot]
  | a :: as, [], N, _ => by
    rw [show dot (a :: as) [] = 0 from rfl]
    simp
  | a :: as, b :: bs, N, h => by
    obtain ⟨N, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by simp at h; omega⟩
    rw [show dot (a :: as) (b :: bs) = a * b + dot as bs from rfl,
      dot_eq_sum as bs N (by simpa using h), Finset.sum_range_succ']
    simp [add_comm]

lemma length_rRows (K E : ℤ) (Lall : List (List ℤ)) : ∀ (Bs Ls : List (List ℤ)),
    (rRows K E Lall Bs Ls).length = min Bs.length Ls.length
  | [], _ => by simp [rRows]
  | _ :: _, [] => by simp [rRows]
  | _ :: Bs, _ :: Ls => by simp [rRows, length_rRows K E Lall Bs Ls, Nat.succ_min_succ]

lemma getD_rRows (K E : ℤ) (Lall : List (List ℤ)) : ∀ (Bs Ls : List (List ℤ)) (i : ℕ),
    i < Bs.length → i < Ls.length →
    (rRows K E Lall Bs Ls).getD i [] =
      List.zipWith (fun b Lj => b * E - K * dot (Ls.getD i []) Lj) (Bs.getD i []) Lall
  | [], _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, _, h => absurd h (by simp)
  | Bi :: Bs, Li :: Ls, 0, _, _ => by simp [rRows]
  | Bi :: Bs, Li :: Ls, i + 1, h1, h2 => by
    simpa [rRows] using getD_rRows K E Lall Bs Ls i (by simpa using h1) (by simpa using h2)

lemma absInit_eq : ∀ r : List ℤ,
    absInit r = ∑ j ∈ range (r.length - 1), (r.getD j 0).natAbs
  | [] => by simp [absInit]
  | [_] => by simp [absInit]
  | x :: y :: ys => by
    rw [absInit, absInit_eq (y :: ys)]
    simp only [List.length_cons, Nat.add_sub_cancel]
    rw [Finset.sum_range_succ']
    simp [add_comm]

lemma lastD_eq : ∀ r : List ℤ, r ≠ [] → lastD r = r.getD (r.length - 1) 0
  | [], h => absurd rfl h
  | [_], _ => by simp [lastD]
  | x :: y :: ys, _ => by
    rw [lastD, lastD_eq (y :: ys) (by simp)]
    simp

lemma getD_addAbsInit : ∀ (acc : List ℕ) (r : List ℤ) (j : ℕ),
    (addAbsInit acc r).getD j 0 =
      acc.getD j 0 + (if j + 1 < r.length then (r.getD j 0).natAbs else 0)
  | acc, [], j => by simp [addAbsInit]
  | acc, [_], j => by simp [addAbsInit]
  | acc, x :: y :: ys, 0 => by
    simp [addAbsInit]
    cases acc <;> simp
  | acc, x :: y :: ys, j + 1 => by
    rw [addAbsInit, List.getD_cons_succ, getD_addAbsInit acc.tail (y :: ys) j]
    cases acc <;> simp

lemma getD_colAbs : ∀ (R : List (List ℤ)) (j : ℕ), (colAbs R).getD j 0 =
    ∑ k ∈ range R.length, (if j + 1 < (R.getD k []).length then ((R.getD k []).getD j 0).natAbs
      else 0)
  | [], j => by simp [colAbs]
  | r :: rs, j => by
    rw [colAbs, getD_addAbsInit, getD_colAbs rs j, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

lemma getD_eq_getElem' {α : Type*} (l : List α) (d : α) {i : ℕ} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

lemma headD_eq_getD {α : Type*} (l : List α) (d : α) : l.headD d = l.getD 0 d := by
  cases l <;> rfl

lemma getD_tail {α : Type*} (l : List α) (d : α) (i : ℕ) : l.tail.getD i d = l.getD (i + 1) d := by
  cases l <;> simp

lemma ddCheck_spec (DE : ℤ) : ∀ (R : List (List ℤ)) (cs : List ℕ), ddCheck DE R cs = true →
    ∀ i < R.length, (absInit (R.getD i []) : ℤ) + (cs.getD i 0 : ℤ) ≤ lastD (R.getD i []) - DE
  | [], _, _ => fun i hi => absurd hi (by simp)
  | r :: rs, cs, h => by
    simp only [ddCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    intro i hi
    cases i with
    | zero =>
      rw [headD_eq_getD] at h
      simpa using h.1
    | succ i =>
      have := ddCheck_spec DE rs cs.tail h.2 i (by simpa using hi)
      rw [getD_tail] at this
      simpa using this

/-- **Soundness of `pdCheck`.** -/
theorem pdCheck_sound {n : ℕ} {K E DE : ℤ} {B L : List (List ℤ)} (hK : 0 ≤ K)
    (h : pdCheck n K E DE B L = true) (x : ℕ → ℂ) :
    (DE : ℝ) * ∑ i ∈ range n, ‖x i‖ ^ 2 ≤ (E : ℝ) * (hform n B x).re := by
  simp only [pdCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hB, hL⟩, hBs⟩, hLs⟩, hdd⟩ := h
  set R := rRows K E L B L with hR
  have hBs' := lowerShape_spec 0 B hBs
  have hLs' := lowerShape_spec 0 L hLs
  have hRlen : R.length = n := by rw [hR, length_rRows, hB, hL, min_self]
  -- the rows of `R`
  have hRrow : ∀ i < n, R.getD i [] =
      List.zipWith (fun b Lj => b * E - K * dot (L.getD i []) Lj) (B.getD i []) L :=
    fun i hi => getD_rRows K E L B L i (by omega) (by omega)
  have hRlen_i : ∀ i < n, (R.getD i []).length = i + 1 := by
    intro i hi
    rw [hRrow i hi, List.length_zipWith, hBs' i (by omega)]
    omega
  -- the entries of `R`
  have hent : ∀ i < n, ∀ j ≤ i, ent R i j =
      ent B i j * E - K * ∑ k ∈ range n, ent L i k * ent L j k := by
    intro i hi j hj
    have hjB : j < (B.getD i []).length := by rw [hBs' i (by omega)]; omega
    have hjL : j < L.length := by omega
    simp only [ent]
    rw [hRrow i hi, getD_eq_getElem' _ _ (by rw [List.length_zipWith]; omega),
      List.getElem_zipWith, getD_eq_getElem' _ _ hjB, getD_eq_getElem' _ _ hjL]
    congr 2
    rw [← getD_eq_getElem' _ [] hjL]
    exact dot_eq_sum _ _ n (by rw [hLs' i (by omega)]; omega)
  have hLsym : ∀ i j, (∑ k ∈ range n, ent L i k * ent L j k) =
      ∑ k ∈ range n, ent L j k * ent L i k :=
    fun i j => Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hsym : ∀ i < n, ∀ j < n, symEnt R i j =
      symEnt B i j * E - K * ∑ k ∈ range n, ent L i k * ent L j k := by
    intro i hi j hj
    unfold symEnt
    split_ifs with hji
    · exact hent i hi j hji
    · rw [hent j hj i (by omega), hLsym]
  -- diagonal dominance of `R`
  have hddR : ∀ i < n, ∑ j ∈ range n, (if i = j then (0 : ℝ) else |(symEnt R i j : ℝ)|) ≤
      (symEnt R i i : ℝ) - DE := by
    intro i hi
    have h1 := ddCheck_spec DE R (colAbs R) hdd i (by omega)
    have hne : R.getD i [] ≠ [] := by
      intro h0; have := hRlen_i i hi; rw [h0] at this; simp at this
    have hlast : lastD (R.getD i []) = ent R i i := by
      rw [lastD_eq _ hne, hRlen_i i hi, Nat.add_sub_cancel]; rfl
    have habs : ((absInit (R.getD i []) : ℕ) : ℝ) = ∑ j ∈ range i, |(ent R i j : ℝ)| := by
      rw [absInit_eq, hRlen_i i hi, Nat.add_sub_cancel]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.cast_natAbs, Int.cast_abs]; rfl
    have hcol : (((colAbs R).getD i 0 : ℕ) : ℝ) =
        ∑ k ∈ range n, (if i < k then |(ent R k i : ℝ)| else 0) := by
      rw [getD_colAbs, hRlen]
      push_cast
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hRlen_i k (Finset.mem_range.mp hk)]
      by_cases hik : i < k
      · rw [ite_eq_left (by omega), ite_eq_left hik, Nat.cast_natAbs, Int.cast_abs]; rfl
      · rw [ite_eq_right (by omega), ite_eq_right hik]
    have h1' : ((absInit (R.getD i []) : ℕ) : ℝ) + (((colAbs R).getD i 0 : ℕ) : ℝ) ≤
        (ent R i i : ℝ) - DE := by
      rw [← hlast]; exact_mod_cast h1
    rw [habs, hcol] at h1'
    have hdiag : symEnt R i i = ent R i i := by simp [symEnt]
    rw [hdiag]
    refine le_trans (le_of_eq ?_) h1'
    have e1 : ∀ j ∈ range n, (if i = j then (0 : ℝ) else |(symEnt R i j : ℝ)|) =
        (if j < i then |(ent R i j : ℝ)| else 0) + (if i < j then |(ent R j i : ℝ)| else 0) := by
      intro j _
      unfold symEnt
      rcases lt_trichotomy j i with hji | rfl | hji
      · rw [ite_eq_right (Ne.symm hji.ne), ite_eq_left hji.le, ite_eq_left hji, ite_eq_right (not_lt.mpr hji.le),
          add_zero]
      · simp
      · rw [ite_eq_right hji.ne, ite_eq_right (not_le.mpr hji), ite_eq_right (not_lt.mpr hji.le), ite_eq_left hji,
          zero_add]
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  -- `Re (x* R x) ≥ DE |x|²`
  have hR' := re_form_ge_of_diagDom n (fun i j => (symEnt R i j : ℝ))
    (fun i j => by simp [symEnt_comm R i j]) (DE : ℝ) hddR x
  -- `x* R x = E x* B x - K ∑ₖ |yₖ|²`
  have hy : ∀ k, starRingEnd ℂ (∑ i ∈ range n, (ent L i k : ℂ) * x i) *
      (∑ j ∈ range n, (ent L j k : ℂ) * x j) =
      ∑ i ∈ range n, ∑ j ∈ range n, (ent L i k : ℂ) * (ent L j k : ℂ) *
        (starRingEnd ℂ (x i) * x j) := by
    intro k
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_intCast]
    ring
  have h3 : ∑ k ∈ range n, ∑ i ∈ range n, ∑ j ∈ range n,
      (ent L i k : ℂ) * (ent L j k : ℂ) * (starRingEnd ℂ (x i) * x j) =
      ∑ i ∈ range n, ∑ j ∈ range n,
        (∑ k ∈ range n, (ent L i k : ℂ) * (ent L j k : ℂ)) * (starRingEnd ℂ (x i) * x j) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  have hform_R : (∑ i ∈ range n, ∑ j ∈ range n,
      (((symEnt R i j : ℝ)) : ℂ) * (starRingEnd ℂ (x i) * x j)) =
      (E : ℂ) * hform n B x - (K : ℂ) * ∑ k ∈ range n,
        starRingEnd ℂ (∑ i ∈ range n, (ent L i k : ℂ) * x i) *
          (∑ j ∈ range n, (ent L j k : ℂ) * x j) := by
    simp_rw [hy]
    rw [h3]
    unfold hform
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hsym i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)]
    push_cast
    ring
  rw [hform_R] at hR'
  have hpos : 0 ≤ (∑ k ∈ range n, starRingEnd ℂ (∑ i ∈ range n, (ent L i k : ℂ) * x i) *
      (∑ j ∈ range n, (ent L j k : ℂ) * x j)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun k _ => by rw [re_conj_mul_self]; exact sq_nonneg _
  have hK' : (0 : ℝ) ≤ K := by exact_mod_cast hK
  have hre : ∀ (k : ℤ) (z : ℂ), ((k : ℂ) * z).re = (k : ℝ) * z.re := by
    intro k z; simp [Complex.mul_re]
  rw [Complex.sub_re, hre, hre] at hR'
  nlinarith [mul_nonneg hK' hpos]

end LoewnerS0.Cex
