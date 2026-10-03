/-!
# A computable checker for the sum-of-squares certificate

This file contains only computable definitions on `Nat`, `Int` and lists (it does not import
mathlib). They are evaluated by the Lean kernel (`decide +kernel`) in `LoewnerS0.Cex.CheckId` and
`LoewnerS0.Cex.CheckPD`, and their meaning is established in `LoewnerS0.Cex.Sound`.

The certificate (see `claude/disproof_starlike.tex`, Section 5) states that on the unit sphere
`S³ ⊂ ℂ²`, with `S = |w₁|²`, `T = |w₂|²`,

  `LC · F(w) = ∑_{l=0}^{14} Sˡ T^(14-l) · V(w)* Bₗ V(w)`,

where `Bₗ = binom(14,l) · LC · Cₗ` are integer matrices (`LC` = common denominator), `V(w)` is
the vector of the 52 monomials `χ_j(w₁) χ_k(w₂)`, `(j,k) ∈ {-6,…,6} × {-1,…,2}`, and
`χ_a(z) = z^a` for `a ≥ 0`, `χ_a(z) = z̄^|a|` for `a < 0`.

## Identity check

Both sides are written as sums of *symmetric terms*
`(∑ₖ vₖ Sᵏ T^(d-k)) · (χ_Δ + χ_{-Δ})`, `χ_Δ(w) = χ_{Δ₁}(w₁) χ_{Δ₂}(w₂)` (`Term`).
Terms with the same `(Δ, d)` are added (`msort`), then terms with the same `Δ` are brought to a
common degree `d` using `S + T = 1` (`elev`) and added (`combineMode`). The check is that all
resulting coefficient vectors vanish.

## Positive definiteness check

For each `l` we are given an integer lower-triangular matrix `L` (a rounded Cholesky factor of
`Cₗ - 3·10⁻⁶ I`, scaled by `2³⁰`). We check that `R = E·Bₗ - K·L Lᵀ` (`E = 4³⁰`,
`K = binom(14,l)·LC`) is diagonally dominant with margin `DE`:
`∑_{j ≠ i} |R_ij| ≤ R_ii - DE`. This implies `E · V* Bₗ V ≥ DE · |V|²`.
-/

namespace LoewnerS0.Cex

/-! ### The vector `V` -/

/-- frequency in `w₁` of the `i`-th entry of `V` (window `{-6,…,6} × {-1,…,2}`, `j`-major) -/
def idxJ (i : Nat) : Int := Int.ofNat (i / 4) - 6

/-- frequency in `w₂` of the `i`-th entry of `V` -/
def idxK (i : Nat) : Int := Int.ofNat (i % 4) - 1

/-- the exponent of `|z|²` in `conj (χ_a z) * χ_b z` -/
def mm (a b : Int) : Nat :=
  if 0 ≤ a ∧ 0 ≤ b then (min a b).toNat
  else if a < 0 ∧ b < 0 then (min (-a) (-b)).toNat
  else 0

/-- the canonical representative of `{Δ, -Δ}` -/
def canonMode (d1 d2 : Int) : Int × Int :=
  if 0 < d1 ∨ (d1 = 0 ∧ 0 ≤ d2) then (d1, d2) else (-d1, -d2)

/-! ### Symmetric terms -/

/-- The symmetric term `(∑ₖ vec[k] Sᵏ T^(deg-k)) · (χ_(d1,d2) + χ_(-d1,-d2))`. -/
structure Term where
  d1 : Int
  d2 : Int
  deg : Nat
  vec : List Int

/-- `x` added to the first entry -/
def addHead (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => (x + y) :: ys

/-- degree elevation `d → d + 1`, based on `Sᵏ T^(d-k) = Sᵏ⁺¹ T^(d-k) + Sᵏ T^(d+1-k)` -/
def elev : List Int → List Int
  | [] => []
  | x :: xs => x :: addHead x (elev xs)

def elevN : Nat → List Int → List Int
  | 0, v => v
  | n + 1, v => elevN n (elev v)

def Term.neg (t : Term) : Term := ⟨t.d1, t.d2, t.deg, t.vec.map (- ·)⟩

/-- entrywise sum, the shorter list padded with zeros -/
def padAdd : List Int → List Int → List Int
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: padAdd xs ys

/-- sorting key: mode first, then decreasing degree -/
def Term.key (t : Term) : Nat :=
  ((t.d1 + 64).toNat * 128 + (t.d2 + 64).toNat) * 64 + (63 - t.deg)

def Term.same (t u : Term) : Bool := t.d1 == u.d1 && t.d2 == u.d2 && t.deg == u.deg

def Term.wf (t : Term) : Bool := decide (t.vec.length ≤ t.deg + 1)

/-- merge two lists (with fuel), adding terms with the same mode and degree -/
def mergeT : Nat → List Term → List Term → List Term
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | f + 1, x :: xs, y :: ys =>
    if x.same y then ⟨x.d1, x.d2, x.deg, padAdd x.vec y.vec⟩ :: mergeT f xs ys
    else if x.key ≤ y.key then x :: mergeT f xs (y :: ys)
    else y :: mergeT f (x :: xs) ys

def mergePairs : List (List Term) → List (List Term)
  | a :: b :: rest => mergeT (a.length + b.length) a b :: mergePairs rest
  | l => l

def msortAux : Nat → List (List Term) → List Term
  | 0, ls => ls.flatten
  | _ + 1, [] => []
  | _ + 1, [l] => l
  | f + 1, a :: b :: rest => msortAux f (mergePairs (a :: b :: rest))

/-- bottom-up merge sort by `Term.key`, adding terms with the same mode and degree -/
def msort (ts : List Term) : List Term := msortAux 32 (ts.map fun t => [t])

/-- Add up consecutive terms of the same mode. In a list sorted by `Term.key` the degrees of
the terms of one mode decrease, so the accumulated lower-degree part `u` is elevated to the
degree of `t` and added. -/
def combineMode : List Term → List Term
  | [] => []
  | t :: ts =>
    match combineMode ts with
    | [] => [t]
    | u :: us =>
      if t.d1 == u.d1 && t.d2 == u.d2 && decide (u.deg ≤ t.deg) && u.wf then
        ⟨t.d1, t.d2, t.deg, padAdd t.vec (elevN (t.deg - u.deg) u.vec)⟩ :: us
      else t :: u :: us

/-! ### The terms of the two sides -/

/-- the term of the lower entry `(i, j)`, `j ≤ i`, of `∑ₗ Sˡ T^(14-l) · 2 V* Bₗ V`;
`v = [B₀ i j, …, B₁₄ i j]` -/
def cTerm (i j : Nat) (v : List Int) : Term :=
  let a := idxJ i
  let b := idxJ j
  let c := idxK i
  let d := idxK j
  let Δ := canonMode (b - a) (d - c)
  let m := mm a b
  ⟨Δ.1, Δ.2, 14 + m + mm c d,
    List.replicate m 0 ++ v.map ((if i = j then (1 : Int) else 2) * ·)⟩

def genRow (i : Nat) : Nat → List (List Int) → List Term
  | _, [] => []
  | j, v :: vs => cTerm i j v :: genRow i (j + 1) vs

def genAll : Nat → List (List (List Int)) → List Term
  | _, [] => []
  | i, row :: rows => genRow i 0 row ++ genAll (i + 1) rows

/-- the symmetric term of the monomial `κ z₁^a z̄₁^a' z₂^b z̄₂^b'` (plus its conjugate) -/
def monoTerm (a a' b b' : Nat) (κ : Int) : Term :=
  let Δ := canonMode ((a : Int) - a') ((b : Int) - b')
  ⟨Δ.1, Δ.2, min a a' + min b b', List.replicate (min a a') 0 ++ [κ]⟩

/-- the monomials of `P = LC · (N₁ z̄₁ + N₂ z̄₂)(1 - r z̄₁)`, where a term `(comp, a, b, c)` of
`N` is `c/10⁴ · w₁^a w₂^b` in component `comp` (`1` or `2`); `KP = LC/10⁴`, `KR = LC·r/10⁴` -/
def pTerms (KP KR : Int) : List (Nat × Nat × Nat × Int) → List Term
  | [] => []
  | (comp, a, b, c) :: rest =>
    (if comp = 1 then [monoTerm a 1 b 0 (KP * c), monoTerm a 2 b 0 (-(KR * c))]
     else [monoTerm a 0 b 1 (KP * c), monoTerm a 1 b 1 (-(KR * c))]) ++ pTerms KP KR rest

/-- all terms of `∑ₗ Sˡ T^(14-l) · 2 V* Bₗ V - (P + P̄)` -/
def allTerms (Ball : List (List (List Int))) (NT : List (Nat × Nat × Nat × Int)) (KP KR : Int) :
    List Term :=
  genAll 0 Ball ++ (pTerms KP KR NT).map Term.neg

/-- the identity check, restricted to the terms selected by `p` -/
def pieceOK (Ball : List (List (List Int))) (NT : List (Nat × Nat × Nat × Int)) (KP KR : Int)
    (p : Term → Bool) : Bool :=
  (combineMode (msort ((allTerms Ball NT KP KR).filter p))).all fun t => t.vec.all (· == 0)

/-- row `i` has `i + 1` entries, each a list of length `L` -/
def shapeOK (L : Nat) : Nat → List (List (List Int)) → Bool
  | _, [] => true
  | i, row :: rows =>
    decide (row.length = i + 1) && row.all (fun v => v.length == L) && shapeOK L (i + 1) rows

/-! ### Positive definiteness -/

def dot : List Int → List Int → Int
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

/-- lower rows of `R = E·B - K·L Lᵀ` -/
def rRows (K E : Int) (Lall : List (List Int)) : List (List Int) → List (List Int) →
    List (List Int)
  | Bi :: Bs, Li :: Ls =>
    List.zipWith (fun b Lj => b * E - K * dot Li Lj) Bi Lall :: rRows K E Lall Bs Ls
  | _, _ => []

/-- `∑ |x|` over all but the last entry -/
def absInit : List Int → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: ys => x.natAbs + absInit (y :: ys)

/-- the last entry -/
def lastD : List Int → Int
  | [] => 0
  | [x] => x
  | _ :: y :: ys => lastD (y :: ys)

/-- add `|r_j|` to `acc_j` for all but the last entry of `r` (the other entries of `acc` are
kept) -/
def addAbsInit : List Nat → List Int → List Nat
  | acc, [] => acc
  | acc, [_] => acc
  | acc, x :: y :: ys => (acc.headD 0 + x.natAbs) :: addAbsInit acc.tail (y :: ys)

/-- the column sums `∑_{k > j} |R_kj|` of a lower-triangular matrix -/
def colAbs : List (List Int) → List Nat
  | [] => []
  | r :: rs => addAbsInit (colAbs rs) r

/-- diagonal dominance with margin `DE` -/
def ddCheck (DE : Int) : List (List Int) → List Nat → Bool
  | [], _ => true
  | r :: rs, cs =>
    decide ((absInit r : Int) + (cs.headD 0 : Int) ≤ lastD r - DE) && ddCheck DE rs cs.tail

/-- row `i` has length `i + 1` -/
def lowerShape : Nat → List (List Int) → Bool
  | _, [] => true
  | i, r :: rs => decide (r.length = i + 1) && lowerShape (i + 1) rs

def pdCheck (n : Nat) (K E DE : Int) (B L : List (List Int)) : Bool :=
  decide (B.length = n) && decide (L.length = n) && lowerShape 0 B && lowerShape 0 L &&
    (let R := rRows K E L B L
     ddCheck DE R (colAbs R))

/-! ### Unpacking the data -/

/-- the `l`-th `W`-bit field of a packed value (offset binary) -/
def field (W l x : Nat) : Int := Int.ofNat ((x >>> (W * l)) % 2 ^ W) - Int.ofNat (2 ^ (W - 1))

/-- the first `n` fields -/
def unpack (W n x : Nat) : List Int := (List.range n).map fun k => field W k x

/-- a packed lower-triangular matrix (row `i` packed into one number) -/
def unpackRows (W : Nat) (rows : List Nat) : List (List Int) :=
  (List.range rows.length).map fun i => unpack W (i + 1) (rows.getD i 0)

end LoewnerS0.Cex
