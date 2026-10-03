import LoewnerS0.Cex.Checker
import LoewnerS0.Cex.DataN
import LoewnerS0.Cex.DataB
import LoewnerS0.Cex.DataL

/-!
# The certificate data, unpacked
-/

namespace LoewnerS0.Cex

/-- the common denominator of all entries of all `C_l` -/
def LC : Nat := 40305583718400000000

/-- `LC · 10⁻⁶` -/
def LC6 : Nat := 40305583718400

/-- the scale `E = 4³⁰` of `L Lᵀ` -/
def Epow : Nat := 4 ^ 30

def binom14 : List Nat := [1, 14, 91, 364, 1001, 2002, 3003, 3432, 3003, 2002, 1001, 364, 91, 14, 1]

/-- entry-major data: `Ball[i][j] = [B₀ i j, …, B₁₄ i j]` -/
def Ball : List (List (List Int)) := BallData.map (·.map (unpack 80 15))

/-- the lower rows of `B_l = binom(14,l) · LC · C_l` -/
def Bmat (l : Nat) : List (List Int) := BallData.map (·.map (field 80 l))

/-- the rounded Cholesky factor for `l` -/
def Lmat (l : Nat) : List (List Int) := unpackRows 40 (LDs.getD l [])

/-- the positive definiteness check for `l` -/
def pdOK (l : Nat) : Bool :=
  pdCheck 52 (binom14.getD l 0 * LC) Epow (binom14.getD l 0 * LC6 * Epow) (Bmat l) (Lmat l)

/-- thresholds splitting the identity check into three pieces (this bounds the kernel's memory
use) -/
def cut1 : Nat := 68 * 128 * 64
def cut2 : Nat := 72 * 128 * 64

def piece1 (t : Term) : Bool := decide (t.key < cut1)
def piece2 (t : Term) : Bool := !decide (t.key < cut1) && decide (t.key < cut2)
def piece3 (t : Term) : Bool := !decide (t.key < cut1) && !decide (t.key < cut2)

end LoewnerS0.Cex
