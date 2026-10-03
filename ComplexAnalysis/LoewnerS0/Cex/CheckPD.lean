import LoewnerS0.Cex.CheckPD0
import LoewnerS0.Cex.CheckPD1
import LoewnerS0.Cex.CheckPD2

/-!
# All 15 positive semidefiniteness checks
-/

namespace LoewnerS0.Cex

theorem pdOK_all : ∀ l < 15, pdOK l = true := by
  intro l hl
  match l, hl with
  | 0, _ => exact pdOK_0
  | 1, _ => exact pdOK_1
  | 2, _ => exact pdOK_2
  | 3, _ => exact pdOK_3
  | 4, _ => exact pdOK_4
  | 5, _ => exact pdOK_5
  | 6, _ => exact pdOK_6
  | 7, _ => exact pdOK_7
  | 8, _ => exact pdOK_8
  | 9, _ => exact pdOK_9
  | 10, _ => exact pdOK_10
  | 11, _ => exact pdOK_11
  | 12, _ => exact pdOK_12
  | 13, _ => exact pdOK_13
  | 14, _ => exact pdOK_14
  | n + 15, h => exact absurd h (Nat.not_lt.mpr (Nat.le_add_left 15 n))

end LoewnerS0.Cex
