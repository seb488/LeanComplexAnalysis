import LoewnerS0.Cex.Data

/-!
# Kernel check that `C_l - 10⁻⁶ I` is positive semidefinite, `l = 10, …, 14`

Each theorem is checked by the Lean kernel (`decide +kernel`); there is no `native_decide`.
The 15 checks are split over three files so that they can be built in parallel.
-/

namespace LoewnerS0.Cex

theorem pdOK_10 : pdOK 10 = true := by decide +kernel

theorem pdOK_11 : pdOK 11 = true := by decide +kernel

theorem pdOK_12 : pdOK 12 = true := by decide +kernel

theorem pdOK_13 : pdOK 13 = true := by decide +kernel

theorem pdOK_14 : pdOK 14 = true := by decide +kernel

end LoewnerS0.Cex
