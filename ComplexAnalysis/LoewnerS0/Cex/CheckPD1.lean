import LoewnerS0.Cex.Data

/-!
# Kernel check that `C_l - 10⁻⁶ I` is positive semidefinite, `l = 5, …, 9`

Each theorem is checked by the Lean kernel (`decide +kernel`); there is no `native_decide`.
The 15 checks are split over three files so that they can be built in parallel.
-/

namespace LoewnerS0.Cex

theorem pdOK_5 : pdOK 5 = true := by decide +kernel

theorem pdOK_6 : pdOK 6 = true := by decide +kernel

theorem pdOK_7 : pdOK 7 = true := by decide +kernel

theorem pdOK_8 : pdOK 8 = true := by decide +kernel

theorem pdOK_9 : pdOK 9 = true := by decide +kernel

end LoewnerS0.Cex
