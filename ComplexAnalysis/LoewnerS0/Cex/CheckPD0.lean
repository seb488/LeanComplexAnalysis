import LoewnerS0.Cex.Data

/-!
# Kernel check that `C_l - 10⁻⁶ I` is positive semidefinite, `l = 0, …, 4`

Each theorem is checked by the Lean kernel (`decide +kernel`); there is no `native_decide`.
The 15 checks are split over three files so that they can be built in parallel.
-/

namespace LoewnerS0.Cex

theorem pdOK_0 : pdOK 0 = true := by decide +kernel

theorem pdOK_1 : pdOK 1 = true := by decide +kernel

theorem pdOK_2 : pdOK 2 = true := by decide +kernel

theorem pdOK_3 : pdOK 3 = true := by decide +kernel

theorem pdOK_4 : pdOK 4 = true := by decide +kernel

end LoewnerS0.Cex
