import LoewnerS0.Cex.Data

/-!
# Kernel check of the identity `F = ∑ₗ b_l V* C_l V` on `S³`

Each theorem is checked by the Lean kernel (`decide +kernel`); there is no `native_decide`.
-/

namespace LoewnerS0.Cex

theorem ball_length : Ball.length = 52 := by decide +kernel

theorem ball_shape : shapeOK 15 0 Ball = true := by decide +kernel

theorem identity_piece1 : pieceOK Ball NT KP KR piece1 = true := by decide +kernel

theorem identity_piece2 : pieceOK Ball NT KP KR piece2 = true := by decide +kernel

theorem identity_piece3 : pieceOK Ball NT KP KR piece3 = true := by decide +kernel

end LoewnerS0.Cex
