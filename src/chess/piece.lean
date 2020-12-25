import tactic.derive_fintype

/-!

Chess piece implementation.

-/

namespace chess

@[derive [decidable_eq, fintype]]
inductive color
| white
| black

@[derive [decidable_eq, fintype]]
inductive piece
| bishop
| king
| knight
| pawn
| queen
| rook

@[derive [decidable_eq, fintype]]
structure colored_piece :=
(piece : piece)
(color : color)

/-- "Forget" a piece's color. -/
instance : has_coe colored_piece piece := ⟨colored_piece.piece⟩

@[simp] protected lemma coe {p : colored_piece} : (p : piece) = p.piece := rfl

@[pattern, simps] def white_bishop : colored_piece := ⟨piece.bishop, color.white⟩
@[pattern, simps] def white_king : colored_piece := ⟨piece.king, color.white⟩
@[pattern, simps] def white_knight : colored_piece := ⟨piece.knight, color.white⟩
@[pattern, simps] def white_pawn : colored_piece := ⟨piece.pawn, color.white⟩
@[pattern, simps] def white_queen : colored_piece := ⟨piece.queen, color.white⟩
@[pattern, simps] def white_rook : colored_piece := ⟨piece.rook, color.white⟩

@[pattern, simps] def black_bishop : colored_piece := ⟨piece.bishop, color.black⟩
@[pattern, simps] def black_king : colored_piece := ⟨piece.king, color.black⟩
@[pattern, simps] def black_knight : colored_piece := ⟨piece.knight, color.black⟩
@[pattern, simps] def black_pawn : colored_piece := ⟨piece.pawn, color.black⟩
@[pattern, simps] def black_queen : colored_piece := ⟨piece.queen, color.black⟩
@[pattern, simps] def black_rook : colored_piece := ⟨piece.rook, color.black⟩

notation ` ♔ ` := chess.white_king
notation ` ♕ ` := chess.white_queen
notation ` ♖ ` := chess.white_rook
notation ` ♗ ` := chess.white_bishop
notation ` ♘ ` := chess.white_knight
notation ` ♙ ` := chess.white_pawn

notation ` ♚ ` := chess.black_king
notation ` ♛ ` := chess.black_queen
notation ` ♜ ` := chess.black_rook
notation ` ♝ ` := chess.black_bishop
notation ` ♞ ` := chess.black_knight
notation ` ♟︎ ` := chess.black_pawn

notation ` __ ` := none

def colored_piece_repr : colored_piece → string
| ♔ := "♔"
| ♕ := "♕"
| ♖ := "♖"
| ♗ := "♗"
| ♘ := "♘"
| ♙ := "♙"
| ♚ := "♚"
| ♛ := "♛"
| ♜ := "♜"
| ♝ := "♝"
| ♞ := "♞"
| ♟︎ := "♟︎"

instance : has_repr colored_piece := ⟨colored_piece_repr⟩

def piece_repr : piece → string
| ♔ := "♔"
| ♕ := "♕"
| ♖ := "♖"
| ♗ := "♗"
| ♘ := "♘"
| ♙ := "♙"

instance : has_repr piece := ⟨piece_repr⟩

abbreviation promotions : Type := {p : piece // p = ♕ ∨ p = ♖ ∨ p = ♗ ∨ p = ♘}

@[derive [decidable_eq, fintype]]
inductive capture
| capture

def capture.repr : capture → string
| capture.capture := "capture"

instance capture_has_repr : has_repr capture := ⟨capture.repr⟩

@[derive [decidable_eq, fintype]]
inductive castle
| kings
| queens

def castle.repr : castle → string
| castle.kings := "kingside"
| castle.queens := "queenside"

end chess
