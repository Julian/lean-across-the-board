/-!

Chess piece implementation.

-/

namespace chess

@[derive decidable_eq]
inductive color
| white
| black

@[derive decidable_eq]
inductive piece
| bishop
| king
| knight
| pawn
| queen
| rook

@[derive decidable_eq]
structure colored_piece :=
(piece : piece)
(color : color)

@[pattern] def white_bishop : colored_piece := ⟨piece.bishop, color.white⟩
@[pattern] def white_king : colored_piece := ⟨piece.king, color.white⟩
@[pattern] def white_knight : colored_piece := ⟨piece.knight, color.white⟩
@[pattern] def white_pawn : colored_piece := ⟨piece.pawn, color.white⟩
@[pattern] def white_queen : colored_piece := ⟨piece.queen, color.white⟩
@[pattern] def white_rook : colored_piece := ⟨piece.rook, color.white⟩

@[pattern] def black_bishop : colored_piece := ⟨piece.bishop, color.black⟩
@[pattern] def black_king : colored_piece := ⟨piece.king, color.black⟩
@[pattern] def black_knight : colored_piece := ⟨piece.knight, color.black⟩
@[pattern] def black_pawn : colored_piece := ⟨piece.pawn, color.black⟩
@[pattern] def black_queen : colored_piece := ⟨piece.queen, color.black⟩
@[pattern] def black_rook : colored_piece := ⟨piece.rook, color.black⟩

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

def piece_repr : colored_piece → string
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

instance : has_repr colored_piece := ⟨piece_repr⟩

end chess
