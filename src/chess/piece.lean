/-!

Chess piece implementation.

-/

namespace chess

@[derive decidable_eq]
inductive color
| white
| black

@[derive decidable_eq]
inductive pieces
| bishop
| king
| knight
| pawn
| queen
| rook

@[derive decidable_eq]
structure colored_pieces :=
(piece : pieces)
(color : color)

@[pattern] def white_bishop : colored_pieces := ⟨pieces.bishop, color.white⟩
@[pattern] def white_king : colored_pieces := ⟨pieces.king, color.white⟩
@[pattern] def white_knight : colored_pieces := ⟨pieces.knight, color.white⟩
@[pattern] def white_pawn : colored_pieces := ⟨pieces.pawn, color.white⟩
@[pattern] def white_queen : colored_pieces := ⟨pieces.queen, color.white⟩
@[pattern] def white_rook : colored_pieces := ⟨pieces.rook, color.white⟩

@[pattern] def black_bishop : colored_pieces := ⟨pieces.bishop, color.black⟩
@[pattern] def black_king : colored_pieces := ⟨pieces.king, color.black⟩
@[pattern] def black_knight : colored_pieces := ⟨pieces.knight, color.black⟩
@[pattern] def black_pawn : colored_pieces := ⟨pieces.pawn, color.black⟩
@[pattern] def black_queen : colored_pieces := ⟨pieces.queen, color.black⟩
@[pattern] def black_rook : colored_pieces := ⟨pieces.rook, color.black⟩

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

def piece_repr : colored_pieces → string
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

instance : has_repr colored_pieces := ⟨piece_repr⟩

end chess
