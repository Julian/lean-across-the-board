/-!

Chess piece implementation.

-/

namespace chess

inductive color
| white
| black

inductive pieces
| bishop
| king
| knight
| pawn
| queen
| rook

class colored_pieces :=
(piece : pieces)
(color : color)

instance white_bishop : colored_pieces := ⟨pieces.bishop, color.white⟩
instance white_king : colored_pieces := ⟨pieces.king, color.white⟩
instance white_knight : colored_pieces := ⟨pieces.knight, color.white⟩
instance white_pawn : colored_pieces := ⟨pieces.pawn, color.white⟩
instance white_queen : colored_pieces := ⟨pieces.queen, color.white⟩
instance white_rook : colored_pieces := ⟨pieces.rook, color.white⟩

instance black_bishop : colored_pieces := ⟨pieces.bishop, color.black⟩
instance black_king : colored_pieces := ⟨pieces.king, color.black⟩
instance black_knight : colored_pieces := ⟨pieces.knight, color.black⟩
instance black_pawn : colored_pieces := ⟨pieces.pawn, color.black⟩
instance black_queen : colored_pieces := ⟨pieces.queen, color.black⟩
instance black_rook : colored_pieces := ⟨pieces.rook, color.black⟩

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

end chess
