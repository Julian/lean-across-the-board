import chess.piece
import chess.algebraic.utils

open chess

namespace chess

open piece

namespace piece

def unicode_symbol : piece → char
| ♔ := '♔'
| ♕ := '♕'
| ♖ := '♖'
| ♗ := '♗'
| ♘ := '♘'
| ♙ := '♙'

def char_symbol : piece → char
| ♔ := 'K'
| ♕ := 'Q'
| ♖ := 'R'
| ♗ := 'B'
| ♘ := 'N'
| ♙ := 'P'

def piece_repr : piece → string
| ♔ := "♔"
| ♕ := "♕"
| ♖ := "♖"
| ♗ := "♗"
| ♘ := "♘"
| ♙ := "♙"

instance : has_repr piece := ⟨piece_repr⟩

def parser (x : piece) : parser piece :=
(parser.ch x.char_symbol <|> parser.ch x.unicode_symbol) $> x

end piece

def parser : parser piece :=
asum (piece.parser <$> [king, queen, rook, bishop, knight, pawn])

#eval parser.run_string (chess.parser) "♗"
#eval parser.run_string (chess.parser) "K"
#eval parser.run_string (chess.parser) "N"
#eval parser.run_string (chess.parser.many) "KQRBNP"
#eval parser.run_string (chess.parser.many) "KQRBNX"


end chess
