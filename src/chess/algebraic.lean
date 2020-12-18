import chess.piece
import chess.algebraic.utils

open chess

namespace chess

open piece parser list (mfirst)

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

abbreviation promotions : Type := {p : piece // p = ♕ ∨ p = ♖ ∨ p = ♗ ∨ p = ♘}

instance : has_repr piece := ⟨piece_repr⟩

def parser' (x : piece) : parser piece :=
(ch x.char_symbol <|> ch x.unicode_symbol) $> x

def promotions.parser' : parser piece :=
decorate_error "<promotions>" $ mfirst parser' [queen, rook, bishop, knight]

-- lemma promotions.parser'_not_king (cb n) (h : promtions.parser' cb n ≠ parse_result.fail): promotions.parser' cb n

def parser : parser piece :=
decorate_error "<piece>" $ mfirst parser' [king, queen, rook, bishop, knight, pawn]

end piece

@[derive [decidable_eq, fintype]]
inductive capture
| capture
| noncapture

def capture.repr : capture → string
| capture.capture := "capture"
| capture.noncapture := "noncapture"

instance capture_has_repr : has_repr capture := ⟨capture.repr⟩

variables {α β : Type} [has_zero α] [has_one α] [has_add α] [has_zero β] [has_one β] [has_add β]

def file.parser' : parser α := numeral.char _ 'a' 'z'
def file.parser [fintype α] : parser α := numeral.char.of_fintype _ 'a'
def rank.parser' : parser α := numeral.from_one α
def rank.parser [fintype α] : parser α := numeral.from_one.of_fintype α
def square.parser' : parser (α × β) :=
(λ x y, ⟨y, x⟩) <$> file.parser' <*> rank.parser'
def square.parser [fintype α] [fintype β] : parser (α × β) :=
(λ x y, ⟨y, x⟩) <$> file.parser <*> rank.parser
def square.parser.optional [fintype α] [fintype β] : parser (option α × option β) :=
(λ x y, ⟨y, x⟩) <$> (some <$> file.parser <|> pure none) <*> (some <$> rank.parser <|> pure none)
def capture.parser : parser capture :=
ch 'x' $> capture.capture <|> pure capture.noncapture

variables (α β)

structure move.description :=
(figure : piece)
(from_sq : (option α × option β))
(to_sq : (α × β))
(capture : capture)

instance move.description.has_repr [has_repr α] [has_repr β] : has_repr (move.description α β) :=
⟨λ ⟨p, fsq, tsq, c⟩, string.intercalate " " [repr p, repr fsq, repr tsq, repr c]⟩

structure pawn.capture.description extends move.description α β :=
(promoted : {p : piece // p ≠ pawn ∧ p ≠ king})

variables {α β}

def move.parser [fintype α] [fintype β] : parser (move.description α β) :=
(λ p fsq c tsq, ⟨p, fsq, tsq, c⟩) <$> piece.parser <*> square.parser.optional <*> capture.parser <*> square.parser

#eval run_string (piece.parser) "♗"
#eval run_string (piece.parser) "K"
#eval run_string (piece.parser) "N"
#eval run_string (piece.parser) "x"
#eval run_string (piece.parser.many) "KQRBNP"
#eval run_string (piece.parser.many) "KQRBNX"

#eval run_string (numeral (fin 300)) "001334"
#eval run_string (@file.parser' (fin 300) _ _ _) "a"
#eval run_string (@file.parser (fin 8) _ _ _ _) "a"
#eval run_string (@file.parser (fin 8) _ _ _ _) "h"
#eval run_string (@file.parser (fin 8) _ _ _ _) "i"
#eval run_string (@rank.parser (fin 300) _ _ _ _) "4"
#eval run_string (@square.parser (fin 300) (fin 300) _ _ _ _ _ _ _ _) "a4"

#eval run_string capture.parser ""

#eval run_string (@move.parser (fin 8) (fin 8) _ _ _ _ _ _ _ _) "Qd5xc8"

end chess
