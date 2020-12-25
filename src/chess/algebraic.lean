import chess.piece
import chess.algebraic.utils
import chess.move.description

open chess

def parse_to_some {α : Type} (p : parser α) : string → option α :=
sum.elim (λ _, none) some ∘ parser.run_string p

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

def parser' : piece → parser piece :=
λ (x : piece), (ch x.char_symbol <|> ch x.unicode_symbol) $> x

def promotions.parser' : parser piece :=
decorate_error "<promotions>" $ mfirst parser' [queen, rook, bishop, knight]

lemma mem_of_mfirst_map_const_eq_done {α β} {f : α → parser β} {l : list α} {a}
  (h : a ∈ mfirst (λ x, f x $> x) l) : a ∈ l :=
begin
  obtain ⟨p, hp, hp'⟩ := mem_of_mfirst h,
  simp only [list.mem_map, list.map_eq_map] at hp,
  obtain ⟨x, hx, rfl⟩ := hp,
  simp only [mem_map_const_iff] at hp',
  exact hp'.left ▸ hx
end

lemma promotions.parser'_mem' {p : piece} (h : p ∈ promotions.parser') :
  p ∈ [queen, rook, bishop, knight] :=
begin
  simp only [promotions.parser', parser', mem_decorate_error_iff] at h,
  exact mem_of_mfirst_map_const_eq_done h
end

def promotions.parser : parser promotions :=
parser.attach promotions.parser' (λ p h, by {
  have H := promotions.parser'_mem' h,
  simp only [list.mem_cons_iff, list.mem_singleton] at H,
  exact H
})

def parser : parser piece :=
decorate_error "<piece>" $ mfirst parser' [king, queen, rook, bishop, knight, pawn]

end piece

instance castle_has_repr : has_repr castle := ⟨castle.repr⟩

variables {m n : Type}
variables [has_zero m] [has_one m] [has_add m]
variables [has_zero n] [has_one n] [has_add n]

def file.parser' : parser m := numeral.char _ 'a' 'z'
def file.parser [fintype m] : parser m := numeral.char.of_fintype _ 'a'
def rank.parser' : parser m := numeral.from_one m
def rank.parser [fintype m] : parser m := numeral.from_one.of_fintype m
def square.parser' : parser (m × n) :=
(λ x y, ⟨y, x⟩) <$> file.parser' <*> rank.parser'
def square.parser [fintype m] [fintype n] : parser (m × n) :=
(λ x y, ⟨y, x⟩) <$> file.parser <*> rank.parser
def square.parser.optional [fintype m] [fintype n] : parser (option m × option n) :=
(λ x y, ⟨y, x⟩) <$> (file.parser.option) <*> (rank.parser.option)
def capture.parser : parser capture :=
ch 'x' $> capture.capture
def castle.parser : parser castle :=
(str "O-O-O" $> castle.queens) <|> (str "O-O" $> castle.kings)

variables [fintype m] [fintype n] [decidable_eq m] [decidable_eq n] [linear_order m] [linear_order n]

-- in this order because absence of the from-square and capture will parse the to-square as
-- from-square, and fail the parser
def move.not_pawn.parser : parser (move.description.chess m n) :=
try ((λ fig fsq cap tsq, ⟨⟨fig, fsq, tsq⟩, cap, none⟩) <$>
  piece.parser <*> square.parser.optional <*> capture.parser.option <*> square.parser) <|>
  (λ fig cap tsq, ⟨⟨fig, (none, none), tsq⟩, cap, none⟩) <$>
    piece.parser <*> capture.parser.option <*> square.parser

def move.pawn.push.parser : parser (move.description.chess m n) :=
(λ tsq prom, ⟨⟨pawn, (none, none), tsq⟩, none, prom⟩) <$>
  square.parser <*> piece.promotions.parser.option

def move.pawn.capture.parser : parser (move.description.chess m n) :=
(λ f r cap tsq prom, ⟨⟨pawn, (r, f), tsq⟩, cap, prom⟩) <$>
  (some <$> file.parser) <*> rank.parser.option <*> (some <$> capture.parser) <*> square.parser <*>
  piece.promotions.parser.option

-- in this order because the push parser is strictly a prefix of the capture parser
def move.pawn.parser : parser (move.description.chess m n) :=
mfirst try [move.pawn.push.parser, move.pawn.capture.parser]

def move.parser : parser (move.description.chess m n) :=
mfirst try [move.not_pawn.parser, move.pawn.parser]

def notation.parser : parser unit :=
one_of ['!', '?', '+', '#'] $> ()

instance {α : Type*} [has_repr α] : has_repr (parse_result α) := ⟨
  λ pr, @parse_result.cases_on _ (λ _, string) pr
    (λ n a, "done (" ++ repr n ++ "): " ++ repr a)
    (λ n a, "fail (" ++ repr n ++ "): " ++ repr a.to_list)
⟩

def general.parser : parser (castle ⊕ move.description.chess (fin 8) (fin 8)) :=
(sum.inl <$> castle.parser) <|> (sum.inr <$> (move.parser <* notation.parser.option))

#eval
(parse_to_some
  ((parser.nat *> (ch '.') *> (ch ' ')) *> (
    (sep_by1
      (parser.nat *> (ch '.') *> (ch ' ').option $> ())
      (prod.mk <$>
        (general.parser <* (ch ' ').option) <*>
        ((general.parser <* (ch ' ').option).try <|>
          ((parser.nat *> ch '-' <* parser.nat) $> sum.inl castle.kings))))
        -- quick way to parse "1-0" scores
  ))
(
  "1. e4 c6 2. d4 d5 3. Nc3 dxe4 4. Nxe4 Nf6 5. Qd3 e5 6. dxe5
Qa5+ 7. Bd2 Qxe5 8. O-O-O Nxe4 9. Qd8+ Kxd8 10. Bg5+ Kc7
11. Bd8# 1-0".to_list.map (λ c, if c = '\n' then ' ' else c)
).as_string)

#eval
(parse_to_some
  ((parser.nat *> (ch '.') *> (ch ' ')) *> (
    (sep_by1
      (parser.nat *> (ch '.') *> (ch ' ').option $> ())
      (prod.mk <$>
        (general.parser <* (ch ' ').option) <*>
        ((general.parser <* (ch ' ').option).try <|>
          ((parser.nat *> ch '-' <* parser.nat) $> sum.inl castle.kings))))
        -- quick way to parse "1-0" scores
  ))
(
  "1. e4 e5 2. Nf3 Nc6 3. Bb5 Nf6 4. O-O d6 5. d4 Nxe4 6. d5 a6
7. Bd3 Nf6 8. dxc6 e4 9. Re1 d5 10. Be2 exf3 11. cxb7 Bxb7
12. Bb5# 1-0"
  .to_list.map (λ c, if c = '\n' then ' ' else c)
).as_string)

end chess
