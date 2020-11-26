import chess.move.legal

/-!
We define local instances for `option (fin n)` for a notational shortcut.
This allows us to write 0, 1, ... for valid `option (fin n)`.
Then, it is easy to use `fin n` as an index type in our boards.
-/

/-- Provide a zero for `option (fin (n + 1))`. -/
def option.fin.zero {n : ℕ} : has_zero (option (fin (n + 1))) := ⟨some 0⟩
local attribute [instance] option.fin.zero

/-- Provide a one for `option (fin (n + 2))`. -/
def option.fin.one {n : ℕ} : has_one (option (fin (n + 2))) := ⟨some 1⟩
local attribute [instance] option.fin.one

/-- Provide addition for `option (fin n)`, which is only on the `some` values,
and shortcircuits on `none`. Given that `0` and `1` are locally defined for
`option (fin (n + 2))`, this gives access to other numerals via `bit0` and `bit1`. -/
def option.fin.add {n : ℕ} : has_add (option (fin n)) := ⟨λ a b, (+) <$> a <*> b⟩
local attribute [instance] option.fin.add

section piece

example : ♞ ≠ ♚ := dec_trivial

end piece

section board

def b₁ : chess.board _ _ _ _ :=
  { chess.board .
    pieces := ![♞],
    contents := PF ![![0 , __], ![__, __], ![__, __]] }

example : b₁.width = 2 := rfl
example : b₁.height = 3 := rfl

example : 0 ∈ b₁.contents := dec_trivial
example : 0 ∈ b₁ := dec_trivial

example : b₁.piece_at (0, 0) = ♞ := rfl

def b₂ {p p' q q' r r' : chess.colored_piece} : chess.board _ _ _ _ :=
  { chess.board .
    pieces := ![p, p', q, q', r, r'],
    contents := PF ![
      ![__, __, 0 , 5 , __, __],
      ![1 , __, 3 , __, __, __],
      ![__, __, __, __, 2 , 4 ]
    ] }

def b₃ {p p' q q' r r' : chess.colored_piece} : chess.board _ _ _ _ :=
  { chess.board .
    pieces := ![p, p', q, q', r, r'],
    contents := PFL [
      [__, __, 0 , 5 , __, __],
      [1 , __, 3 , __, __, __],
      [__, __, __, __, 2 , 4 ]
    ] }

end board

section move

def downright : chess.move b₁ := {start_square := (0, 0), end_square := (2, 1)}

example : downright.piece = ♞ := rfl
example : downright.piece ≠ ♚ := dec_trivial

def cycle : chess.move.sequence _ _ _ _ _ := {
  start_board := b₁,
  elements := ![
    (downright.start_square, downright.end_square),
    (downright.end_square, downright.start_square)
  ]
}

section legal

def centered_knight : chess.board _ _ _ _ :=
  { pieces := ![♘],
    contents := PF ![
      ![__, __, __, __, __],
      ![__, __,  0, __, __],
      ![__, __, __, __, __] ] }

example : chess.move.legal centered_knight := { start_square := (1, 2), end_square := (0, 0) }
example : chess.move.legal centered_knight := { start_square := (1, 2), end_square := (2, 0) }
example : chess.move.legal centered_knight := { start_square := (1, 2), end_square := (0, 4) }
example : chess.move.legal centered_knight := { start_square := (1, 2), end_square := (2, 4) }

def illegal : chess.move centered_knight := { start_square := (1, 2), end_square := (1, 3) }

example : ¬ illegal.is_legal := dec_trivial

def centered_king : chess.board _ _ _ _ :=
  { pieces := ![♔],
    contents := PF ![
      ![__, __, __, __, __],
      ![__, __,  0, __, __],
      ![__, __, __, __, __] ] }

end legal

end move
