import chess.move


def b₁ : chess.board _ _ _ _ :=
  { chess.board .
    pieces := ![♞],
    contents := PF ![![(0 : fin 1), __], ![__, __], ![__, __]] }

example : chess.board.width b₁ = 2 := rfl
example : chess.board.height b₁ = 3 := rfl

example (p p' q q' r r' : chess.colored_pieces) : chess.board _ _ _ _ :=
  { chess.board .
    pieces := ![p, p', q, q', r, r'],
    contents := PF ![
      ![__, __, (0 : fin 6), (5 : fin 6), __, __],
      ![(1 : fin 6), __, (3 : fin 6), __, __, __],
      ![__, __, __, __, (2 : fin 6), (4 : fin 6)]
    ],
    contains_pieces := dec_trivial,
    no_superimposed_pieces := dec_trivial, }


def downright : chess.move b₁ := {start_square := (0, 0), end_square := (2, 1)}
