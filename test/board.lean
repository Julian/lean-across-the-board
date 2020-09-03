import chess.board


example : chess.board _ _ _ _ :=
  { chess.board .
    pieces := ![♞],
    contents := ![![(0 : fin 1)], ![__], ![__]],
    contains_pieces := dec_trivial,
    no_superimposed_pieces := dec_trivial, }

example (p p' q q' r r' : chess.colored_pieces ) : chess.board _ _ _ _ :=
  { chess.board .
    pieces := ![p, p', q, q', r, r'],
    contents := ![
      ![__, __, (0 : fin 6), (5 : fin 6), __, __],
      ![(1 : fin 6), __, (3 : fin 6), __, __, __],
      ![__, __, __, __, (2 : fin 6), (4 : fin 6)]
    ],
    contains_pieces := dec_trivial,
    no_superimposed_pieces := dec_trivial, }
