import chess.board

/-!

"Proof" of Guarini's Problem: swapping some knights.

Given a board like:

    ♞ _ ♞
    _ _ _
    ♘ _ ♘

Guarini's problem asks for a sequence of moves that swaps the knights,
producing:

    ♘ _ ♘
    _ _ _
    ♞ _ ♞

-/


def starting_position : chess.board _ _ _ _ := {
  pieces := ![♞, ♞, ♘, ♘],
  contents := ![
    ![(0 : fin 4), __, (1 : fin 4)],
    ![    __,      __,       __   ],
    ![(2 : fin 4), __, (3 : fin 4)]
  ],
  contains_pieces := dec_trivial,
  no_superimposed_pieces := dec_trivial,
}


def ending_position : chess.board _ _ _ _ := {
  pieces := ![♞, ♞, ♘, ♘],
  contents := ![
    ![(2 : fin 4), __, (3 : fin 4)],  -- FIXME(#1): the indices here are
    ![    __,      __,       __   ],  --            misleading since we just
    ![(0 : fin 4), __, (1 : fin 4)]   --            should care about equality
  ],
  contains_pieces := dec_trivial,
  no_superimposed_pieces := dec_trivial,
}
