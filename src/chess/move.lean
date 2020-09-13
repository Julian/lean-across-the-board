import tactic.dec_trivial

import chess.board


namespace chess

variables (m n : Type) [fintype n] [decidable_eq n] [fintype m] [decidable_eq m]
variables (ι : Type) [fintype ι] [decidable_eq ι]

variables (K : Type*)

variables {m n ι K}

/-- A move is an initial chess board along with the start and end squares
    containing the piece which is moved. -/
structure move :=
(board: board m n ι K)
(start_square : m × n)
(end_square : m × n)
(occupied_start:
    (board.contents start_square.1 start_square.2).is_some
    . tactic.exact_dec_trivial)

end chess
