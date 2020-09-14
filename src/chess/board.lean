import data.matrix.notation
import tactic.dec_trivial

import chess.playfield
import chess.piece


/-!

Straightforward implementation of a chess board.

-/

namespace chess

variables (m n : Type) [fintype n] [decidable_eq n] [fintype m] [decidable_eq m]
variables (ι : Type) [fintype ι] [decidable_eq ι]

variables (K : Type*)

/--
A board is axiomatized as a set of indexable (ergo distinguishable) pieces
which are placed on distinct squares.
-/
structure board :=
(pieces : ι → K)
(contents : playfield m n ι)
(contains_pieces :
  ∀ ix : ι, ∃ pos : m × n, contents pos = ix . tactic.exact_dec_trivial)
(no_superimposed_pieces :
  ∀ (pos pos' : m × n),
    pos ≠ pos' →
    contents pos ≠ __ →
    contents pos' ≠ __ →
      contents pos ≠ contents pos' . tactic.exact_dec_trivial)

namespace board

variables {m n ι K}
/-- The width of the board. -/
def width (b : board m n ι K) : ℕ := fintype.card n
/-- The height of the board. -/
def height (b : board m n ι K) : ℕ := fintype.card m

end board

end chess
