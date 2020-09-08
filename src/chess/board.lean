import data.matrix.notation
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
(contents : matrix m n (option ι))
(contains_pieces : ∀ ix : ι, ∃ x : m, ∃ y : n, contents x y = ix)
(no_superimposed_pieces :
  ∀ (x x' : m),
  ∀ (y y' : n),
    x ≠ x' → y ≠ y' →
    (contents x y).is_some →
    (contents x' y').is_some →
      contents x y ≠ contents x' y')

namespace board

variables {m n ι K}
def width (b : board m n ι K) : ℕ := fintype.card n
def height (b : board m n ι K) : ℕ := fintype.card m

end board

end chess
