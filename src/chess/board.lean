import data.matrix.notation
import tactic.dec_trivial

import chess.playfield
import chess.piece


/-!

Straightforward implementation of a chess board.

-/

namespace chess

variables (m n : Type*) [fintype n] [decidable_eq n] [fintype m] [decidable_eq m]
variables (ι : Type*) [fintype ι] [decidable_eq ι]

variables (K : Type*)

section wrap

variables [has_repr K]

structure option_wrapper :=
(val : option K)
(none_s : string)

instance wrapped_option_repr : has_repr (option_wrapper K) :=
⟨λ ⟨val, s⟩, (option.map has_repr.repr val).get_or_else s⟩

variables {K}
def option_wrap (val : option K) (none_s : string) : option_wrapper K := ⟨val, none_s⟩

end wrap


/--
A board is axiomatized as a set of indexable (ergo distinguishable) pieces
which are placed on distinct squares of a `playfield`.
-/
structure board :=
(pieces : ι → K)
(contents : playfield m n ι)
(contains_pieces :
  ∀ ix : ι, ix ∈ contents . tactic.exact_dec_trivial)
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

/-- The state of the board, where pieces of the same type are equivalent -/
def reduce (b : board m n ι K) : playfield m n K :=
λ pos, option.map b.pieces (b.contents pos)

instance : has_mem ι (board m n ι K) :=
⟨λ ix b, ix ∈ b.contents⟩

section repr

variables [has_repr K]
variables {n' m' ix : ℕ}

def board_repr_pieces (b : board (fin m') (fin n') (fin ix) K) : string :=
playfield.vec_repr b.pieces ++ ";\n\n"

def board_repr_contents (b : board (fin m') (fin n') (fin ix) K) : string :=
playfield.matrix_repr (λ x y, option_wrap (option.map b.pieces (b.contents ⟨x, y⟩)) "\uFF3F")

def board_repr {K : Type*} [has_repr K] {n m ix : ℕ}
  (b : board (fin m) (fin n) (fin ix) K) : string :=
b.board_repr_pieces ++ b.board_repr_contents

instance board_repr_instance : has_repr (board (fin m') (fin n') (fin ix) K) := ⟨board_repr⟩

end repr

end board

end chess
