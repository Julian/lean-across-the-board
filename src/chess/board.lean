import data.matrix.notation
import tactic.dec_trivial

import chess.playfield
import chess.piece


/-!

# Definitions and theorems about a chess board

## Summary

The chess board is a set of indexed `piece`s on a `playfield`. A board is valid,
and can only be constructed, if all the pieces are present on the board, and no two
distinct (by index) pieces share the same position on the board.

## Main definitions

1. The `board` itself, which requires an indexed vector of `piece`s,
and the `playfield` which will serve as the where those pieces are placed.
Additionally, all pieces must be present on the playfield, and no two distinct (by index)
pieces can share a position on the playfield.

2. A way to reduce the board, following the indices to just the pieces. This allows
comparison of boards that are equivalent modulo permutation of indices that point to
equivalent pieces.

## Implementation notes

1. A `board` requires finite dimensions for the `playfield`, finite indices, and a
finite piece set. Ideally, this should be generizable to potentially infinite types.
However, since `playfield`s are usually provided by `matrix`, which is restricted
to finite dimensions, it is easiest to define the board as finite. Additionally,
to perform position math, more constraints on the dimension types will likely be
necessary, like `decidable_linear_order`.

2. The requirement of `decidable_eq` on the dimensions and index allows use of
`dec_trivial` to automatically infer proofs for board constraint propositions.
That means instantiation of a `board` will not require explicit proofs for the propositions.

3. The board does not define what are valid position comparisons -- the geometry of
the space is not defined other than what the `playfield` provides.

4. Currently, all pieces are constrained by the definition of a board to be present
on the playfield. That means no capturing moves and no piece introduction moves are possible.

-/

namespace chess

-- The dimensions of the board, finite and decidably equal
variables (m n : Type*) [fintype n] [decidable_eq n] [fintype m] [decidable_eq m]
-- The index associated to pieces on a playfield
variables (ι : Type*) [fintype ι] [decidable_eq ι]
-- The piece type
variables (K : Type*)

section wrap
-- TODO: Move this section and definitions out of this file
variables [has_repr K]

/--
An auxiliary wrapper for `option K` that allows for overriding the `has_repr` instance
for `option`, and rather, output just the value in the `some` and a custom provided
`string` for `none`.
-/
structure option_wrapper :=
(val : option K)
(none_s : string)

instance wrapped_option_repr : has_repr (option_wrapper K) :=
⟨λ ⟨val, s⟩, (option.map has_repr.repr val).get_or_else s⟩

variables {K}
/--
Construct an `option_wrapper` term from a provided `option K` and the `string`
that will override the `has_repr.repr` for `none`.
-/
def option_wrap (val : option K) (none_s : string) : option_wrapper K := ⟨val, none_s⟩

end wrap


/--
A board is axiomatized as a set of indexable (ergo distinguishable) pieces
which are placed on distinct squares of a `playfield`.
-/
structure board :=
-- The pieces the board holds, provided as an indexed vector
(pieces : ι → K)
-- The playfield on which the pieces are placed
(contents : playfield m n ι)
-- All the pieces in `pieces` are on the `contents`
-- See "Implementation details" for info about `dec_trivial`
(contains_pieces :
  ∀ ix : ι, ix ∈ contents . tactic.exact_dec_trivial)
-- Different positions hold different indices
-- TODO: Rename, since indices can't share a position when defined via a `matrix`
-- TODO: Express as a surjectivity constraint when combined with `contains_pieces`
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

-- Allows saying that `b b' : board m n ι K` are `b ≈ b'`.
instance : has_equiv (board m n ι K) := ⟨λ b b', reduce b = reduce b'⟩

-- An indexed piece is on the board if it is in the board's `playfield`.
instance : has_mem ι (board m n ι K) :=
⟨λ ix b, ix ∈ b.contents⟩

section repr

variables [has_repr K]
variables {n' m' ix : ℕ}

/--
A board's `pieces` is a "vector", so `vec_repr` is used to represent it.
-/
def board_repr_pieces (b : board (fin m') (fin n') (fin ix) K) : string :=
playfield.vec_repr b.pieces

/--
A board's `contents` can be represented by reducing the board according to
the indexed vector at `pieces`, and placing the pieces on the `playfield`.
We override the default `option K` representation by using `option_wrap`,
and supply an underscore to represent empty positions.
-/
def board_repr_contents (b : board (fin m') (fin n') (fin ix) K) : string :=
playfield.matrix_repr (λ x y, option_wrap (b.reduce ⟨x, y⟩) "\uFF3F")

/--
A board's representation is just the concatentation of the representations
of the `pieces` and `contents` via `board_repr_pieces` and `board_repr_contents`,
respectively, with newlines inserted for clarity.
-/
def board_repr {K : Type*} [has_repr K] {n m ix : ℕ}
  (b : board (fin m) (fin n) (fin ix) K) : string :=
b.board_repr_pieces ++ ";\n\n" ++ b.board_repr_contents

instance board_repr_instance : has_repr (board (fin m') (fin n') (fin ix) K) := ⟨board_repr⟩

end repr

end board

end chess
