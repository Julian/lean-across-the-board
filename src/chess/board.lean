import data.matrix.notation
import tactic.dec_trivial

import chess.playfield
import chess.piece
import chess.utils


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

3. `board.piece_at`, which extracts the piece which sits on a given square.

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

/--
A board is axiomatized as a set of indexable (ergo distinguishable) pieces
which are placed on distinct squares of a `playfield`.

No inhabited instance because the index type can be larger than the
cardinality of the playfield dimensions.
-/
@[nolint has_inhabited_instance]
structure board :=
-- The pieces the board holds, provided as an indexed vector
(pieces : ι → K)
-- The playfield on which the pieces are placed
(contents : playfield m n ι)
-- All the pieces in `pieces` are on the `contents`
-- See "Implementation details" for info about `dec_trivial`
(contains : function.surjective contents.index_at . tactic.exact_dec_trivial)
-- Different positions hold different indices
(injects : contents.some_injective . tactic.exact_dec_trivial)

namespace board

variables {m n ι K}
/-- The width of the board. Explicit argument for projection notation. -/
@[nolint unused_arguments]
def width (b : board m n ι K) : ℕ := fintype.card n
/-- The height of the board. Explicit argument for projection notation. -/
@[nolint unused_arguments]
def height (b : board m n ι K) : ℕ := fintype.card m

/-- The state of the board, where pieces of the same type are equivalent -/
def reduce (b : board m n ι K) : playfield m n K :=
λ pos, option.map b.pieces (b.contents pos)

-- Allows saying that `b b' : board m n ι K` are `b ≈ b'`.
instance : has_equiv (board m n ι K) := ⟨λ b b', reduce b = reduce b'⟩

-- An indexed piece is on the board if it is in the board's `playfield`.
instance : has_mem ι (board m n ι K) :=
⟨λ ix b, ix ∈ b.contents⟩

/--
Explicitly state that the proposition that an index `ix : ι` is in the board
is `decidable`, when the `ι` is itself `decidable_eq`.
-/
instance contents_decidable {b : board m n ι K} {ix : ι} : decidable (ix ∈ b) :=
set.decidable_mem ((∈) ix) b

/--
A board contains all of the `ix : ι` indices that it knows of,
stated explicitly. Uses the `board.contains` constraint.
-/
lemma retains_pieces (b : board m n ι K) (ix : ι) : ix ∈ b.contents :=
exists.elim (b.contains ix) (λ pos h, h ▸ playfield.index_at_in pos)

/--
A board maps each index `ix : ι` to a unique position `pos : m × n`,
stated explicitly. Uses the `board.injects` constraint.
-/
lemma no_superimposed (b : board m n ι K) (pos pos' : m × n) (hne : pos ≠ pos')
  (h : b.contents.occupied_at pos) : b.contents pos ≠ b.contents pos' :=
λ H, hne (b.injects h H)

/--
Given that the board is `occupied_at` some `pos : m × n`,
then the index at some `pos' : m × n` is equal to the index at `pos`,
iff that `pos'` is equal `pos' = pos`.
-/
protected lemma inj_iff (b : board m n ι K) :
  ∀ {pos pos' : m × n}, b.contents.occupied_at pos → (b.contents pos = b.contents pos' ↔ pos = pos') :=
λ _ _ H, playfield.inj_iff b.contents b.injects H

section repr

-- A board can be represented if the pieces themselves can be represented
variables [has_repr K]
variables {n' m' ix : ℕ}

/--
A board's `pieces` is a "vector", so `vec_repr` is used to represent it.
-/
def board_repr_pieces (b : board (fin m') (fin n') (fin ix) K) : string :=
chess.utils.vec_repr b.pieces

/--
A board's `contents` can be represented by reducing the board according to
the indexed vector at `pieces`, and placing the pieces on the `playfield`.
We override the default `option K` representation by using `option_wrap`,
and supply an underscore to represent empty positions.
-/
def board_repr_contents (b : board (fin m') (fin n') (fin ix) K) : string :=
chess.utils.matrix_repr (λ x y, chess.utils.option_wrap (b.reduce ⟨x, y⟩) "\uFF3F")

/--
A board's representation is just the concatentation of the representations
of the `pieces` and `contents` via `board_repr_pieces` and `board_repr_contents`,
respectively, with newlines inserted for clarity.
-/
def board_repr {K : Type*} [has_repr K] {n m ix : ℕ}
  (b : board (fin m) (fin n) (fin ix) K) : string :=
b.board_repr_pieces ++ ";\n\n" ++ b.board_repr_contents

/-- A board's representation is provided by `board_repr`. -/
instance board_repr_instance : has_repr (board (fin m') (fin n') (fin ix) K) := ⟨board_repr⟩

end repr

/-- The (colored) `piece` on a given square. -/
def piece_at
  (b : board m n ι K)
  (pos : m × n)
  (h : b.contents.occupied_at pos . tactic.exact_dec_trivial) : K :=
b.pieces (b.contents.index_at ⟨pos, h⟩)

end board

end chess
