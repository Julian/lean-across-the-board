import chess.utils
import data.matrix.notation

/-!

# Definitions and theorems about the chess board field

## Summary

The field on which chess pieces are placed is a 2D plane, where each
position corresponds to a piece index. This is because we think of
defining pieces and moves, usually, by indicating which position
they are at, and which position they are moved to.

## Main definitions

1. The playfield itself (`playfield`)
2. Conversion from a `matrix` of (possibly) occupied spaces to a `playfield`
3. Moving a piece by switching the indices at two specified positions using `move_piece`
4. Making a sequence of moves at once using `move_sequence`

## Implementation details

1. The `playfield` type itself has no requirements to be finite in any dimension,
or that the indices used are finite. We represent the actual index wrapped by
`option`, such that the empty square can be an `option.none`. The playfield definition
wraps the two types used to define the dimensions of the board into a pair.

2. In the current implementation, the way to construct a `playfield` is to provide
a matrix. This limits the `playfield` to a finite 2D plane. Another possible implementation
is of a "sparse matrix", where for each index, we can look up where the piece is.
This now allows for an infinite playfield, but still complicates using infinite pieces.
For now, the closely-tied `matrix` definition makes `playfield` a light type wrapper
on top of `matrix`, i.e. a function of two variables.

3. Currently, `move_piece` just swaps the (potentially absent) indices at two positions.
This is done by using an `equiv.swap` as an updating function. For now, this means that
moves that use `move_piece` are non-capturing. Additionally, no math or other requirements
on the positions or their contents is required. This means that `move_piece` supports a
move from a position to itself. A separate `move` is defined in `chess.move` that has
more chess-like rule constraints.

4. Index presence on the board is not limited to have each index on at-most-one position.
Preventing duplication of indices is not enforced by the `playfield` itself. However,
any given position can hold at-most-one index on it. The actual chess-like rule constraints
are in `chess.board`.

5. Sequences of moves are implemented on top of `move`s, rather than vice versa (`move`s
being defined as sequences of length one). This *probably* causes a bit of duplication,
which may warrant flipping things later.

-/

-- The height and width of the playfield
variables (m n : Type*)
-- The index type at (possibly) each position
variables (ι : Type*)

/--
A `playfield m n ι` represents a `matrix (m × n) option ι`, which is
a model for a `m × n` shaped game board where not every square is
occupied.
-/
def playfield : Type* := m × n → option ι

section playfield

-- The dimensions and index type of the playfield can be assumed
variables {m n ι}

/--
A conversion function to turn a bare `matrix` into a `playfield`.
A `matrix` requires the dimensions to be finite.

An example empty 3 × 3 playfield for 4 pieces could be generated by:
```
matrix_to_playfield ((
  ![![none, none, none],
    ![none, none, none],
    ![none, none, none]] : matrix (fin 3) (fin 3) (option (fin 4))
```

where the positions are 0-indexed, with the origin in the top-left,
first dimension for the row, and second dimension for the column
(0,0) (0,1) (0,2)
(1,0) (1,1) (1,2)
(2,0) (2,1) (2,2)

-/
def matrix_to_playfield [fintype m] [fintype n]
  (M : matrix m n (option ι)) : playfield m n ι :=
λ ⟨x, y⟩, M x y

-- Provide a short notation to be used for `playfield` construction when
-- using matrix notation
notation `PF` M := matrix_to_playfield M

/--
A `playfield` is by default `inhabited` by empty squares everywhere.
-/
instance playfield.inhabited : inhabited (playfield m n ι) :=
⟨λ ⟨x, y⟩, none⟩

-- Definitions and lemmas in this section will be accessible as `pf.___`
-- for a `pf : playfield m n ι`
namespace playfield

/--
A piece, identified by an index, is on the board, if there is any position
such that the index at that position is the one we're inquiring about.
Providing a `has_mem` instance allows using `ix ∈ pf` for `ix : ι, pf : playfield m n ι`.
This definition does not preclude duplicated indices on the playfield.
See "Implementation details".
-/
instance : has_mem ι (playfield m n ι) :=
⟨λ ix p, ∃ pos, p pos = ix⟩

section repr

-- The size of the "vectors" for a `fin n' → ι`, for `has_repr` definitions
variables {m' n' : ℕ}
-- Require an index to be `repr`esentable to be able to represent a "vector" of it
variable [has_repr ι]

-- A finite `playfield` is just a uncurried `matrix`.
instance playfield_repr_instance :
  has_repr (playfield (fin n') (fin m') ι) := ⟨chess.utils.matrix_repr ∘ function.curry⟩

end repr

-- To be able to state whether two positions are equal
-- we need to be able to make the equality on each of the dimensions `decidable`
variables [decidable_eq m] [decidable_eq n]
-- Fix a `pf : playfield m n ι` to use in definitions and lemmas below
variables (pf : playfield m n ι)

section move_piece

-- Fix `start_square` and `end_square : m × n` to use in definitions and lemmas below
variables (start_square end_square : m × n)

/--
Move an (optional) index from `start_square` to `end_square` on a `playfield`,
swapping the indices at those squares.

Does not assume anything about occupancy.
-/
def move_piece : playfield m n ι :=
λ pos, pf (equiv.swap start_square end_square pos)

/--
Equivalent to to `move_piece`, but useful for `rewrite`\ ing.
-/
lemma move_piece_def : pf.move_piece start_square end_square =
    λ pos, pf (equiv.swap start_square end_square pos) := rfl

/--
Moving an (optional) index that was at `start_square` places it at `end_square`
-/
@[simp] lemma move_piece_start :
pf.move_piece start_square end_square start_square = pf end_square :=
by simp only [move_piece_def, equiv.swap_apply_left]

/--
Moving an (optional) index that was at `end_square` places it at `start_square`
-/
@[simp] lemma move_piece_end :
pf.move_piece start_square end_square end_square = pf start_square :=
by simp only [move_piece_def, equiv.swap_apply_right]

/--
Moving an (optional) index retains whatever (optional) indices that were at other squares.
-/
@[simp] lemma move_piece_diff
  {start_square end_square other_square : m × n}
  (ne_start : other_square ≠ start_square)
  (ne_end : other_square ≠ end_square) :
pf.move_piece start_square end_square other_square = pf other_square :=
by simp only [move_piece_def, equiv.swap_apply_of_ne_of_ne ne_start ne_end]

end move_piece

section move_sequence

-- The length of the sequence
variables {o : ℕ}
-- Fix a sequence of start and end squares.
variables (seq : vector ((m × n) × (m × n)) o)

/-- Make a sequence of `move`s all at once. -/
def move_sequence : fin (o + 1) → playfield m n ι :=
(vector.scanl (λ acc (x : prod _ _), move_piece acc x.fst x.snd) pf seq).nth

/--
Equivalent to to `move_sequence`, but useful for `rewrite`\ ing.
-/
lemma move_sequence_def : pf.move_sequence seq =
  (vector.scanl (λ acc (x : prod _ _), move_piece acc x.fst x.snd) pf seq).nth := rfl

/--
Throughout a sequence, moving an (optional) index that was at
`start_square` places it at `end_square`.
-/
@[simp] lemma move_sequence_start :
∀ (e : fin o), ((pf.move_sequence seq) e) (seq.nth e).fst =
               ((pf.move_sequence seq) e) (seq.nth e).snd := by begin
  sorry,
end

/--
Throughout a sequence, moving an (optional) index retains whatever
(optional) indices that were at other squares.
-/
@[simp] lemma move_sequence_end :
∀ (e : fin o), ((pf.move_sequence seq) e) (seq.nth e).snd =
               ((pf.move_sequence seq) e) (seq.nth e).fst := by begin
  sorry,
end

/--
Throughout a sequence, moving an (optional) index that was at
`start_square` places it at `end_square`.
-/
@[simp] lemma move_sequence_diff
  {start_square end_square other_square : m × n}
  (ne_start : other_square ≠ start_square)
  (ne_end : other_square ≠ end_square) :
∀ (e : fin o), ((pf.move_sequence seq) e) (seq.nth e).fst =
               ((pf.move_sequence seq) e) (seq.nth e).snd := by begin
  sorry,
end

end move_sequence

end playfield

end playfield
