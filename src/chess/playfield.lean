import data.matrix.notation

variables {m n : Type}
variables {ι : Type}

/--
A `playfield X Y R` represents a `matrix (X × Y) option R`, which is
a model for a `X × Y` shaped game board where not every square is
occupied.
-/
def playfield (X Y : Type) (R : Type) : Type* := X × Y → option R

section playfield

/-- A conversion function to turn a bare `matrix` into a `playfield`. -/
def matrix_to_playfield {X Y R : Type} [fintype X] [fintype Y]
  (M : matrix X Y (option R)) : playfield X Y R :=
λ ⟨x, y⟩, M x y

notation `PF` M := matrix_to_playfield M

/-- A `playfield` is by default `inhabited` by empty squares everywhere. -/
instance playfield.inhabited : inhabited (playfield m n ι) :=
⟨λ ⟨x, y⟩, none⟩

namespace playfield

section move_piece

variables [decidable_eq m] [decidable_eq n]
variables (M : playfield m n ι)
variables (start_square end_square : m × n)

/--
Move a `piece` from `start_square` to `end_square` on a `playfield`,
swapping the pieces at those squares.

Does not assume anything about occupancy.
-/
def move_piece : playfield m n ι :=
λ pos, M (equiv.swap start_square end_square pos)

/-- Equivalent to to `move_piece`, but useful for `rewrite`ing. -/
lemma move_piece_def : M.move_piece start_square end_square =
    λ pos, M (equiv.swap start_square end_square pos) := rfl

/-- Moving a piece moves `start_square` to `end_square` -/
@[simp] lemma move_piece_start :
M.move_piece start_square end_square start_square = M end_square :=
by simp only [move_piece_def, equiv.swap_apply_left]

/-- Moving a piece moves `end_square` to `start_square` -/
@[simp] lemma move_piece_end :
M.move_piece start_square end_square end_square = M start_square :=
by simp only [move_piece_def, equiv.swap_apply_right]

/-- Moving a piece fixes other squares / pieces. -/
@[simp] lemma move_piece_diff
  {start_square end_square other_square : m × n}
  (ne_start : other_square ≠ start_square)
  (ne_end : other_square ≠ end_square) :
M.move_piece start_square end_square other_square = M other_square :=
by simp only [move_piece_def, equiv.swap_apply_of_ne_of_ne ne_start ne_end]

end move_piece

end playfield

end playfield
