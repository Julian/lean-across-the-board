import data.matrix.notation

variables {m n : Type}
variables {ι : Type}

/-- A `playfield X Y R` represents a `matrix (X × Y) option R`,
which is a model for a `X × Y` shaped game board where not every square is occupied. -/
def playfield (X Y : Type) (R : Type) : Type* := X × Y → option R

section playfield

/-- A conversion function to turn a bare `matrix` into a `playfield`. -/
def matrix_to_playfield {X Y R : Type} [fintype X] [fintype Y]
  (M : matrix X Y (option R)) : playfield X Y R :=
λ ⟨x, y⟩, M x y

notation `PF` M := matrix_to_playfield M

variables (M : playfield m n ι)

/-- A `playfield` is by default `inhabited` by empty squares everywhere. -/
instance playfield.inhabited : inhabited (playfield m n ι) := ⟨λ ⟨x, y⟩, none⟩

namespace playfield

section move_piece

variables [decidable_eq n] [decidable_eq m]
variables (start_square end_square : m × n)

/-- Move piece from `start_square` to `end_square` on a `playfield`,
swapping the pieces at those squares. Does not assume anything about occupancy. -/
def move_piece : playfield m n ι :=
λ pos, M (equiv.swap start_square end_square pos)

lemma move_piece_def :
  M.move_piece start_square end_square = λ pos, M (equiv.swap start_square end_square pos) := rfl

@[simp] lemma move_piece_diff
  {start_square end_square chosen : m × n}
  (hnes : chosen ≠ start_square) (hnee : chosen ≠ end_square) :
M.move_piece start_square end_square chosen = M chosen :=
by simp only [move_piece_def, equiv.swap_apply_of_ne_of_ne hnes hnee]

@[simp] lemma move_piece_start
  (start_square : m × n) (end_square : m × n)  :
M.move_piece start_square end_square start_square = M end_square :=
by simp only [move_piece_def, equiv.swap_apply_left]

@[simp] lemma move_piece_end
  (start_square : m × n) (end_square : m × n) :
M.move_piece start_square end_square end_square = M start_square :=
by simp only [move_piece_def, equiv.swap_apply_right]

end move_piece

end playfield

end playfield
