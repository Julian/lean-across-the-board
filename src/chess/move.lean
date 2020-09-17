import data.equiv.basic
import tactic.dec_trivial

import chess.board


namespace chess

variables {m n : Type}

lemma split_eq (x : m × n) (p p' : m × n) :
  x = p ∨ x = p' ∨ (x ≠ p ∧ x ≠ p') := by tauto

variables [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]
variables {ι : Type} [fintype ι] [decidable_eq ι]

variables {K : Type*}

variables (b : board m n ι K)

/--
A move is a (distinct) start and end square whose start square is
occupied and whose end square is not.

(Captures are not implemented yet.)
-/
structure move :=
(start_square : m × n)
(end_square : m × n)
(diff_squares : start_square ≠ end_square . tactic.exact_dec_trivial)
(occupied_start :
    b.contents start_square ≠ __
    . tactic.exact_dec_trivial)
(unoccupied_end : b.contents end_square = __ . tactic.exact_dec_trivial)

variable {b}
variable (f : move b)

namespace move

/-- Start squares are occupied before a move. -/
@[simp] lemma before_occupied_start :
    b.contents f.start_square ≠ __ := f.occupied_start

/-- End squares are unoccupied before a move. -/
@[simp] lemma before_unoccupied_end :
    b.contents f.end_square = __ := f.unoccupied_end

/-- Start squares are unoccupied after a move. -/
@[simp] lemma after_unoccupied_start :
    b.contents.move_piece f.start_square f.end_square f.start_square = __ :=
by simp only [playfield.move_piece_start, before_unoccupied_end]

/-- End squares are occupied after a move. -/
@[simp] lemma after_occupied_end :
    b.contents.move_piece f.start_square f.end_square f.end_square ≠ __ :=
by simp only [playfield.move_piece_end, ne.def, not_false_iff, before_occupied_start]

/-- Other squares are unchanged after a move. -/
@[simp] lemma before_after_same (pos : m × n)
    (h : pos ≠ f.start_square) (h' : pos ≠ f.end_square) :
    b.contents.move_piece f.start_square f.end_square pos = b.contents pos :=
b.contents.move_piece_diff h h'

/-- Pieces do not disappear after a move. -/
lemma retains_pieces (ix : ι) :
    ix ∈ b.contents.move_piece f.start_square f.end_square :=
begin
  obtain ⟨pos, h⟩ := b.contains_pieces ix,
  by_cases hs : pos = f.start_square;
  by_cases he : pos = f.end_square,
  { have H := f.diff_squares,
    rw [←hs, ←he] at H,
    contradiction },
  { use f.end_square,
    simp [hs, he, ←h] },
  { use f.start_square,
    simp [hs, he, ←h] },
  { use pos,
    simp [hs, he, ←h] }
end

/-- Pieces do not become superimposed after a move. -/
lemma no_superimpose (pos pos') (hne : pos ≠ pos')
    (h : b.contents.move_piece f.start_square f.end_square pos ≠ __)
    (h' : b.contents.move_piece f.start_square f.end_square pos' ≠ __) :
    b.contents.move_piece f.start_square f.end_square pos ≠
      b.contents.move_piece f.start_square f.end_square pos' :=
begin
  rcases split_eq pos f.end_square f.start_square with rfl|rfl|⟨hE, hS⟩;
  rcases split_eq pos' f.end_square f.start_square with rfl|rfl|⟨hE', hS'⟩,
  { contradiction }, { exfalso, simpa only [move.after_unoccupied_start] using h' },
  { have occ' : b.contents pos' ≠ __,
    { intro H, apply h',
      simpa only [hS', hE', playfield.move_piece_diff, ne.def, not_false_iff] using H },
    have H' := b.no_superimposed_pieces pos' f.start_square hS' occ' f.before_occupied_start,
    simpa only [hS', hE', move.before_after_same, playfield.move_piece_end,
      ne.def, not_false_iff] using H'.symm },
  { exfalso, simpa only [move.after_unoccupied_start] using h },
  { contradiction },
  { exfalso, simpa only [move.after_unoccupied_start] using h },
  { have occ : b.contents pos ≠ __,
      { intro H, apply h,
        simpa only [hS, hE, playfield.move_piece_diff, ne.def, not_false_iff] using H },
    have H := b.no_superimposed_pieces pos f.start_square hS occ f.before_occupied_start,
    simpa only [hS, hE, move.before_after_same, playfield.move_piece_end,
      ne.def, not_false_iff] using H.symm },
  { exfalso, simpa only [move.after_unoccupied_start] using h' },
  { have occ : b.contents pos ≠ __,
      { intro H, apply h,
        simpa only [hS, hE, playfield.move_piece_diff, ne.def, not_false_iff] using H },
    have occ' : b.contents pos' ≠ __,
      { intro H, apply h',
        simpa only [hS', hE', playfield.move_piece_diff, ne.def, not_false_iff] using H },
    have H := b.no_superimposed_pieces pos pos' hne occ occ',
    simpa only [hS, hE, hS', hE', move.before_after_same, ne.def, not_false_iff] using H }
end

end move

variables (b) (f)

/-- A valid `move` on a `board` retains a valid board state. -/
def perform_move : board m n ι K :=
{ pieces := b.pieces,
  contents := b.contents.move_piece f.start_square f.end_square,
  contains_pieces := f.retains_pieces,
  no_superimposed_pieces := f.no_superimpose }

end chess
