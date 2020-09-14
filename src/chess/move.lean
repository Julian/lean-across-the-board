import tactic.dec_trivial
import data.equiv.basic

import chess.board


namespace chess

variables {m n : Type}

lemma split_eq (x : m × n) (p p' : m × n) :
  x = p ∨ x = p' ∨ (x ≠ p ∧ x ≠ p') :=
begin
  by_cases H : x = p,
  { exact or.inl H },
  by_cases H' : x = p',
  { exact or.inr (or.inl H') },
  { exact or.inr (or.inr ⟨H, H'⟩) },
end

variables [fintype n] [fintype m] [decidable_eq n] [decidable_eq m]
variables {ι : Type} [fintype ι] [decidable_eq ι]

variables {K : Type*}

variables (b : board m n ι K)

/-- A move is an initial chess board along with the start and end squares
    containing the piece which is moved. -/
structure move :=
(start_square : m × n)
(end_square : m × n)
(diff_squares : end_square ≠ start_square)
(occupied_start :
    b.contents start_square ≠ __
    . tactic.exact_dec_trivial)
(unoccupied_end : b.contents end_square = __)

variable {b}
variable (f : move b)

namespace move

@[simp] lemma before_occupied_start :
    b.contents f.start_square ≠ __ := f.occupied_start

@[simp] lemma before_unoccupied_end :
    b.contents f.end_square = __ := f.unoccupied_end

@[simp] lemma after_unoccupied_start :
    b.contents.move_piece f.start_square f.end_square f.start_square = __ :=
by simp only [playfield.move_piece_start, before_unoccupied_end]

@[simp] lemma after_occupied_end :
    b.contents.move_piece f.start_square f.end_square f.end_square ≠ __ :=
by simp only [playfield.move_piece_end, ne.def, not_false_iff, before_occupied_start]

@[simp] lemma before_after_same (pos : m × n)
    (h : pos ≠ f.start_square) (h' : pos ≠ f.end_square) :
    b.contents.move_piece f.start_square f.end_square pos = b.contents pos :=
b.contents.move_piece_diff h h'

lemma retains_pieces (ix : ι) :
    ∃ pos, b.contents.move_piece f.start_square f.end_square pos = ix :=
begin
  obtain ⟨pos, h⟩ := b.contains_pieces ix,
  by_cases hs : pos = f.start_square;
  by_cases he : pos = f.end_square,
  { have H := f.diff_squares,
    rw [←hs, ←he] at H,
    exact absurd (eq.refl pos) H },
  { use f.end_square,
    simp [hs, he, ←h] },
  { use f.start_square,
    simp [hs, he, ←h] },
  { use pos,
    simp [hs, he, ←h] }
end


lemma no_superimpose (pos pos') (hne : pos ≠ pos')
    (h : b.contents.move_piece f.start_square f.end_square pos ≠ __)
    (h' : b.contents.move_piece f.start_square f.end_square pos' ≠ __) :
    b.contents.move_piece f.start_square f.end_square pos ≠
      b.contents.move_piece f.start_square f.end_square pos' :=
begin
  rcases split_eq pos f.end_square f.start_square with rfl|rfl|⟨hE, hS⟩;
  rcases split_eq pos' f.end_square f.start_square with rfl|rfl|⟨hE', hS'⟩,
  { contradiction },
  { exfalso, simpa only [move.after_unoccupied_start] using h' },
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
