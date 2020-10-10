import data.equiv.basic
import tactic.dec_trivial

import chess.board


namespace chess

variables {m n : Type}

lemma split_eq (x : m × n) (p p' : m × n) :
  x = p ∨ x = p' ∨ (x ≠ p ∧ x ≠ p') := by tauto

variables [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]
variables {ι : Type} [fintype ι] [decidable_eq ι]

variables {K : Type}

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
(occupied_start : b.contents start_square ≠ __ . tactic.exact_dec_trivial)
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

lemma start_square_is_some :
  (b.contents f.start_square).is_some :=
by simp only [option.ne_none_iff_is_some.mp f.occupied_start, before_occupied_start]

/-- The piece that is being moved. -/
def piece : K :=
(b.pieces (option.get f.start_square_is_some))

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

variables (f)

/-- A valid `move` on a `board` retains a valid board state. -/
def perform_move : board m n ι K :=
{ pieces := b.pieces,
  contents := b.contents.move_piece f.start_square f.end_square,
  contains_pieces := f.retains_pieces,
  no_superimposed_pieces := f.no_superimpose }

variables (m n ι K)
-- The length of the sequence
variables (o : ℕ)

/--
A move `sequence` represents a sequential set of moves from a starting `board`.
-/
structure sequence :=
(start_board : board m n ι K)
(elements : fin o → (m × n) × (m × n))
(atrivial_moves : ∀ (e : fin o), (elements e).fst ≠ (elements e).snd . tactic.exact_dec_trivial)

namespace sequence

variables {m n ι K o}
variables (s : sequence m n ι K o)

def scan_contents : fin (o + 1) → playfield m n ι :=
((vector.of_fn s.elements).scanl (λ acc (x : prod _ _), playfield.move_piece acc x.fst x.snd)
   s.start_board.contents).nth

/-- Pieces do not disappear after any `move` in a `sequence`. -/
lemma retains_pieces (ixₒ : fin (o + 1)) : ∀ (ixᵢ : ι), ixᵢ ∈ (s.scan_contents ixₒ) :=
begin
  intro ix,
  apply vector.scanl.induction_on,
  { exact s.start_board.contains_pieces ix },
  {
    intros pf squares h_pf,
    obtain ⟨pos, h⟩ := h_pf,
    by_cases hs : pos = squares.fst;
    by_cases he : pos = squares.snd,
    { use pos, simp [←hs, ←he, ←h] },
    { use squares.snd, simp [hs, he, ←h] },
    { use squares.fst, simp [hs, he, ←h] },
    { use pos, simp [hs, he, ←h] }
  }
end

/-- Pieces do not become superimposed after any `move` in a `sequence`. -/
lemma no_superimpose
    (ixₒ : fin (o + 1))
    (pos pos')
    (hne : pos ≠ pos')
    (h : (s.scan_contents ixₒ) pos ≠ __)
    (h' : (s.scan_contents ixₒ) pos' ≠ __) :
      (s.scan_contents ixₒ) pos ≠ (s.scan_contents ixₒ) pos' :=
begin
  sorry,
end

/-- The board which results from applying the first `ix₀ + 1` `move`s in the `sequence`. -/
def boards (ixₒ : fin (o + 1)) : board m n ι K :=
{ contents := s.scan_contents ixₒ,
  pieces := s.start_board.pieces,
  contains_pieces := s.retains_pieces ixₒ,
  no_superimposed_pieces := s.no_superimpose ixₒ }

/-- The board which results from applying all `move`s in the `sequence`. -/
def end_board : board m n ι K := s.boards (fin.last o)

variables {b s}

/-- The `ix₀ + 1`'st `move` in the `sequence`. -/
def moves (ixₒ: fin o) : chess.move b :=
{ start_square := (s.elements ixₒ).fst,
  end_square := (s.elements ixₒ).snd,
  diff_squares := s.atrivial_moves ixₒ,
  occupied_start := sorry,
  unoccupied_end := sorry }

/--
Any square which is not the `start_square` or `end_square` of any `move`
in the `sequence` is fixed across all `move`s (i.e. contains the same piece or remains empty).
-/
lemma fixes_unmentioned_squares
  (ixᵢ : ι)
  {pos}
  {h_pos: s.start_board.contents pos = ixᵢ}
  (h_unmentioned : ∀ ixₒ, pos ≠ (s.elements ixₒ).fst ∧ pos ≠ (s.elements ixₒ).snd) :
    ∀ ixₒ, (s.boards ixₒ).contents pos = ixᵢ :=
begin
  dsimp [boards, scan_contents],
  intro ix,
  apply fin.induction_on ix,
  { simpa only [vector.nth_zero, vector.scanl_head] using h_pos },
  { intros ix' h,
    simpa only [vector.scanl_nth, h_unmentioned, playfield.move_piece_diff,
                vector.nth_of_fn, ne.def, not_false_iff] using h },
end

end sequence
end move

namespace board

variable (b)

/--
Assert the existence of a `sequence` of length `o` from a `start_board` to a given end board.
-/
def has_sequence_len (end_board: board m n ι K) (o : ℕ) :=
    ∃ (s : chess.move.sequence m n ι K o), b ≈ s.start_board ∧ end_board ≈ s.end_board

/-- Assert the existence of a `sequence` from a `start_board` to a given end board. -/
def has_sequence_to (end_board: board m n ι K) :=
    ∃ (o : ℕ), b.has_sequence_len end_board o

end board

end chess
