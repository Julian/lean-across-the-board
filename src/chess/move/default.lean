import data.equiv.basic
import tactic.dec_trivial

import chess.board


/-!

# Definitions and theorems about chess board movements

## Summary

A `move` on a particular `board` is a pair of squares whose start square
contains a `piece` and whose end square does not.

Moves may be combined into `sequence`s of moves, which encapsulate
multiple sequential moves all iteratively satisfying the above
condition.

## Main definitions

1. The `move` itself, which requires specifying the particular `board`
it will occur on

2. `perform_move`, which yields the `board` whose playfield has the
start and end squares of a `move` suitably modified

3. A move `sequence`, rooted on a starting board, containing a sequence
of start and end squares which can be treated as iterated moves.

## Implementation notes

1. `move` and `sequence` are implemented independently of each other.
`sequence.moves` can be used to extract a `move` from a particular
index into a `sequence`. `sequence`s are also currently finite, and
therefore also may automatically infer proofs of move conditions via
`dec_trivial`.

2. Currently, no legality checks or piece math whatsoever is performed,
meaning `move`s are not yet programmatically confirmed to be
legal. Captures are similarly not yet supported.

-/


namespace chess

variables {m n : Type}

variables [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]
variables {ι : Type} [fintype ι] [decidable_eq ι]

variables {K : Type}

variables (b : board m n ι K)

/--
A move is a (distinct) start and end square whose start square is
occupied and whose end square is not.

No inhabited instance because the board might be
made up of a single occupied position.

(Captures are not implemented yet.)
-/
@[nolint has_inhabited_instance]
structure move :=
(start_square : m × n)
(end_square : m × n)
(occupied_start : b.contents.occupied_at start_square . tactic.exact_dec_trivial)
(unoccupied_end : ¬ b.contents.occupied_at end_square . tactic.exact_dec_trivial)

variable {b}
variable (f : move b)

namespace move

/-- Start squares are occupied before a move. -/
@[simp] lemma before_occupied_start :
    b.contents.occupied_at f.start_square := f.occupied_start

/-- End squares are unoccupied before a move. -/
@[simp] lemma before_unoccupied_end :
    ¬ b.contents.occupied_at f.end_square := f.unoccupied_end

/-- Start squares are unoccupied after a move. -/
@[simp] lemma after_unoccupied_start :
    ¬ (b.contents.move_piece f.start_square f.end_square).occupied_at f.start_square :=
by simp only [playfield.move_piece_occupied_start, before_unoccupied_end, not_false_iff]

/-- End squares are occupied after a move. -/
@[simp] lemma after_occupied_end :
    (b.contents.move_piece f.start_square f.end_square).occupied_at f.end_square :=
by simp only [before_occupied_start, playfield.move_piece_occupied_end]

/-- Other squares are unchanged after a move. -/
@[simp] lemma before_after_same {pos : m × n}
    (h : pos ≠ f.start_square) (h' : pos ≠ f.end_square) :
    b.contents.move_piece f.start_square f.end_square pos = b.contents pos :=
b.contents.move_piece_diff h h'

/-- Other occupation are unchanged after a move. -/
@[simp] lemma before_after_same_occupied {pos : m × n}
    (h : pos ≠ f.start_square) (h' : pos ≠ f.end_square) :
    (b.contents.move_piece f.start_square f.end_square).occupied_at pos =
      b.contents.occupied_at pos :=
by simp only [h, h', ne.def, playfield.move_piece_occupied_diff, not_false_iff]

/-- The start and end squares of a move are distinct. -/
lemma diff_squares : f.start_square ≠ f.end_square :=
λ H, f.unoccupied_end (H ▸ f.occupied_start)

/-- The piece that is being moved. -/
def piece : K :=
(b.pieces (b.contents.index_at ⟨f.start_square, f.occupied_start⟩))

/-- Pieces do not become superimposed after a move. -/
lemma no_superimposed (pos pos') (hne : pos ≠ pos')
    (h : (b.contents.move_piece f.start_square f.end_square).occupied_at pos) :
    b.contents.move_piece f.start_square f.end_square pos ≠
      b.contents.move_piece f.start_square f.end_square pos' :=
λ H, hne (b.contents.retains_injectivity b.injects f.occupied_start h H)

variables (f)

/--
A `move` retains all indices, ignoring empty squares,
present on the `board` it operates on.
-/
lemma retains_surjectivity :
  function.surjective (b.contents.move_piece f.start_square f.end_square).index_at :=
b.contents.index_at_retains_surjectivity b.contains f.before_occupied_start

/-- A `move` retains accesing indices injectively on the `board` it operates on. -/
lemma retains_injectivity :
  (b.contents.move_piece f.start_square f.end_square).some_injective :=
b.contents.retains_injectivity b.injects f.before_occupied_start

/-- A valid `move` on a `board` retains a valid board state. -/
def perform_move : board m n ι K :=
{ pieces := b.pieces,
  contents := b.contents.move_piece f.start_square f.end_square,
  contains := f.retains_surjectivity,
  injects := f.retains_injectivity }


-- The length of the sequence
variables {o : ℕ}

/--
Define the mapping of `playfield`s after performing successive `move_piece`s
using the pairs of positions in the provided `elements`,
starting from the `start_board`.
-/
def scan_contents
  (start_board: board m n ι K)
  (elements : fin o → (m × n) × (m × n)) : fin (o + 1) → playfield m n ι :=
start_board.contents.move_sequence (vector.of_fn elements)

variables (m n ι K o)

/--
A move `sequence` represents a sequential set of moves from a starting `board`.

No inhabited instance because boards do not have an inhabited instance.
-/
@[nolint has_inhabited_instance]
structure sequence :=
(start_board : board m n ι K)
(elements : fin o → (m × n) × (m × n))
(all_occupied_start' :
  ∀ (e : fin o),
    ((scan_contents start_board elements) e.cast_succ).occupied_at (elements e).fst . tactic.exact_dec_trivial)
(all_unoccupied_end' :
  ∀ (e : fin o),
    ¬ ((scan_contents start_board elements) e.cast_succ).occupied_at (elements e).snd . tactic.exact_dec_trivial)

namespace sequence

variables {m n ι K o}
variables (s : sequence m n ι K o)

/-- Shorthand for referring to the contents at a sequence index `ixₒ : fin (o + 1)`. -/
def contents_at (ixₒ : fin (o + 1)) : playfield m n ι :=
(scan_contents s.start_board s.elements) ixₒ

/-- Shorthand for referring to the contents at a sequence index `ixₒ : fin (o + 1)`. -/
lemma contents_at_def (ixₒ : fin (o + 1)) :
  s.contents_at ixₒ = (scan_contents s.start_board s.elements) ixₒ := rfl

/-- Every scanned board is occupied at the start square of the upcoming move. -/
lemma all_occupied_start (e : fin o) : (s.contents_at e.cast_succ).occupied_at (s.elements e).fst :=
s.all_occupied_start' e

/-- Every scanned board is unoccupied at the end square of the upcoming move. -/
lemma all_unoccupied_end (e : fin o) : ¬ (s.contents_at e.cast_succ).occupied_at (s.elements e).snd :=
s.all_unoccupied_end' e

open playfield vector

/-- The first contents in a `scan_contents` `sequence` is of the `start_board`. -/
@[simp] lemma sequence_zero : s.contents_at 0 = s.start_board.contents :=
by simp only [contents_at_def, scan_contents, move_sequence_def, nth_zero, scanl_head]

/-- Any `contents_at` a step in the `sequence` is the result of performing a `move_piece` using
the `sequence.elements` at that step. -/
lemma sequence_step (e : fin o) :
  s.contents_at e.succ =
    (s.contents_at e.cast_succ).move_piece (s.elements e).fst (s.elements e).snd :=
by simp only [contents_at_def, scan_contents, move_sequence_def, scanl_nth, nth_of_fn]

/-- Every `playfield` in a sequence of moves contains all the indices it can. -/
lemma retains_surjectivity (ixₒ : fin (o + 1)) :
  function.surjective (s.contents_at ixₒ).index_at :=
begin
  apply fin.induction_on ixₒ,
  { rw sequence_zero,
    exact s.start_board.contains },
  { intros ix h,
    rw sequence_step,
    apply playfield.index_at_retains_surjectivity _ h,
    exact s.all_occupied_start _ },
end

/-- Every `playfield` in a sequence of moves injectively accesses the indices. -/
lemma retains_injectivity (ixₒ : fin (o + 1)) : (s.contents_at ixₒ).some_injective :=
begin
  apply fin.induction_on ixₒ,
  { simpa only [sequence_zero] using s.start_board.injects },
  { intros ix h,
    simp only [sequence_step],
    apply playfield.retains_injectivity _ h,
    exact s.all_occupied_start _ },
end

/-- Pieces do not disappear after any `move_piece` in a `sequence`. -/
lemma retains_pieces (ixₒ : fin (o + 1)) (ixᵢ : ι) :
  ixᵢ ∈ (s.contents_at ixₒ) :=
exists.elim (s.retains_surjectivity ixₒ ixᵢ) (λ pos h, h ▸ playfield.index_at_in pos)

/-- Pieces do not become superimposed after any `move` in a `sequence`. -/
lemma no_superimposed (ixₒ : fin (o + 1)) (pos pos') (hne : pos ≠ pos')
    (h : (s.contents_at ixₒ).occupied_at pos) :
      (s.contents_at ixₒ) pos ≠ (s.contents_at ixₒ) pos' :=
λ H, hne (s.retains_injectivity _ h H)

/-- The board which results from applying the first `ix₀ + 1` `move`s in the `sequence`. -/
def boards (ixₒ : fin (o + 1)) : board m n ι K :=
{ contents := s.contents_at ixₒ,
  pieces := s.start_board.pieces,
  contains := s.retains_surjectivity ixₒ,
  injects := s.retains_injectivity ixₒ }

/-- The board which results from applying all `move`s in the `sequence`. -/
def end_board : board m n ι K := s.boards (fin.last o)

variables {b}
variables (s)

/-- The `ix₀`'th `move` in the `sequence`. -/
def moves (ixₒ : fin o) : chess.move (s.boards ixₒ.cast_succ) :=
{ start_square := (s.elements ixₒ).fst,
  end_square := (s.elements ixₒ).snd,
  occupied_start := by { simpa only [boards] using s.all_occupied_start _ },
  unoccupied_end := by { simpa only [boards] using s.all_unoccupied_end _ } }

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
  { simpa only [sequence_zero] using h_pos },
  { intros ix' h,
    simpa only [sequence_step, move_piece_diff,
                h_unmentioned, ne.def, not_false_iff] using h },
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
