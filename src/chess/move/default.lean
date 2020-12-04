import data.equiv.basic
import tactic.dec_trivial
import tactic.derive_fintype

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
@[derive [decidable_eq, fintype], nolint has_inhabited_instance]
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
def piece : K := b.piece_at f.start_square f.occupied_start

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

/--
Define the mapping of `playfield`s after performing successive `move_piece`s
using the pairs of positions in the provided `elements`,
starting from the `start_board`.
-/
def scan_contents
  (start_board: board m n ι K)
  (elements : list ((m × n) × (m × n))) : list (playfield m n ι) :=
start_board.contents.move_sequence elements

variables (m n ι K)

/--
A move `sequence` represents a sequential set of moves from a starting `board`.

No inhabited instance because boards do not have an inhabited instance.
-/
@[nolint has_inhabited_instance]
structure sequence :=
(start_board : board m n ι K)
(elements : list ((m × n) × (m × n)))
(all_occupied_start' :
  ∀ {e : ℕ} (he : e < elements.length),
    ((start_board.contents.playfield_at elements he).occupied_at (elements.nth_le e he).fst) . tactic.exact_dec_trivial)
(all_unoccupied_end' :
  ∀ {e : ℕ} (he : e < elements.length),
    ¬ ((start_board.contents.playfield_at elements he).occupied_at (elements.nth_le e he).snd) . tactic.exact_dec_trivial)

namespace sequence

variables {m n ι K}
variables (s : sequence m n ι K)

/-- Shorthand for referring to the contents at a sequence index `ixₒ : fin (o + 1)`. -/
def contents_at {i : ℕ} (ixₒ : i < s.elements.length) : playfield m n ι :=
s.start_board.contents.playfield_at s.elements ixₒ

/-- Shorthand for referring to the contents at a sequence index `ixₒ : fin (o + 1)`. -/
lemma contents_at_def {i : ℕ} (ixₒ : i < s.elements.length) :
  s.contents_at ixₒ = s.start_board.contents.playfield_at s.elements ixₒ := rfl

/-- Shorthand for referring to the contents at a sequence index `ixₒ : fin (o + 1)`. -/
def contents_after {i : ℕ} (ixₒ : i < s.elements.length) : playfield m n ι :=
s.start_board.contents.playfield_after s.elements ixₒ

/-- Shorthand for referring to the contents at a sequence index `ixₒ : fin (o + 1)`. -/
lemma contents_after_def {i : ℕ} (ixₒ : i < s.elements.length) :
  s.contents_after ixₒ = s.start_board.contents.playfield_after s.elements ixₒ := rfl

/-- Every scanned board is occupied at the start square of the upcoming move. -/
lemma all_occupied_start {e : ℕ} (he : e < s.elements.length) :
  (s.contents_at he).occupied_at (s.elements.nth_le e he).fst :=
s.all_occupied_start' he

/-- Every scanned board is unoccupied at the end square of the upcoming move. -/
lemma all_unoccupied_end {e : ℕ} (he : e < s.elements.length) :
  ¬ (s.contents_at he).occupied_at (s.elements.nth_le e he).snd :=
s.all_unoccupied_end' he

open playfield vector list

lemma contents_at_succ {e : ℕ} (he : e + 1 < s.elements.length) :
  s.contents_at he = s.contents_after (nat.lt_of_succ_lt he) :=
by simp only [contents_at_def, contents_after_def, playfield_at_def, playfield_after_def]

/-- The first contents in a `scan_contents` `sequence` is of the `start_board`. -/
@[simp] lemma sequence_zero {h : 0 < s.elements.length} :
  s.contents_at h = s.start_board.contents :=
by  simp only [contents_at_def, move_sequence_def, playfield_at_def, nth_le_zero_scanl]

/-- Any `contents_at` a step in the `sequence` is the result of performing a `move_piece` using
the `sequence.elements` at that step. -/
lemma sequence_step {e : ℕ} (he : e < s.elements.length) :
  s.contents_after he =
    (s.contents_at he).move_piece
    (s.elements.nth_le e he).fst (s.elements.nth_le e he).snd :=
by simp only [contents_at_def, contents_after_def, playfield_after_eq_move]

/-- Every scanned board is unoccupied at the start square of the previous move. -/
lemma all_unoccupied_start_after {e : ℕ} (he : e < s.elements.length) :
  ¬ (s.contents_after he).occupied_at (s.elements.nth_le e he).fst :=
by { rw [sequence_step, move_piece_occupied_start], exact all_unoccupied_end s he }

/-- Every scanned board is occupied at the end square of the previous move. -/
lemma all_occupied_end_after {e : ℕ} (he : e < s.elements.length) :
  (s.contents_after he).occupied_at (s.elements.nth_le e he).snd :=
by { rw [sequence_step, move_piece_occupied_end], exact all_occupied_start s he }

/-- Every `playfield` in a sequence of moves contains all the indices it can. -/
lemma retains_surjectivity {e : ℕ} (he : e < s.elements.length) :
  function.surjective (s.contents_at he).index_at :=
begin
  induction e with e IH,
  { rw sequence_zero,
    exact s.start_board.contains },
  { rw [contents_at_succ, sequence_step],
    exact (s.contents_at (nat.lt_of_succ_lt he)).index_at_retains_surjectivity
      (IH (nat.lt_of_succ_lt he)) (all_occupied_start _ _) }
end

/-- Every `playfield` in a sequence of moves contains all the indices it can. -/
lemma retains_surjectivity_after {e : ℕ} (he : e < s.elements.length) :
  function.surjective (s.contents_after he).index_at :=
begin
  rw sequence_step,
  exact (s.contents_at he).index_at_retains_surjectivity (retains_surjectivity _ _)
    (all_occupied_start _ _)
end

/-- Every `playfield` in a sequence of moves injectively accesses the indices. -/
lemma retains_injectivity {e : ℕ} (he : e < s.elements.length) :
  (s.contents_at he).some_injective :=
begin
  induction e with e IH,
  { rw sequence_zero,
    exact s.start_board.injects },
  { rw [contents_at_succ, sequence_step],
    apply playfield.retains_injectivity _ (IH (nat.lt_of_succ_lt he)),
    exact s.all_occupied_start _ }
end

/-- Every `playfield` in a sequence of moves injectively accesses the indices. -/
lemma retains_injectivity_after {e : ℕ} (he : e < s.elements.length) :
  (s.contents_after he).some_injective :=
begin
  rw sequence_step,
  exact (s.contents_at he).retains_injectivity (retains_injectivity _ _)
    (all_occupied_start _ _)
end

/-- Pieces do not disappear after any `move_piece` in a `sequence`. -/
lemma retains_pieces {e : ℕ} (ixₒ : e < s.elements.length) (ixᵢ : ι) :
  ixᵢ ∈ (s.contents_after ixₒ) :=
exists.elim (s.retains_surjectivity_after ixₒ ixᵢ) (λ pos h, h ▸ playfield.index_at_in pos)

/-- Pieces do not become superimposed after any `move` in a `sequence`. -/
lemma no_superimposed {e : ℕ} (ixₒ : e < s.elements.length) (pos pos') (hne : pos ≠ pos')
    (h : (s.contents_after ixₒ).occupied_at pos) :
      (s.contents_after ixₒ) pos ≠ (s.contents_after ixₒ) pos' :=
λ H, hne (s.retains_injectivity_after _ h H)

/-- The board which results from applying the first `ix₀ + 1` `move`s in the `sequence`. -/
def boards (e : ℕ) (ixₒ : e < s.elements.length) : board m n ι K :=
{ contents := s.contents_after ixₒ,
  pieces := s.start_board.pieces,
  contains := s.retains_surjectivity_after ixₒ,
  injects := s.retains_injectivity_after ixₒ }

/-- The board which results from applying all `move`s in the `sequence`. -/
def end_board : board m n ι K :=
  dite (s.elements.length = 0) (λ _, s.start_board)
    (λ h, s.boards (s.elements.length - 1) (nat.pred_lt h))

/-- The board which on which the first `ix₀ + 1` `move`s in the `sequence` is applied. -/
def boards_before (e : ℕ) (ixₒ : e < s.elements.length) : board m n ι K :=
{ contents := s.contents_at ixₒ,
  pieces := s.start_board.pieces,
  contains := s.retains_surjectivity ixₒ,
  injects := s.retains_injectivity ixₒ }

variables {b}
variables (s)

/-- The `ix₀`'th `move` in the `sequence`. -/
def moves (e : ℕ) (he : e < s.elements.length) : chess.move (s.boards_before e he) :=
{ start_square := (s.elements.nth_le e he).fst,
  end_square := (s.elements.nth_le e he).snd,
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
  (h_unmentioned : ∀ {e : ℕ} (ixₒ : e < s.elements.length),
    pos ≠ (s.elements.nth_le e ixₒ).fst ∧ pos ≠ (s.elements.nth_le e ixₒ).snd) :
    ∀ {e : ℕ} (ixₒ : e < s.elements.length), (s.boards e ixₒ).contents pos = some ixᵢ :=
begin
  dsimp [boards, scan_contents],
  intros e he,
  rw [sequence_step, move_piece_diff _ (h_unmentioned _).left (h_unmentioned _).right],
  induction e with e IH,
  { simpa only [sequence_zero] using h_pos },
  { simp only [sequence_step, move_piece_diff, contents_at_succ, h_unmentioned,
               ne.def, not_false_iff],
    apply IH }
end

end sequence
end move

namespace board

variable (b)

/--
Assert the existence of a `sequence` of length `o` from a `start_board` to a given end board.
-/
def has_sequence_len (end_board: board m n ι K) (o : ℕ) :=
    ∃ (s : chess.move.sequence m n ι K), b ≈ s.start_board ∧ end_board ≈ s.end_board

/-- Assert the existence of a `sequence` from a `start_board` to a given end board. -/
def has_sequence_to (end_board: board m n ι K) :=
    ∃ (o : ℕ), b.has_sequence_len end_board o

end board

end chess
