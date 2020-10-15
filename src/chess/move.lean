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

(Captures are not implemented yet.)
-/
structure move :=
(start_square : m × n)
(end_square : m × n)
(diff_squares : start_square ≠ end_square . tactic.exact_dec_trivial)
(occupied_start : b.contents.occupied_at start_square . tactic.exact_dec_trivial)
(unoccupied_end : ¬ b.contents.occupied_at end_square . tactic.exact_dec_trivial)

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

lemma end_square_is_some_after :
  (b.contents.move_piece f.start_square f.end_square f.end_square).is_some :=
by simp only [option.ne_none_iff_is_some.mp f.occupied_start, playfield.move_piece_end]

lemma start_square_is_none_after :
  (b.contents.move_piece f.start_square f.end_square f.start_square).is_none :=
by simp only [after_unoccupied_start, bool.coe_sort_tt, option.is_none_none]

lemma end_square_is_none :
  (b.contents f.end_square).is_none :=
by simp only [before_unoccupied_end, bool.coe_sort_tt, option.is_none_none]

@[simp] lemma before_after_is_some (pos : m × n)
    (h : pos ≠ f.start_square) (h' : pos ≠ f.end_square) :
    (b.contents.move_piece f.start_square f.end_square pos).is_some ↔ (b.contents pos).is_some :=
by simp only [h, h', before_after_same, ne.def, not_false_iff]

/-- The piece that is being moved. -/
def piece : K :=
(b.pieces (option.get f.start_square_is_some))

/-- Pieces do not become superimposed after a move. -/
lemma no_superimpose (pos pos') (hne : pos ≠ pos')
    (h : b.contents.move_piece f.start_square f.end_square pos ≠ __)
    ⦃h' : b.contents.move_piece f.start_square f.end_square pos' ≠ __⦄ :
    b.contents.move_piece f.start_square f.end_square pos ≠
      b.contents.move_piece f.start_square f.end_square pos' :=
λ H, hne (playfield.retains_injectivity b.injects f.before_occupied_start H h)

variables (f)

lemma retains_surjectivity :
  function.surjective (b.contents.move_piece f.start_square f.end_square).index_at :=
begin
  intro ix,
  obtain ⟨six', hsi⟩ := b.contents.occupied_has_some.mp f.start_square_is_some,
  obtain ⟨P, hP⟩ := b.contains ix,
  have hP' := congr_arg some hP,
  rw ←hP,
  simp only [playfield.index_at_some, coe_coe] at hP',
  rcases split_eq (P : m × n) f.start_square f.end_square with H|H|⟨hS, hE⟩,
  { use f.end_square,
    { convert f.end_square_is_some_after },
    { use f.end_square,
      split,
      { simp only [option.some_get] },
      { intros sq hsq,
        simp only [option.some_get, playfield.move_piece_def, equiv.swap_apply_right] at hsq,
        have := f.start_square_is_some,
        rw [←hsq] at this,
        rw b.inj_iff this at hsq,
        rcases split_eq sq f.start_square f.end_square with rfl|rfl|⟨hS', hE'⟩,
        { simpa only [equiv.swap_apply_left] using hsq.symm},
        { refl },
        { simp only [equiv.swap_apply_of_ne_of_ne, hS', hE', ne.def, not_false_iff] at hsq,
          contradiction } } },
    { apply option.some.inj,
      simp only [playfield.index_at_some, playfield.move_piece_end, subtype.coe_mk, coe_coe, H] } },
  { rw coe_coe at H,
    exfalso,
    simpa only [H, f.before_unoccupied_end] using hP' },
  { rw coe_coe at hS hE,
    use P,
    { simpa only [hS, hE, move.before_after_same, ne.def, not_false_iff, coe_coe] using P.val.property },
    { use P,
      split,
      { simp only [option.some_get] },
      { intros sq hsq,
        simp only [option.some_get, coe_coe, hS, hE, playfield.move_piece_def,
                   move.before_after_same, ne.def, not_false_iff] at hsq,
        have := P.val.property,
        rw [subtype.val_eq_coe, subtype.val_eq_coe, ←hsq] at this,
        rw b.inj_iff this at hsq,
        rcases split_eq sq f.start_square f.end_square with rfl|rfl|⟨hS', hE'⟩,
        { simpa only [equiv.swap_apply_left] using hsq.symm },
        { simp only [equiv.swap_apply_right] at this hsq,
          exact absurd hsq.symm hS },
        { simpa only [equiv.swap_apply_of_ne_of_ne, hS', hE', ne.def, not_false_iff] using hsq } } },
    { apply option.some.inj,
      simp only [hS, hE, playfield.index_at_some, move.before_after_same, ne.def, not_false_iff, subtype.coe_mk, coe_coe] } }
end

-- this was my original grueling proof
--   contains := by {
--     unfold function.surjective,
--     intro ix,
--     obtain ⟨ix', hi⟩ := b.contents.occupied_has_some.mp f.start_square_is_some,
--     obtain ⟨P, hP⟩ := b.contains ix,
--     have hP' := congr_arg some hP,
--     simp only [playfield.index_at_some, coe_coe] at hP',
--     by_cases h : (ix = ix'),
--     { use f.end_square,
--       { convert f.end_square_is_some_after },
--       { use f.end_square,
--         split,
--         { simp only [option.some_get]},
--         { intros sq hsq,
--           rcases split_eq sq f.start_square f.end_square with rfl|rfl|⟨hS', hE'⟩,
--           { simp only [option.some_get, playfield.move_piece_end, move.after_unoccupied_start] at hsq,
--             simpa only [move.before_occupied_start] using hsq.symm },
--           { refl },
--           { simp only [hS', hE', option.some_get, move.before_after_same,
--                        playfield.move_piece_end, ne.def, not_false_iff] at hsq,
--             have := f.start_square_is_some,
--             rw [←hsq] at this,
--             rw b.inj_iff this at hsq,
--             contradiction } } },
--       { apply option.some.inj,
--         simp only [playfield.index_at_some, playfield.move_piece_end, subtype.coe_mk, coe_coe],
--         rwa [←h] at hi } },
--     { rcases split_eq (P : m × n) f.start_square f.end_square with H|H|⟨hS, hE⟩,
--       { rw ←hP,
--         exfalso,
--         rw coe_coe at H,
--         apply h,
--         apply option.some.inj,
--         rw [←hi, ←hP],
--         simp only [H, playfield.index_at_some, coe_coe, equiv.swap_apply_right] },
--       { use f.end_square,
--         { convert f.end_square_is_some_after },
--         { use f.end_square,
--           split,
--           { simp only [option.some_get]},
--           { intros sq hsq,
--             rcases split_eq sq f.start_square f.end_square with rfl|rfl|⟨hS', hE'⟩,
--             { simp only [option.some_get, playfield.move_piece_end, move.after_unoccupied_start] at hsq,
--               simpa only [move.before_occupied_start] using hsq.symm },
--             { refl },
--             { simp only [hS', hE', option.some_get, move.before_after_same,
--                         playfield.move_piece_end, ne.def, not_false_iff] at hsq,
--               have := f.start_square_is_some,
--               rw [←hsq] at this,
--               rw b.inj_iff this at hsq,
--               contradiction } } },
--         { exfalso,
--           rw coe_coe at H,
--           have := congr_arg some hP,
--           simpa only [H, playfield.index_at_some, move.before_unoccupied_end, coe_coe] using this} },
--       { rw coe_coe at hS hE,
--         use P,
--         { convert P.val.property,
--           simp only [hS, hE, move.before_after_same, ne.def, not_false_iff, subtype.val_eq_coe, coe_coe] },
--         { use P,
--           split,
--           { simp only [option.some_get] },
--           { intros sq hsq,
--             simp only [hS, hE, option.some_get, move.before_after_same, ne.def, not_false_iff, coe_coe] at hsq,
--             rcases split_eq sq f.start_square f.end_square with rfl|rfl|⟨hS', hE'⟩,
--             { rw move.after_unoccupied_start at hsq,
--               exact absurd P.val.property (option.not_is_some_iff_eq_none.mpr hsq.symm) },
--             { have := congr_arg some hP,
--               simp only [playfield.index_at_some, equiv.swap_apply_right, playfield.move_piece_end, coe_coe] at this hsq,
--               rw [this, hi] at hsq,
--               exact absurd (option.some.inj hsq) (ne.symm h) },
--             { simp only [hS', hE', option.some_get, move.before_after_same,
--                           playfield.move_piece_end, ne.def, not_false_iff] at hsq,
--               have := P.val.property,
--               simp only [subtype.val_eq_coe, ←hsq] at this,
--               rwa ←b.inj_iff this } } },
--         { simp_rw ←hP,
--           apply option.some.inj,
--           simp only [hS, hE, playfield.index_at_some, move.before_after_same, ne.def, not_false_iff, subtype.coe_mk, coe_coe] } } }
--   }
-- }


/-- A valid `move` on a `board` retains a valid board state. -/
def perform_move : board m n ι K :=
{ pieces := b.pieces,
  contents := b.contents.move_piece f.start_square f.end_square,
  contains := retains_surjectivity b f,
  injects := retains_injectivity b f
   }


-- The length of the sequence
variables {o : ℕ}

def scan_contents
  (start_board: board m n ι K)
  (elements : fin o → (m × n) × (m × n)) : fin (o + 1) → playfield m n ι :=
start_board.contents.move_sequence (vector.of_fn elements)

variables (m n ι K o)

/--
A move `sequence` represents a sequential set of moves from a starting `board`.
-/
structure sequence :=
(start_board : board m n ι K)
(elements : fin o → (m × n) × (m × n))
(all_diff_squares :
  ∀ (e : fin o),
    (elements e).fst ≠ (elements e).snd . tactic.exact_dec_trivial)
(all_occupied_start' :
  ∀ (e : fin o),
    ((scan_contents start_board elements) e.cast_succ) (elements e).fst ≠ __ . tactic.exact_dec_trivial)
(all_unoccupied_end' :
  ∀ (e : fin o),
    ((scan_contents start_board elements) e.cast_succ) (elements e).snd = __ . tactic.exact_dec_trivial)

namespace sequence

variables {m n ι K o}
variables (s : sequence m n ι K o)

/-- Shorthand for referring to the contents at a sequence index `ixₒ : fin (o + 1)`. -/
def contents_at (ixₒ : fin (o + 1)) : playfield m n ι :=
(scan_contents s.start_board s.elements) ixₒ

/-- Shorthand for referring to the contents at a sequence index `ixₒ : fin (o + 1)`. -/
lemma contents_at_def (ixₒ : fin (o + 1)) :
  s.contents_at ixₒ = (scan_contents s.start_board s.elements) ixₒ := rfl

lemma all_occupied_start (e : fin o) : (s.contents_at e.cast_succ) (s.elements e).fst ≠ __ :=
s.all_occupied_start' e

lemma all_unoccupied_end (e : fin o) : (s.contents_at e.cast_succ) (s.elements e).snd = __ :=
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

/-- Pieces do not disappear after any `move_piece` in a `sequence`. -/
lemma retains_pieces (ixₒ : fin (o + 1)) (ixᵢ : ι) :
  ixᵢ ∈ (s.contents_at ixₒ) :=
begin
  apply fin.induction_on ixₒ,
  { simpa only [sequence_zero] using s.start_board.contains_pieces ixᵢ },
  { rintros ix h,
    simpa only [sequence_step] using playfield.retains_pieces _ _ _ _ h },
end

lemma retains_injectivity (ixₒ : fin (o + 1)) : (s.contents_at ixₒ).some_injective :=
begin
  apply fin.induction_on ixₒ,
  { simpa only [sequence_zero] using s.start_board.contents_is_some_injective },
  { intros ix h,
    simp only [sequence_step],
    apply playfield.retains_injectivity h,
    exact s.all_occupied_start _ },
end

/-- Pieces do not become superimposed after any `move` in a `sequence`. -/
lemma no_superimpose (ixₒ : fin (o + 1)) (pos pos') (hne : pos ≠ pos')
    (h : (s.contents_at ixₒ) pos ≠ __)
    ⦃h' : (s.contents_at ixₒ) pos' ≠ __⦄ :
      (s.contents_at ixₒ) pos ≠
      (s.contents_at ixₒ) pos' :=
λ H, hne (s.retains_injectivity _ H h)

/-- The board which results from applying the first `ix₀ + 1` `move`s in the `sequence`. -/
def boards (ixₒ : fin (o + 1)) : board m n ι K :=
{ contents := s.contents_at ixₒ,
  pieces := s.start_board.pieces,
  contains_pieces := s.retains_pieces ixₒ,
  no_superimposed_pieces := s.no_superimpose ixₒ }

/-- The board which results from applying all `move`s in the `sequence`. -/
def end_board : board m n ι K := s.boards (fin.last o)

variables {b s}

/-- The `ix₀`'th `move` in the `sequence`. -/
def moves (ixₒ: fin o) : chess.move (s.boards ixₒ.cast_succ) :=
{ start_square := (s.elements ixₒ).fst,
  end_square := (s.elements ixₒ).snd,
  diff_squares := s.all_diff_squares ixₒ,
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
