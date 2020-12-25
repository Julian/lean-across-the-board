import data.fintype.basic

import chess.move


/-!

# Legal chess move definitions and theorems

## Summary

Legal chess `move`s are moves which satisfy the legal rules of
chess. This includes both the mathematics of which squares a given
`piece` type can move to and the broader set of `board` conditions that
must be satisfied (e.g. not moving a `king` into check).

Only a subset of these rules are currently implemented below so far.
Currently:

  * knight move math

are what is implemented.

(No chess variants are currently implemented either.)

## Main definitions

1. `move.is_legal`, which can decide whether a given `move` is legal

2. `move.legal`, which represents a `move` along with the above proof
that the `move.is_legal`

3. `board.moves_from`, which given a position on the provided `board`,
produces the set of legal moves which may be performed from that square.

## Implementation notes

1. `moves_from` is currently defined to return a `finset`, even though
in theory topologically one could have boards with infinitely many
immediate next squares. This finiteness assumption will eventually need
fixing in other places, so it seems safe here for now.

2. The requirement of `decidable_eq` on the various types surrounding
`move.legal` means that again `dec_trivial` can automatically infer
proofs for move legality without them being explicitly provided.

-/


variables {m n: Type}

variables [fintype m] [decidable_eq m] [linear_order m]
variables [fintype n] [decidable_eq n] [linear_order n]
variables {ι : Type} [fintype ι] [decidable_eq ι]

variables {b : chess.board m n ι chess.colored_piece}

namespace chess

/-- The finite set of (presumably squares) between two elements of `m` (or `n`). -/
def between (left right : m) := {x | left ≤ x ∧ x ≤ right}.to_finset

local notation x `-` y := (between x y).card

/-- Two squares `pos` and `pos'` are adjacent (i.e. have no square between them). -/
@[derive decidable_pred]
def adjacent (pos pos' : m) :=
pos - pos' = 2 ∨ pos' - pos = 2

/-- Two squares `pos` and `pos'` have exactly one square between them. -/
@[derive decidable_pred]
def one_gap (pos pos' : m) :=
pos - pos' = 3 ∨ pos' - pos = 3

/-- A legal knight move moves 2 squares in one direction and 1 in the other. -/
@[derive decidable_pred]
def knight_move (stp enp : m × n) : Prop :=
(adjacent stp.fst enp.fst ∧ one_gap stp.snd enp.snd) ∨
  (one_gap stp.fst enp.fst ∧ adjacent stp.snd enp.snd)

@[derive decidable_pred]
def rook_move (stp enp : m × n) : Prop :=
(stp.fst - enp.fst = 0 ∧ 0 < stp.snd - enp.snd) ∨
  (stp.snd - enp.snd = 0 ∧ 0 < stp.fst - enp.fst)

@[derive decidable_pred]
def bishop_move (stp enp : m × n) : Prop :=
stp.fst - enp.fst = stp.snd - enp.snd ∧ 0 < stp.fst - enp.fst

@[derive decidable_pred]
def queen_move (stp enp : m × n) : Prop :=
rook_move stp enp ∨ bishop_move stp enp

@[derive decidable_pred]
def king_move (stp enp : m × n) : Prop :=
adjacent stp.fst enp.fst ∨ adjacent stp.snd enp.snd

-- no enpassant yet, no color based directionality, constant first type, changing second type
-- and not capture
@[derive decidable_pred]
def pawn_move (stp enp : m × n) : Prop :=
stp.fst = enp.fst ∧ adjacent stp.snd enp.snd

open chess.piece

def piece.move_rule : chess.piece → m × n → m × n → Prop
| bishop := bishop_move
| king := king_move
| knight := knight_move
| pawn := pawn_move
| queen := queen_move
| rook := rook_move

instance piece.move_rule.decidable_pred :
  Π (p : chess.piece) (stp : m × n), decidable_pred (p.move_rule stp)
| bishop := bishop_move.decidable_pred
| king := king_move.decidable_pred
| knight := knight_move.decidable_pred
| pawn := pawn_move.decidable_pred
| queen := queen_move.decidable_pred
| rook := rook_move.decidable_pred

namespace move

/-- A legal chess move. -/
def is_legal (f : chess.move b) : Prop :=
f.piece.piece.move_rule f.start_square f.end_square

/-- A legal knight move. -/
@[simp] lemma is_legal_knight_iff {f : chess.move b} (h_piece : knight = f.piece) :
  f.is_legal ↔ knight_move f.start_square f.end_square :=
begin
  unfold move.is_legal,
  unfold_coes at h_piece,
  rw ←h_piece,
  exact iff.rfl
end

instance is_legal_decidable {f : chess.move b} : decidable f.is_legal :=
piece.move_rule.decidable_pred f.piece.piece f.start_square f.end_square

variable (b)

/--
A legal move is a `move` along with a proof that the move satisfies the
rules of chess.

No inhabited instance because `move` is uninhabited.
-/
@[derive fintype, nolint has_inhabited_instance, ext]
structure legal extends chess.move b :=
(legality: (is_legal to_move) . tactic.exact_dec_trivial)

/--
A legal sequence is a move `sequence` along with a proof that all sequential
moves are legal.

No inhabited instance because `sequence` is uninhabited.
-/
@[nolint has_inhabited_instance]
structure sequence.legal extends chess.move.sequence m n ι chess.colored_piece :=
(legality: ∀ {i : ℕ} (hi : i < to_sequence.elements.length),
  is_legal (to_sequence.moves i hi) . tactic.exact_dec_trivial)

end move

namespace board

variable (b)

/-- The `finset` of `legal` moves from a given square. -/
def moves_from (pos : m × n) : finset (move.legal b) :=
{x : move.legal b | x.start_square = pos}.to_finset

/-- The `finset` of `legal` moves from a given square. -/
lemma moves_from_def (pos : m × n) :
  b.moves_from pos = {x : move.legal b | x.start_square = pos}.to_finset := rfl

/-- The `finset` of `legal` moves from a given square. -/
@[simp] lemma mem_moves_from {pos : m × n} (x : move.legal b) :
    x ∈ (b.moves_from pos) ↔ x.to_move.start_square = pos :=
by simp only [moves_from_def, set.mem_to_finset, set.mem_set_of_eq]

variable (pos : m × n)

end board

section bounds

variable {pos : m × n}

/-- There are 0 `legal` moves from an unoccupied square. -/
lemma moves_from.unoccupied_empty
  (h_empty : ¬ b.contents.occupied_at pos . tactic.exact_dec_trivial) :
    b.moves_from pos = ∅ := begin
    rw finset.eq_empty_iff_forall_not_mem,
    intro x,
    by_contradiction h',
    rw board.mem_moves_from at h',
    rw ←h' at h_empty,
    have h_occ := x.occupied_start,
    contradiction,
end

end bounds

end chess
