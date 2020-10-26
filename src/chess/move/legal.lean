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

namespace chess

variables {m n: Type}

variables [fintype m] [decidable_eq m] [decidable_linear_order m]
variables [fintype n] [decidable_eq n] [decidable_linear_order n]
variables {ι : Type} [fintype ι] [decidable_eq ι]

variables {b : chess.board m n ι chess.colored_piece}

namespace move

/-- The finite set of (presumably squares) between two elements of `m` (or `n`). -/
def between (left right : m) := {x | left ≤ x ∧ x ≤ right}.to_finset

/-- Two squares `pos` and `pos'` are adjacent (i.e. have no square between them). -/
@[derive decidable_pred]
def adjacent (pos pos' : m) :=
(between pos pos').card = 2 ∨ (between pos' pos).card = 2

/-- Two squares `pos` and `pos'` have exactly one square between them. -/
@[derive decidable_pred]
def one_gap (pos pos' : m) :=
(between pos pos').card = 3 ∨ (between pos' pos).card = 3

/-- A legal knight move moves 2 squares in one direction and 1 in the other. -/
@[derive decidable_pred]
def knight_move (stp enp : m × n) : Prop :=
((adjacent stp.fst enp.fst) ∧ (one_gap stp.snd enp.snd)) ∨
  ((one_gap stp.fst enp.fst) ∧ (adjacent stp.snd enp.snd))

open chess.piece

/-- A legal chess move. -/
def is_legal (f : chess.move b) : Prop :=
match (f.piece : chess.piece) with
| knight := knight_move f.start_square f.end_square
| _ := false
end

instance is_legal_decidable {f : chess.move b} : decidable f.is_legal := begin
  unfold is_legal,
  unfold_coes,
  cases f.piece.piece,
  case knight { dsimp [is_legal], exact or.decidable, },
  case bishop { exact decidable.false },
  case king { exact decidable.false },
  case pawn { exact decidable.false },
  case queen { exact decidable.false },
  case rook { exact decidable.false }
end

variable (b)

/--
A legal move is a `move` along with a proof that the move satisfies the
rules of chess.
-/
@[derive fintype]
structure legal extends chess.move b :=
(legality: (is_legal to_move) . tactic.exact_dec_trivial)

variables {o : ℕ}

structure sequence.legal extends chess.move.sequence m n ι chess.colored_piece o :=
(legality: ∀ (i : fin o), is_legal (to_sequence.moves i) . tactic.exact_dec_trivial)

end move

namespace board

variable (b)

/-- The `finset` of `legal` moves from a given square. -/
@[derive fintype]
def moves_from (pos : m × n) : set (move.legal b) :=
{x : move.legal b | x.start_square = pos}

/-- The `finset` of `legal` moves from a given square. -/
lemma moves_from_def (pos : m × n) :
  b.moves_from pos = {x : move.legal b | x.start_square = pos} := rfl

/-- The `finset` of `legal` moves from a given square. -/
@[simp] lemma mem_moves_from {pos : m × n} (x : move.legal b) :
    x ∈ (b.moves_from pos) ↔ x.to_move.start_square = pos := iff.rfl

end board

section bounds

variable {pos : m × n}

/-- There are 0 `legal` moves from an unoccupied square. -/
lemma moves_from.unoccupied_zero
  (h_empty : ¬ b.contents.occupied_at pos . tactic.exact_dec_trivial) :
    ∀ (x : move.legal b), x ∉ (b.moves_from pos) := begin
    intro x,
    refine ne.elim _,
    by_contradiction h',
    push_neg at h',
    rw ←h' at h_empty,
    have h_occ := x.occupied_start,
    contradiction,
end

end bounds

end chess
