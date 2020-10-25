import data.fintype.basic

import chess.move

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

variable b
/--
A legal move is a `move` along with a proof that the move satisfies the rules of chess.
-/
structure legal extends chess.move b :=
(legality: (is_legal to_move) . tactic.exact_dec_trivial)

variables {o : ℕ}

structure sequence.legal extends chess.move.sequence m n ι chess.colored_piece o :=
(legality: ∀ (i : fin o), is_legal (to_sequence.moves i) . tactic.exact_dec_trivial)

end move

namespace board

variable (b)

/-- The `set` of `legal` moves from a given square. -/
def moves_from (pos : m × n) : set (move.legal b) :=
{x : move.legal b | x.start_square = pos}.to_finset

/-
/-- The `set` of `legal` moves from a given square. -/
lemma moves_from_def (pos : m × n) :
  b.moves_from pos = {x : move.legal b | x.start_square = pos}.to_finset := rfl
-/

lemma knight_max_8_moves
  {pos : m × n}
  (h_occ : b.contents.occupied_at pos . tactic.exact_dec_trivial)
  (h_knight : chess.piece.knight = (b.piece_at pos h_occ) . tactic.exact_dec_trivial)
  : (b.moves_from pos).to_finset.card <= 8 :=
begin
  sorry,
end

end board

end chess
