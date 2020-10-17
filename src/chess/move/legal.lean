import chess.move

namespace chess.move

variables {m n: Type}

variables [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]
variables {ι : Type} [fintype ι] [decidable_eq ι]

variables {b : chess.board m n ι chess.colored_pieces}

open chess.pieces

def is_legal (f : chess.move b) : Prop :=
match f.piece.piece with
  | knight := true
  | _ := false
end

/--
A legal move is a `move` along with a proof that the move satisfies the rules of chess.
-/
structure legal extends chess.move b :=
(legality: (is_legal to_move) . tactic.exact_dec_trivial)

variables {o : ℕ}

structure sequence.legal extends chess.move.sequence m n ι chess.colored_pieces o :=
(legality: ∀ (i : fin o), is_legal (to_sequence.moves i) . tactic.exact_dec_trivial)

end chess.move
