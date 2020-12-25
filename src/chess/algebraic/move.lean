import chess.move.description
import chess.algebraic

open chess

namespace chess

namespace board

variables {m n : Type} {i : ℕ}

variables [has_zero m] [has_one m] [has_add m]
variables [has_zero n] [has_one n] [has_add n]
variables [fintype m] [decidable_eq m] [linear_order m]
variables [fintype n] [decidable_eq n] [linear_order n]

def run_move_sequence_no_capture (b : board m n (fin i) colored_piece) (l : list string) :
  option (board m n (fin i) colored_piece) :=
mfoldl
  (λ B str, parse_to_some move.parser str >>= λ desc, (B.run_move desc).pbind
    (λ pair hp, desc.capture.pbind_with
      (λ h, chess.move.perform_move (
        ⟨pair.fst, pair.snd, desc.occupied_start B hp, desc.unoccupied_end_of_no_capture B hp h⟩
        : chess.move B))
      (λ _ _, none)
    )
  )
b l

end board

end chess
