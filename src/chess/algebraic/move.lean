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

def perform_no_capture (b : board m n (fin i) colored_piece) (desc : move.description.chess m n)
  (pair : (m × n) × (m × n)) (hp : pair ∈ b.run_move desc) :
  option (board m n (fin i) colored_piece) :=
desc.capture.pbind_with
  (λ h, chess.move.perform_move
    (⟨pair.fst, pair.snd, desc.occupied_start b hp,
      desc.unoccupied_end_of_no_capture b hp h⟩ : chess.move b))
  (λ _ _, none)

def run_move_sequence_no_capture (b : board m n (fin i) colored_piece) (l : list string) :
  option (board m n (fin i) colored_piece) :=
mfoldl
  (λ B str, parse_to_some move.parser str >>= λ desc, (B.run_move desc).pbind
    (perform_no_capture B desc))
b l

end board

end chess

@[simp] lemma option.pbind_with_eq_some_of_const_none {α β : Type*}
  (x : option α) (g : x = none → option β) (b : β) :
  option.pbind_with x g (λ _ _, none) = some b ↔ x = none ∧ (Π (h : x = none), g h = some b) :=
by cases x; simp

variables {m n : Type} {i : ℕ}

variables [has_zero m] [has_one m] [has_add m]
variables [has_zero n] [has_one n] [has_add n]
variables [fintype m] [decidable_eq m] [linear_order m]
variables [fintype n] [decidable_eq n] [linear_order n]

lemma run_move_pbind (B b' : board m n (fin i) colored_piece) (desc) :
  (B.run_move desc).pbind (B.perform_no_capture desc) = some b'
  ->
  -- ↔
  desc.capture = none
  ∧ ∃ (pair : (m × n) × (m × n)) (hp : pair ∈ B.run_move desc),
  B.contents pair.fst = b'.contents pair.snd
  -- B.contents desc.to_description.from_sq = b'.contents desc.to_description.to_sq
  :=
begin
  intro h,
  cases hb : B.run_move desc,
  { simp only [option.pbind_eq_some, chess.board.perform_no_capture, option.coe_eq_some,
               option.pbind_with_eq_some_of_const_none, exists_and_distrib_left, prod.exists] at h,
    simp at hb,
  },
  { simp at hb },
  -- rw [hb] at h,
  -- cases hb : B.run_move desc,
  -- { simp [chess.board.run_move], },
  -- rw [chess.board.perform_no_capture],
end
