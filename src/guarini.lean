import chess.notation
import chess.algebraic.move

/-!

"Proof" of Guarini's Problem: swapping some knights.

Given a board like:

    ♞ _ ♞
    _ _ _
    ♘ _ ♘

Guarini's problem asks for a sequence of moves that swaps the knights,
producing:

    ♘ _ ♘
    _ _ _
    ♞ _ ♞

Solution:

    ♞ _ ♞     ♞ _ ♞     ♞ _ _     ♞ _ ♘     _ _ ♘
    _ _ _  →  ♘ _ _  →  ♘ _ _  →  _ _ _  →  _ _ ♞
    ♘ _ ♘     ♘ _ _     ♘ ♞ _     ♘ ♞ _     ♘ ♞ _


              _ ♘ ♘     _ _ ♘     _ _ ♘     _ _ ♘
           →  _ _ ♞  →  _ _ ♞  →  ♘ _ ♞  →  ♘ _ _
              _ ♞ _     _ ♞ ♘     _ ♞ _     ♞ ♞ _


              _ ♞ ♘     ♞ ♞ ♘     _ ♞ ♘     _ ♞ _
           →  ♘ _ _  →  ♘ _ _  →  ♘ _ ♞  →  ♘ _ ♞
              _ ♞ _     _ _ _     _ _ _     _ ♘ _


              ♘ ♞ _     ♘ ♞ ♘     ♘ ♞ ♘     ♘ _ ♘
           →  ♘ _ ♞  →  _ _ ♞  →  _ _ _  →  _ _ _
              _ _ _     _ _ _     ♞ _ _     ♞ _ ♞

-/


def starting_position : chess.board _ _ _ _ := listboard [
    [♞, __, ♞],
    [__, __, __],
    [♘, __, ♘] ]


def ending_position : chess.board _ _ _ _ := {
  starting_position with
  pieces := ![♘, ♘, ♞, ♞],
}

-- Direct solution

def guarini_seq : chess.move.sequence.legal :=
{ start_board := starting_position,
  elements := [
  ((2, 0), (0, 1)),
  ((2, 2), (1, 0)),
  ((0, 1), (2, 2)),
  ((0, 2), (2, 1)),
  ((0, 0), (1, 2)),
  ((1, 2), (2, 0)),
  ((2, 0), (0, 1)),
  ((2, 1), (0, 0)),
  ((0, 0), (1, 2)),
  ((1, 0), (0, 2)),
  ((0, 2), (2, 1)),
  ((2, 2), (1, 0)),
  ((1, 0), (0, 2)),
  ((0, 1), (2, 2)),
  ((2, 1), (0, 0)),
  ((1, 2), (2, 0))] }


def guarini_algebraic : list string :=
  [
    "Nab1",
    "N3a2",
    "Nbc3",
    "Ncb3",
    "Nac2",
    "Nca3",
    "Nab1",
    "Nba1",
    "Nac2",
    "Nac1",
    "Ncb3",
    "Nca2",
    "Nac1",
    "Nbc3",
    "Nba1",
    "Nca3"
  ]

#eval starting_position.run_move_sequence_no_capture guarini_algebraic
/-
(some ♞, ♞, ♘, ♘;

♘, ＿, ♘;
＿, ＿, ＿;
♞, ＿, ♞)
-/

#eval some ending_position
/-
(some ♘, ♘, ♞, ♞;

♘, ＿, ♘;
＿, ＿, ＿;
♞, ＿, ♞)
-/
-- set_option trace.simp_lemmas true
-- set_option trace.simplify.rewrite true

lemma guarini_SAN :
  ((starting_position.run_move_sequence_no_capture guarini_algebraic).map chess.board.reduce) =
  some ending_position.reduce :=
begin
  rw guarini_algebraic,
  rw chess.board.run_move_sequence_no_capture,
  simp only [option.coe_eq_some, list.mfoldl_cons, list.mfoldl_nil, option.bind_eq_some,
             option.map_eq_some', bind_pure],
  simp only [option.pbind_with_eq_some_of_const_none],
end

#exit


def first_move : chess.move starting_position :=
let pair := guarini_seq.elements.nth_le 0 dec_trivial in ⟨pair.fst, pair.snd, dec_trivial, dec_trivial⟩

example : guarini_seq.to_sequence.boards_before 0 dec_trivial ≈ guarini_seq.start_board := dec_trivial

example : guarini_seq.to_sequence.boards 0 dec_trivial ≈ first_move.perform_move := dec_trivial

example : ∀ ix (hix : ix < guarini_seq.elements.length),
  (guarini_seq.elements.nth_le ix hix).fst ≠ (guarini_seq.elements.nth_le ix hix).snd := dec_trivial

lemma guarini : starting_position.has_sequence_to ending_position :=
⟨guarini_seq.elements.length, guarini_seq.to_sequence, dec_trivial⟩

-- #check eval_expr

/-
deep recursion was detected at 'replace' (potential solution: increase stack space in your system)
-/

-- Graph-equivalence
