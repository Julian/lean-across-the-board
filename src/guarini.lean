import chess.move
import data.vector2

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


def starting_position : chess.board _ _ _ _ := {
  pieces := ![♞, ♞, ♘, ♘],
  contents := PF ![
    ![(0 : fin 4), __, (1 : fin 4)],
    ![    __,      __,       __   ],
    ![(2 : fin 4), __, (3 : fin 4)]
  ],
}


def ending_position : chess.board _ _ _ _ := {
  starting_position with
  pieces := ![♘, ♘, ♞, ♞],
}

-- Direct solution

def guarini_seq : fin _ → ((fin 3 × fin 3) × (fin 3 × fin 3)) := ![
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
  ((1, 2), (2, 0))
]

/-
♞, ♞, ♘, ♘
-/

#eval starting_position.pieces

/-
(some 0), none, (some 1);
none, none, none;
(some 2), none, (some 3)
-/

#eval starting_position.contents

def first_move : chess.move starting_position :=
let pair := guarini_seq 0 in ⟨pair.fst, pair.snd, dec_trivial, dec_trivial, dec_trivial⟩

/-
♞, ♞, ♘, ♘;

♞, ＿, ♞;
＿, ＿, ＿;
♘, ＿, ♘
-/

#eval starting_position
/-
♞, ♞, ♘, ♘;

♞, ♘, ♞;
＿, ＿, ＿;
＿, ＿, ♘
-/

#eval first_move.perform_move

/-
((some 3), none, (some 2);
none, none, none;
(some 1), none, (some 0),
((2, 0), (0, 1)), ((2, 2), (1, 0)), ((0, 1), (2, 2)), ((0, 2), (2, 1)), ((0, 0), (1, 2)), ((1, 2), (2, 0)), ((2, 0), (0, 1)), ((2, 1), (0, 0)), ((0, 0), (1, 2)), ((1, 0), (0, 2)), ((0, 2), (2, 1)), ((2, 2), (1, 0)), ((1, 0), (0, 2)), ((0, 1), (2, 2)), ((2, 1), (0, 0)), ((1, 2), (2, 0)))
-/

def guarini_seq.scan_contents : fin _ → playfield _ _ _ :=
(vector.scanl (λ acc (x : prod _ _), playfield.move_piece acc x.fst x.snd)
  starting_position.contents (vector.of_fn guarini_seq)).nth

example : ∀ ix, (guarini_seq ix).fst ≠ (guarini_seq ix).snd := dec_trivial

def guarini_position : chess.board _ _ _ _ :=
  { contents := guarini_seq.scan_contents (fin.last _),
    pieces := starting_position.pieces }

example : guarini_position ≈ ending_position := dec_trivial

/-  Pseudo-proof of a direct solution
lemma starting_position.exists_move_seq ending_position := begin
  use guarini_seq,
end
-/

-- Graph-equivalence
