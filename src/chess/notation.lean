import data.matrix.notation
import chess.piece
import chess.playfield
import tactic.basic
import data.vector2
import utils.vector.filter
import utils.vector.reduce_some
import utils.matrix.ravel

variables (pf : playfield (fin 3) (fin 3) chess.colored_pieces)
variables (hf : pf = PF ![![♞, __, ♞], ![__, __, __], ![♘, __, ♘]])

#eval PF (![![(♞ : option (chess.colored_pieces)), __, ♞], ![__, __, __], ![♘, __, ♘]])

#check list.reduce_option

variables {α : Type*} {n m : ℕ}
variables (l : list α) (v : vector α n)
variables (p : α → Prop) [decidable_pred p]

#eval vector.nth $ vector.reduce_some (vector.of_fn $ matrix.ravel
      (![![(♞ : option (chess.colored_pieces)), __, ♞],
         ![__, __, __],
         ![♘, __, ♘]])) rfl
/-
♞, ♞, ♘, ♘
-/

/-
vector.map_accumr :
  Π {α : Type u_2} {β : Type u_3} {n : ℕ} {σ : Type},
    (α → σ → σ × β) → vector α n → σ → σ × vector β n
-/

#check @vector.map_accumr

def vector.map_accuml {α β : Type*} {n : ℕ} {σ : Type}
  (f : α → σ → σ × β) (v : vector α n) (s : σ) : σ × vector β n :=
prod.map id vector.reverse (vector.map_accumr f v.reverse s)

lemma list.length_cons_tail {x : α} {l : list α} (h : (x :: l).length = n + 1) : l.length = n :=
by { simpa only [add_left_inj, list.length] using h }

#check fin.has_zero

example {m n : ℕ} : m < m + (n + 1) :=
begin
  simp,
end

#check fin.cast_add


#eval vector.nth $ vector.enumerate_from 5 $
  (vector.of_fn (![some 1, some 2, some 6, none, some 10]))
/-
(5, (some 1)), (6, (some 2)), (7, (some 6)), (8, none), (9, (some 10))
-/


#eval vector.nth $ vector.enumerate $ vector.of_fn $
  (![![(♞ : option (chess.colored_pieces)), __, ♞], ![__, __, __], ![♘, __, ♘]])
