import data.matrix.notation
import chess.piece
import chess.playfield
import tactic.basic
import data.vector2
import .filter

variables (pf : playfield (fin 3) (fin 3) chess.colored_pieces)
variables (hf : pf = PF ![![♞, __, ♞], ![__, __, __], ![♘, __, ♘]])

#eval PF (![![(♞ : option (chess.colored_pieces)), __, ♞], ![__, __, __], ![♘, __, ♘]])

#check list.reduce_option

variables {α : Type*} {n m : ℕ}
variables (l : list α) (v : vector α n)
variables (p : α → Prop) [decidable_pred p]

def pi_extract {α β : Sort*} {C : Sort* → β → Sort*} : Π {b : β}, C α b → β
| b _ := b

section list

def list.filter_length : list α → ℕ
| []     := 0
| (a::l) := if p a then l.filter_length + 1 else l.filter_length

lemma list.filter_length_eq : l.filter_length p = (l.filter p).length :=
begin
  induction l with hd tl IH,
  { simp only [list.filter_length, list.filter_nil, list.length] },
  { simp only [list.filter_length, list.filter, IH, list.length],
    split_ifs;
    refl }
end

end list

def vector.count_some (v : vector (option α) n) : ℕ :=
v.filter_count (λ x, option.is_some x)

lemma vector.count_some_def (v : vector (option α) n) :
  v.count_some = v.filter_count (λ x, option.is_some x) := rfl

def vector.filter_some (v : vector (option α) n) (hm : v.count_some = m) :
  vector (option α) m :=
v.filter (λ x, option.is_some x) hm

lemma vector.filter_some_pred (v : vector (option α) n) (hm : v.count_some = m) :
  ∀ i, ((v.filter_some hm).nth i).is_some :=
vector.filter_valid _ hm

def vector.reduce_some (v : vector (option α) n) (hm : v.count_some = m) :
  vector α m :=
vector.of_fn (λ i, option.get ((v.filter_some_pred hm) i))

#check vector.reduce_some

#eval pi_extract (vector.of_fn (![1, 2, 6, 10]))
#reduce (vector.of_fn (![some 1, some 2, some 6, none, some 10]))
#reduce vector.count_some (vector.of_fn (![some 1, some 2, some 6, none, some 10]))
#reduce vector.filter_some (vector.of_fn (![some 1, some 2, some 6, none, some 10])) _
#reduce vector.reduce_some (vector.of_fn (![some 1, some 2, some 6, none, some 10])) rfl

def matrix.ravel {α : Sort*} : Π {n m : ℕ}, ((fin n) → (fin m) → α) → fin (n * m) → α
| _       0 _ i      := matrix.vec_empty i
| 0       m M ⟨i, h⟩ := matrix.vec_empty ⟨i, nat.zero_mul m ▸ h⟩
| (n + 1) m M i      := fin.append
                          (by rw [nat.succ_mul, add_comm])
                          (matrix.vec_head M) (matrix.ravel (matrix.vec_tail M)) i

#eval vector.last $ vector.scanl list.append [] $ vector.map (λ f, list.reduce_option $ vector.to_list (vector.of_fn f)) $ vector.of_fn (![![(♞ : option (chess.colored_pieces)), __, ♞], ![__, __, __], ![♘, __, ♘]]))
#check fin.append
#eval matrix.ravel (![![(♞ : option (chess.colored_pieces)), __, ♞], ![__, __, __], ![♘, __, ♘]])

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

def vector.enumerate' {α : Type*} {n : ℕ} (v : vector α (n + 1)) :
  vector (fin (n + 1) × α) (n + 1) :=
prod.snd $ vector.map_accuml (λ x i, ((i + 1), (i, x))) v 0

def vector.enumerate {α : Type*} : Π {n : ℕ}, vector α n → vector (fin n × α) n
| 0       _ := vector.nil
| (n + 1) v := vector.enumerate' v

#eval vector.nth $
  (vector.of_fn (![some 1, some 2, some 6, none, some 10]))

#eval vector.nth $ vector.enumerate
  (vector.of_fn (![some 1, some 2, some 6, none, some 10]))
