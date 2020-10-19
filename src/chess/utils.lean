import data.matrix.notation
import data.vector2

/-!

Helpers that don't currently fit elsewhere...

-/

lemma split_eq {m n : Type*} (x : m × n) (p p' : m × n) :
  p = x ∨ p' = x ∨ (x ≠ p ∧ x ≠ p') := by tauto

section scan

variable {n : ℕ}
variables {α β : Type*}
variables (f : β → α → β) (b : β)
variables (v : vector α n) (v' : vector α (n + 1))

def vector.scanl : vector β (n + 1) :=
⟨list.scanl f b v.to_list, by rw [list.length_scanl, vector.to_list_length]⟩

@[simp] lemma vector.scanl_nil : vector.scanl f b vector.nil = b ::ᵥ vector.nil := rfl

lemma vector.scanl_cons (x : α) : vector.scanl f b (x ::ᵥ v) = b ::ᵥ vector.scanl f (f b x) v :=
by simpa only [vector.scanl, vector.to_list_cons]

lemma vector.scanl_val : ∀ {v : vector α n}, (vector.scanl f b v).val = list.scanl f b v.val
| ⟨l, hl⟩ := rfl

lemma vector.to_list_scanl : (vector.scanl f b v).to_list = list.scanl f b v.to_list := rfl

lemma vector.scanl_singleton (v : vector α 1) :
  vector.scanl f b v = b ::ᵥ f b v.head ::ᵥ vector.nil :=
begin
  rw ←vector.cons_head_tail v,
  rw vector.scanl_cons,
  simp only [vector.scanl_nil, vector.cons_head, vector.singleton_tail],
end

@[simp] lemma vector.scanl_head :
  (vector.scanl f b v).head = b :=
begin
  cases n,
  { have : v = vector.nil := by simp only [eq_iff_true_of_subsingleton],
    simp only [this, vector.scanl_nil, vector.cons_head] },
  { rw ←vector.cons_head_tail v,
    simp only [←vector.nth_zero, vector.nth_eq_nth_le, vector.to_list_scanl,
                vector.to_list_cons, list.scanl, fin.val_zero', list.nth_le] }
end

lemma vector.scanl_nth (i : fin n) :
  (vector.scanl f b v).nth i.succ = f ((vector.scanl f b v).nth i.cast_succ) (v.nth i) :=
begin
  rcases n with _|n,
  { exact fin_zero_elim i },
  induction n with n hn generalizing b,
  { have i0 : i = 0 := by simp only [eq_iff_true_of_subsingleton],
    simpa only [vector.scanl_singleton, i0, vector.nth_zero] },
  { rw [←vector.cons_head_tail v, vector.scanl_cons, vector.nth_cons_succ],
    obtain ⟨i, hi⟩ := i,
    cases i,
    { simp only [fin.mk_zero, vector.nth_zero, vector.scanl_head,
                 fin.coe_eq_cast_succ, fin.cast_succ_zero, vector.cons_head] },
    { have : fin.succ ⟨i, nat.lt_of_succ_lt_succ hi⟩ = ⟨i.succ, hi⟩ := rfl,
      simp only [←this, hn, fin.cast_succ_fin_succ, vector.nth_cons_succ] } }
end

end scan

-- For `playfield`s, the piece type and/or piece index type.
variables (X : Type*)
variables [has_repr X]

namespace chess.utils

section repr

/--
An auxiliary wrapper for `option X` that allows for overriding the `has_repr` instance
for `option`, and rather, output just the value in the `some` and a custom provided
`string` for `none`.
-/
structure option_wrapper :=
(val : option X)
(none_s : string)

instance wrapped_option_repr : has_repr (option_wrapper X) :=
⟨λ ⟨val, s⟩, (option.map has_repr.repr val).get_or_else s⟩

variables {X}
/--
Construct an `option_wrapper` term from a provided `option X` and the `string`
that will override the `has_repr.repr` for `none`.
-/
def option_wrap (val : option X) (none_s : string) : option_wrapper X := ⟨val, none_s⟩

-- The size of the "vectors" for a `fin n' → X`, for `has_repr` definitions
variables {m' n' : ℕ}

/--
For a "vector" `X^n'` represented by the type `Π n' : ℕ, fin n' → X`, where
the `X` has a `has_repr` instance itself, we can provide a `has_repr` for the "vector".
This definition is used for displaying rows of the playfield, when it is defined
via a `matrix`, likely through notation.
-/
def vec_repr : Π {n' : ℕ}, (fin n' → X) → string :=
λ _ v, string.intercalate ", " ((vector.of_fn v).to_list.map repr)

instance vec_repr_instance : has_repr (fin n' → X) := ⟨vec_repr⟩

/--
For a `matrix` `X^(m' × n')` where the `X` has a `has_repr` instance itself,
we can provide a `has_repr` for the matrix, using `vec_repr` for each of the rows of the matrix.
This definition is used for displaying the playfield, when it is defined
via a `matrix`, likely through notation.
-/
def matrix_repr : Π {m' n'}, matrix (fin m') (fin n') X → string :=
λ _ _ M, string.intercalate ";\n" ((vector.of_fn M).to_list.map repr)

instance matrix_repr_instance :
  has_repr (matrix (fin n') (fin m') X) := ⟨matrix_repr⟩

end repr

end chess.utils
