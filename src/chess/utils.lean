import data.vector2

/-!

Helpers that don't currently fit elsewhere...

-/

section scan

variable {n : ℕ}
variables {α β : Type*}
variables (f : β → α → β) (b : β)
variables (v : vector α n) (v' : vector α (n + 1))

def vector.scanl : vector β (n + 1) :=
⟨list.scanl f b v.to_list, by rw [list.length_scanl, vector.to_list_length]⟩

@[simp] lemma vector.scanl_nil : vector.scanl f b vector.nil = b :: vector.nil := rfl

lemma vector.scanl_cons (x : α) : vector.scanl f b (x :: v) = b :: vector.scanl f (f b x) v :=
by simpa only [vector.scanl, vector.to_list_cons]

lemma vector.scanl_val : ∀ {v : vector α n}, (vector.scanl f b v).val = list.scanl f b v.val
| ⟨l, hl⟩ := rfl

def vector.last : α := v'.nth (fin.last n)

lemma vector.last_def : v'.last = v'.nth (fin.last n) := rfl

lemma vector.to_list_reverse : v.reverse.to_list = v.to_list.reverse := rfl

lemma vector.reverse_nth_zero : v'.reverse.head = v'.last :=
begin
  have : 0 = v'.to_list.length - 1 - n,
    { simp only [nat.add_succ_sub_one, add_zero, vector.to_list_length, nat.sub_self,
                 list.length_reverse] },
  rw [←vector.nth_zero, vector.last_def, vector.nth_eq_nth_le, vector.nth_eq_nth_le],
  simp_rw [vector.to_list_reverse, fin.val_eq_coe, fin.coe_last, fin.coe_zero, this],
  rw list.nth_le_reverse,
end

@[simp] lemma vector.tail_nil : (@vector.nil α).tail = vector.nil := rfl

@[simp] lemma vector.singleton_tail (v : vector α 1) : v.tail = vector.nil :=
by simp only [←vector.cons_head_tail, eq_iff_true_of_subsingleton]

lemma vector.to_list_scanl : (vector.scanl f b v).to_list = list.scanl f b v.to_list := rfl

@[simp] lemma vector.to_list_singleton (v : vector α 1) : v.to_list = [v.head] :=
begin
  rw ←vector.cons_head_tail v,
  simp only [vector.to_list_cons, vector.to_list_nil, vector.cons_head, eq_self_iff_true,
             and_self, vector.singleton_tail]
end

lemma vector.scanl_singleton (v : vector α 1) :
  vector.scanl f b v = b :: f b v.head :: vector.nil :=
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

@[elab_as_eliminator] protected lemma fin.induction_on
  {n : ℕ}
  {P : fin (n + 1) → Prop}
  (i : fin (n + 1))
  (h0 : P 0)
  (hs : ∀ i : fin n, P i.cast_succ → P i.succ) : P i :=
begin
  obtain ⟨i, hi⟩ := i,
  induction i with i IH,
  { rwa [fin.mk_zero] },
  { have : fin.succ ⟨i, nat.lt_of_succ_lt_succ hi⟩ = ⟨i.succ, hi⟩ := rfl,
    rw ←this,
    apply hs,
    apply IH }
end

@[elab_as_eliminator] protected lemma vector.scanl.induction_on
  {α β : Type*} {n : ℕ}
  {P : β → Prop}
  (v : vector α n)
  {f : β → α → β}
  {b : β}
  (h_b: P b)
  (h_ih: ∀ {y : β} {x : α}, P y → P (f y x))
  {ix : fin (n + 1)} : P ((vector.scanl f b v).nth ix) :=
begin
  apply ix.induction_on,
  { simp only [h_b, fin.mk_zero, vector.nth_zero, vector.scanl_head] },
  { intros i h,
    rw [vector.scanl_nth],
    exact h_ih h }
end

end scan

-- For `playfield`s, the piece type.
variables (K : Type*)
variables [has_repr K]

namespace chess.utils

/--
An auxiliary wrapper for `option K` that allows for overriding the `has_repr` instance
for `option`, and rather, output just the value in the `some` and a custom provided
`string` for `none`.
-/
structure option_wrapper :=
(val : option K)
(none_s : string)

instance wrapped_option_repr : has_repr (option_wrapper K) :=
⟨λ ⟨val, s⟩, (option.map has_repr.repr val).get_or_else s⟩

variables {K}
/--
Construct an `option_wrapper` term from a provided `option K` and the `string`
that will override the `has_repr.repr` for `none`.
-/
def option_wrap (val : option K) (none_s : string) : option_wrapper K := ⟨val, none_s⟩

end chess.utils
