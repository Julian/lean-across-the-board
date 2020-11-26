import data.list
import utils.option

open list

namespace list

variables {α β γ : Type*}

lemma nth_append_right {l₁ l₂ : list α} {n : ℕ} (hn : l₁.length ≤ n) :
  (l₁ ++ l₂).nth n = l₂.nth (n - l₁.length) :=
begin
  by_cases hl : (n < (l₁ ++ l₂).length),
  { rw [nth_le_nth hl, nth_le_nth, nth_le_append_right hn] },
  { rw [nth_len_le (le_of_not_lt hl), nth_len_le],
    rw [not_lt, length_append] at hl,
    exact nat.le_sub_left_of_add_le hl },
end

@[simp] lemma reduce_option_cons_of_some (x : α) (l : list (option α)) :
  reduce_option (some x :: l) = x :: l.reduce_option :=
by simp only [reduce_option, filter_map, id.def, eq_self_iff_true, and_self]

@[simp] lemma reduce_option_cons_of_none (l : list (option α)) :
  reduce_option (none :: l) = l.reduce_option :=
by simp only [reduce_option, filter_map, id.def]

lemma filter_map_append {α β : Type*} (l l' : list α) (f : α → option β) :
  filter_map f (l ++ l') = filter_map f l ++ filter_map f l' :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { rw [cons_append, filter_map, filter_map],
    cases f hd;
    simp only [filter_map, hl, cons_append, eq_self_iff_true, and_self] }
end

@[simp] lemma reduce_option_nil : @reduce_option α [] = [] := rfl

@[simp] lemma reduce_option_map {l : list (option α)} {f : α → β} :
  reduce_option (map (option.map f) l) = map f (reduce_option l) :=
begin
  induction l with hd tl hl,
  { simp only [reduce_option_nil, map_nil] },
  { cases hd;
    simpa only [true_and, option.map_some', map, eq_self_iff_true,
                reduce_option_cons_of_some] using hl },
end

lemma reduce_option_append (l l' : list (option α)) :
  (l ++ l').reduce_option = l.reduce_option ++ l'.reduce_option :=
filter_map_append l l' id

lemma reduce_option_length_le (l : list (option α)) :
  l.reduce_option.length ≤ l.length :=
begin
  induction l with hd tl hl,
  { simp only [reduce_option_nil, length] },
  { cases hd,
    { exact nat.le_succ_of_le hl },
    { simpa only [length, add_le_add_iff_right, reduce_option_cons_of_some] using hl} }
end

lemma reduce_option_forall_iff {l : list (option α)} :
  l.reduce_option.length = l.length ↔ ∀ x ∈ l, option.is_some x :=
begin
  induction l with hd tl hl,
  { simp only [forall_const, reduce_option_nil, not_mem_nil,
               forall_prop_of_false, eq_self_iff_true, length, not_false_iff] },
  { cases hd,
    { simp only [mem_cons_iff, forall_eq_or_imp, bool.coe_sort_ff, false_and,
                 reduce_option_cons_of_none, length, option.is_some_none, iff_false],
      intro H,
      have := reduce_option_length_le tl,
      rw H at this,
      exact absurd (nat.lt_succ_self _) (not_lt_of_le this) },
    { simp only [hl, true_and, mem_cons_iff, forall_eq_or_imp, add_left_inj,
                 bool.coe_sort_tt, length, option.is_some_some, reduce_option_cons_of_some] } }
end

lemma reduce_option_exists_iff {l : list (option α)} :
  l.reduce_option.length < l.length ↔ ∃ x ∈ l, x = none :=
begin
  induction l with hd tl hl,
  { simp only [reduce_option_nil, not_mem_nil, length, not_false_iff, not_lt,
               exists_false, exists_prop_of_false, iff_false] },
  { cases hd,
    { simp only [mem_cons_iff, reduce_option_cons_of_none, length, exists_prop,
                 true_or, eq_self_iff_true, exists_eq_right, iff_true],
      have := reduce_option_length_le tl,
      exact lt_of_le_of_lt this (nat.lt_succ_self _) },
    { simp only [hl, mem_cons_iff, length, reduce_option_cons_of_some,
                 exists_prop, false_or, exists_eq_right, add_lt_add_iff_right] } }
end

lemma to_list_eq_reduce_option (x : option α) :
  x.to_list = [x].reduce_option :=
by { cases x; refl }

lemma reduce_option_concat (l : list (option α)) (x : option α) :
  (l.concat x).reduce_option = l.reduce_option ++ x.to_list :=
begin
  induction l with hd tl hl generalizing x,
  { cases x;
    simp [option.to_list] },
  { simp only [concat_eq_append, reduce_option_append] at hl,
    cases hd;
    simp [hl, reduce_option_append] }
end

lemma reduce_option_concat_of_some (l : list (option α)) (x : α) :
  (l.concat (some x)).reduce_option = l.reduce_option.concat x :=
by simp only [reduce_option_nil, concat_eq_append, reduce_option_append, reduce_option_cons_of_some]

lemma reduce_option_mem_iff {l : list (option α)} {x : α} :
  (some x) ∈ l ↔ x ∈ l.reduce_option :=
begin
  induction l with hd tl hl,
  { simp only [reduce_option_nil, not_mem_nil] },
  { simp only [hl, mem_cons_iff],
    split,
    { rintro (rfl | H),
      { simp only [mem_cons_iff, true_or, eq_self_iff_true, reduce_option_cons_of_some] },
      { cases hd;
        simp only [H, mem_cons_iff, or_true, reduce_option_cons_of_some, reduce_option_cons_of_none] } },
    { intro H,
      cases hd,
      { simpa only [false_or] using H },
      { simpa only using H } } },
end

lemma reduce_option_nth_iff {l : list (option α)} {x : α} :
  (∃ i, l.nth i = some (some x)) ↔ ∃ i, l.reduce_option.nth i = some x :=
by rw [←mem_iff_nth, ←mem_iff_nth, reduce_option_mem_iff]

lemma some_injective_of_reduce_option_injective {l : list (option α)}
  (h : ∀ ⦃x⦄, x < l.reduce_option.length → ∀ ⦃y⦄, l.reduce_option.nth x = l.reduce_option.nth y → x = y) :
  ∀ ⦃a₁⦄, l.nth a₁ >>= id ≠ none → ∀ ⦃a₂⦄, l.nth a₁ = l.nth a₂ → a₁ = a₂ :=
begin
  intros x hx y,
  contrapose!,
  intros hne H,
  simp at hx,
  obtain ⟨z, hx⟩ := hx,
  have hy : l.nth y = some (some z),
    { rw [←H, ←hx] },
  have hx' := exists.intro x hx,
  have hy' := exists.intro y hy,
  rw reduce_option_nth_iff at hx' hy',
  obtain ⟨i, hi⟩ := hx',
  obtain ⟨j, hj⟩ := hy',
  rw list.nth_eq_some at hi,
  obtain ⟨hli, hi⟩ := hi,
  obtain ⟨hlx, hx'⟩ := hz,
  obtain ⟨hly, hy'⟩ := hy',
  rw ←hy' at hx',
  simp at h,
  apply h,
end

@[simp] lemma map_id'' : map (@id α) = id :=
funext is_lawful_functor.id_map

lemma nth_pmap {p : α → Prop} (f : Π a, p a → β) (l : list α) (h : ∀ a ∈ l, p a) (n : ℕ) :
  nth (pmap f l h) n = option.pmap f (nth l n) (λ x H, h x (nth_mem H)) :=
begin
  induction l with hd tl hl generalizing n,
  { simp only [nth, pmap, option.pmap_none] },
  { cases n,
    { simp only [nth, pmap, option.pmap] },
    { simp only [hl, nth, pmap] } }
end

lemma nth_le_pmap {p : α → Prop} (f : Π a, p a → β) (l : list α) (h : ∀ a ∈ l, p a) (n : ℕ)
  (hn : n < (pmap f l h).length):
  nth_le (pmap f l h) n hn =
    f (nth_le l n (@length_pmap _ _ p f l h ▸ hn)) (h _ (nth_le_mem l n (@length_pmap _ _ p f l h ▸ hn))) :=
begin
  induction l with hd tl hl generalizing n,
  { simp only [length, pmap] at hn,
    exact absurd hn (not_lt_of_le n.zero_le) },
  { cases n,
    { simp only [pmap, nth_le] },
    { simpa only [hl, pmap, nth_le] } }
end

end list

section semigroup

variables {α : Type*} (f : α → α → α) [is_associative α f] {x y : α} [semigroup α]

@[simp] lemma comp_assoc_left : (f x) ∘ (f y) = (f (f x y)) :=
by { ext z, rw [function.comp_apply, @is_associative.assoc _ f _ x y z], }

/--
Composing two multiplications on the left by `x` and `y`
is equal to a multiplication on the left by `x * y`.
-/
@[simp] lemma comp_semigroup_left [semigroup α] {x y : α} : ((*) x) ∘ ((*) y) = ((*) (x * y)) :=
by simp only [comp_assoc_left]

/--
Composing two additions on the left by `x` and `y`
is equal to a addition on the left by `x + y`.
-/
@[simp] lemma comp_add_semigroup_left [add_semigroup α] {x y : α} : ((+) x) ∘ ((+) y) = ((+) (x + y)) :=
by simp

/--
Composing two multiplications on the right by `x` and `y`
is equal to a multiplication on the right by `y * w`.
-/
@[simp] lemma comp_semigroup_right [semigroup α] {x y : α} : (* x) ∘ (* y) = (* (y * x)) :=
by { ext z, rw [function.comp_app, mul_assoc] }

/--
Composing two multiplications on the right by `x` and `y`
is equal to a multiplication on the right by `y + w`.
-/
@[simp] lemma comp_add_semigroup_right [add_semigroup α] {x y : α} : (+ x) ∘ (+ y) = (+ (y + x)) :=
by { ext z, rw [function.comp_app, add_assoc] }

end semigroup
