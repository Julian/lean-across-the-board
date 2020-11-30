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

lemma nth_take_of_lt {l : list α} {n m : ℕ} (h : m < n) :
  (l.take n).nth m = l.nth m :=
begin
  induction n with n hn generalizing l m,
  { simp only [nat.nat_zero_eq_zero] at h,
    exact absurd h (not_lt_of_le m.zero_le) },
  { cases l with hd tl,
    { simp only [take_nil] },
    { cases m,
      { simp only [nth, take] },
      { simpa only using hn (nat.lt_of_succ_lt_succ h) } } },
end

@[simp] lemma nth_take {l : list α} {n : ℕ} :
  (l.take (n + 1)).nth n = l.nth n :=
nth_take_of_lt (nat.lt_succ_self n)

lemma take_succ {l : list α} {n : ℕ} :
  l.take (n + 1) = l.take n ++ (l.nth n).to_list :=
begin
  induction l with hd tl hl generalizing n,
  { simp only [option.to_list, nth, take_nil, append_nil]},
  { cases n,
    { simp only [option.to_list, nth, eq_self_iff_true, and_self, take, nil_append] },
    { simp only [hl, cons_append, nth, eq_self_iff_true, and_self, take] } }
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

lemma join_take (L : list (list α)) (n : ℕ) : (take n L).join = (take n L).foldr (++) [] :=
begin
  induction L with l ls hl generalizing n,
  { simp only [join, foldr, take_nil] },
  { cases n,
    { simp only [join, take, foldr] },
    { simp only [hl, join, take, foldr] } }
end

lemma reduce_option_join (L : list (list (option α))) : L.join.reduce_option = (map reduce_option L).join :=
begin
  induction L with l ls hL,
  { simp only [join, reduce_option_nil, map_nil] },
  { cases l with hd tl,
    { simp only [join, hL, reduce_option_nil, map, nil_append] },
    { cases hd,
      { simp only [hL, join, reduce_option_append, map] },
      { simp only [hL, join, reduce_option_append, map] } } }
end

section prefixs

lemma prefix_take_le_iff (L : list (list (option α))) (m n : ℕ) (hm : m < L.length) :
  (take m L) <+: (take n L) ↔ m ≤ n :=
begin
  simp only [prefix_iff_eq_take, length_take],
  induction m with m IH generalizing L n,
  { simp only [min_eq_left, eq_self_iff_true, zero_le, take] },
  { cases n,
    { simp only [nat.nat_zero_eq_zero, le_zero_iff_eq, take, take_nil],
      split,
      { cases L,
        { simp only [length] at hm,
          exact absurd hm (not_lt_of_le m.succ.zero_le) },
        { simp only [forall_prop_of_false, not_false_iff, take] } },
      { intro h,
        contradiction } },
    { cases L with l ls,
      { simp only [length] at hm,
        exact absurd hm (not_lt_of_le m.succ.zero_le) },
      { simp only [length] at hm,
        specialize IH ls n (nat.lt_of_succ_lt_succ hm),
        simp only [le_of_lt (nat.lt_of_succ_lt_succ hm), min_eq_left] at IH,
        simp only [le_of_lt hm, IH, true_and, min_eq_left, eq_self_iff_true, length, take],
        exact ⟨nat.succ_le_succ, nat.le_of_succ_le_succ⟩ } } },
end

lemma cons_prefix_iff {l l' : list α} (x y : α) :
  x :: l <+: y :: l' ↔ x = y ∧ l <+: l' :=
begin
  split,
  { rintro ⟨L, hL⟩,
    simp only [cons_append] at hL,
    exact ⟨hL.left, ⟨L, hL.right⟩⟩ },
  { rintro ⟨rfl, h⟩,
    rwa [prefix_cons_inj] },
end

lemma map_prefix {l l' : list α} (f : α → β) (h : l <+: l') :
  l.map f <+: l'.map f :=
begin
  induction l with hd tl hl generalizing l',
  { simp only [nil_prefix, map_nil] },
  { cases l' with hd' tl',
    { simpa only using eq_nil_of_prefix_nil h },
    { rw cons_prefix_iff at h,
      simp only [h, prefix_cons_inj, hl, map] } },
end

lemma filter_map_prefix {l l' : list α} (f : α → option β) (h : l <+: l') :
  l.filter_map f <+: l'.filter_map f :=
begin
  induction l with hd tl hl generalizing l',
  { simp only [nil_prefix, filter_map_nil] },
  { cases l' with hd' tl',
    { simpa only using eq_nil_of_prefix_nil h },
    { rw cons_prefix_iff at h,
      rw [←@singleton_append _ hd _, ←@singleton_append _ hd' _, filter_map_append,
         filter_map_append, h.left, prefix_append_right_inj],
      exact hl h.right } },
end

lemma reduce_option_prefix {l l' : list (option α)} (h : l <+: l') :
  l.reduce_option <+: l'.reduce_option :=
filter_map_prefix id h

end prefixs

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
