import utils.list
import utils.option
import tactic.nth_rewrite

open list

namespace list

variables {α : Type*} {l : list (option α)} {x : option α} {n m : ℕ}

def enum_some : list (option α) → list (option ℕ)
| [] := []
| (none :: xs) := none :: (enum_some xs)
| (some x :: xs) := some 0 :: (enum_some xs).map (option.map (+ 1))

@[simp] lemma enum_some_nil : @enum_some α []  = [] := rfl

@[simp] lemma enum_some_cons_none (l : list (option α)) :
  enum_some (none :: l) = none :: enum_some l := rfl

@[simp] lemma enum_some_cons_some (x : α) (l : list (option α)) :
  enum_some (some x :: l) = some 0 :: l.enum_some.map (option.map nat.succ) := rfl

@[simp] lemma length_enum_some {l : list (option α)} : (enum_some l).length = l.length :=
begin
  induction l with hd tl hl,
  { simp only [enum_some_nil, length] },
  { cases hd,
    { simp only [hl, enum_some_cons_none, length] },
    { simp only [hl, length, length_map, enum_some_cons_some, map_eq_map] } }
end

lemma enum_some_reduce_option_eq_range (l : list (option α)) :
  l.enum_some.reduce_option = range (l.reduce_option.length) :=
begin
  induction l with hd tl hl,
  { simp only [range, range_core, enum_some_nil, reduce_option_nil, length] },
  { cases hd,
    { simpa only using hl },
    { simp only [hl, true_and, eq_self_iff_true, length, reduce_option_cons_of_some,
                 range_succ_eq_map, reduce_option_map, enum_some_cons_some] } },
end

lemma enum_some_lt (l : list (option α)) {x : ℕ} (h : some x ∈ l.enum_some) :
  x < l.reduce_option.length :=
by rwa [reduce_option_mem_iff, enum_some_reduce_option_eq_range, mem_range] at h

lemma enum_some_lt' (l : list (option α)) :
  ∀ (x ∈ l.enum_some) (a ∈ x), a < l.reduce_option.length :=
λ x hx a ha, enum_some_lt l (option.mem_def.mp ha ▸ hx)

lemma enum_some_exists_of_lt {i : ℕ} (l : list (option α)) (h : i < l.reduce_option.length) :
  ∃ k, l.enum_some.nth k = some (some i) :=
begin
  induction l with hd tl hl generalizing i,
  { simp only [reduce_option_nil, length] at h,
    exact absurd h (not_lt_of_le i.zero_le) },
  { cases hd,
    { rw [reduce_option_cons_of_none] at h,
      obtain ⟨k, hk⟩ := hl h,
      exact ⟨k + 1, hk⟩ },
    { cases i,
      { exact ⟨0, rfl⟩ },
      { simp only [length, reduce_option_cons_of_some] at h,
        obtain ⟨k, hk⟩ := hl (nat.lt_of_succ_lt_succ h),
        use k + 1,
        simp only [nth, enum_some_cons_some, nth_map, hk, option.map_some'] } } },
end

lemma enum_some_mem_of_lt {i : ℕ} (l : list (option α)) (h : i < l.reduce_option.length) :
  some i ∈ l.enum_some :=
mem_iff_nth.mpr (enum_some_exists_of_lt l h)

lemma enum_some_bind_reduce_option {α : Type*} (l : list (option α)) :
  (enum_some l).map (>>= l.reduce_option.nth) = l :=
begin
  induction l with hd tl hl,
  { simp only [enum_some_nil, map] },
  { cases hd,
    { simp [hl] },
    { have : ∀ (m : α) (ms : list (option α)),
        (λ (k : option ℕ), k >>= (m :: ms.reduce_option).nth) ∘ option.map (+ 1) =
        λ (k : option ℕ), k >>= ms.reduce_option.nth,
        { intros, funext k, cases k; simp },
      simp [hl, this] } }
end

lemma enum_some_sorted {α : Type*} (l : list (option α)) :
  sorted (<) l.enum_some.reduce_option :=
begin
  induction l with hd tl hl,
  { simp only [enum_some_nil, reduce_option_nil, sorted_nil] },
  { cases hd,
    { simpa only using hl },
    { refine sorted_cons.mpr ⟨_, _⟩,
      { simp only [and_imp, id.def, mem_filter_map, exists_exists_and_eq_and, mem_map,
                   exists_imp_distrib, option.map_eq_some'],
        rintros b - - x - rfl,
        exact nat.succ_pos' },
      { simpa only [sorted, reduce_option, pairwise_filter_map, pairwise_map, and_imp,
                    forall_apply_eq_imp_iff₂, add_lt_add_iff_right, exists_imp_distrib,
                    option.map_eq_some', id.def, option.mem_def] using hl } } },
end

lemma enum_some_some_injective {l : list (option α)} :
  ∀ ⦃a₁⦄, (l.enum_some.nth a₁).join ≠ none → ∀ ⦃a₂⦄, l.enum_some.nth a₁ = l.enum_some.nth a₂ → a₁ = a₂ :=
begin
  induction l with hd tl hl,
  { simp only [enum_some_nil, forall_const, forall_prop_of_false, nth, eq_self_iff_true, not_true,
               ne.def, not_false_iff, option.join] },
  { rintro (_ | x) hx y h,
    { cases hd,
      { simpa using hx },
      { cases y,
        { refl },
        { have h' := h.symm,
          simp only [nth, enum_some_cons_some, nth_map, option.map_eq_some'] at h',
          obtain ⟨-, -, w, -, hw⟩ := h',
          contradiction } } },
    { cases y,
      { cases hd,
        { simp only [exists_prop, nth, id.def, enum_some_cons_none, not_not, exists_eq_right,
                     option.bind_eq_none, ne.def, option.mem_def, not_forall] at h hx,
          rw h at hx,
          simpa only [exists_false] using hx },
        { simp only [nth, enum_some_cons_some, nth_map, option.map_eq_some'] at h,
          obtain ⟨-, -, w, -, hw⟩ := h,
          contradiction } },
      { cases hd,
        { simp only [nth, enum_some_cons_none] at h,
          simp only [nth, id.def, enum_some_cons_none, not_not, exists_eq_right,
                     option.mem_def, not_forall] at hx,
          simp only,
          exact hl hx h },
        { simp only [nth, enum_some_cons_some, nth_map] at h,
          have : function.injective (λ x, option.map (option.map nat.succ) x),
            { apply option.map_injective,
              apply option.map_injective,
              exact nat.succ_injective },
          replace this := this h,
          simp only [option.map_eq_none_iff, nth, enum_some_cons_some, nth_map, ne.def,
                     option.join_map_eq_map_join] at hx,
          simp only,
          refine hl _ this,
          simpa only [option.bind_id_eq_join] using hx } } } }
end

lemma enum_some_exists_unique {α : Type*} (l : list (option α)) {n : ℕ} (h : n < l.reduce_option.length) :
  ∃! (i : ℕ), l.enum_some.nth i = some (some n) :=
begin
  obtain ⟨i, hi⟩ := enum_some_exists_of_lt l h,
  refine ⟨i, hi, _⟩,
  intro y,
  contrapose!,
  intros hne hy,
  apply hne,
  apply enum_some_some_injective,
  { rw hy,
    simp only [option.join, ne.def, not_false_iff] },
  { rw [hy, hi] },
end

lemma take_enum_some : take n l.enum_some = (l.take n).enum_some :=
begin
  induction l with hd tl hl generalizing n,
  { simp only [enum_some_nil, take_nil] },
  { cases n,
    { simp only [enum_some_nil, take] },
    { cases hd,
      { simp only [hl, enum_some_cons_none, eq_self_iff_true, and_self, take] },
      { simp only [←hl, map_take, eq_self_iff_true, enum_some_cons_some, and_self, take] } } },
end

@[simp] def enum_some_fin (l : list (option α)) : (list (option (fin l.reduce_option.length))) :=
(pmap (option.pmap fin.mk)) l.enum_some l.enum_some_lt'

@[simp] lemma enum_some_fin_map_subtype_eq_enum_some (l : list (option α)) :
  l.enum_some_fin.map (option.map subtype.val) = l.enum_some :=
begin
  simpa only [map_pmap, option.map_pmap, pmap_eq_map, option.map_id'', id.def, enum_some_fin,
              fin.mk_eq_subtype_mk, option.pmap_eq_map] using list.map_id _,
end

lemma enum_some_fin_exists_unique {α : Type*} (l : list (option α)) (n : fin (l.reduce_option.length)) :
  ∃! (i : ℕ), l.enum_some_fin.nth i = some (some n) :=
begin
  obtain ⟨i, hi, hi'⟩ := enum_some_exists_unique l n.is_lt,
  use i,
  split,
  { simp only [hi, nth_pmap, enum_some_fin, fin.mk_eq_subtype_mk, option.pmap, fin.eta] },
  { intros y hy,
    simp only [nth_pmap, enum_some_fin, fin.mk_eq_subtype_mk, option.pmap_eq_some_iff] at hy,
    apply hi',
    obtain ⟨x, hx, z, rfl, rfl⟩ := hy,
    simp [hx] },
end

lemma enum_some_fin_some_injective {l : list (option α)} :
  ∀ ⦃a₁⦄, (l.enum_some_fin.nth a₁).join ≠ none → ∀ ⦃a₂⦄, l.enum_some_fin.nth a₁ = l.enum_some_fin.nth a₂ → a₁ = a₂ :=
begin
  intros x hx y hy,
  simp only [nth_pmap, option.pmap_eq_none_iff, enum_some_fin, option.join_ne_none',
             ne.def, option.join_pmap_eq_pmap_join] at hx,
  obtain ⟨i, hi⟩ := hx,
  simp only [nth_pmap, hi, enum_some_fin, fin.mk_eq_subtype_mk, option.pmap] at hy,
  have hy' := hy.symm,
  simp at hy',
  apply enum_some_some_injective,
  { rw hi,
    simp only [option.join, ne.def, not_false_iff] },
  { rw [hi, hy'] }
end

lemma enum_some_fin_map_reduce_option (l : list (option α)) :
  (enum_some_fin l).map (option.map (λ x, l.reduce_option.nth_le x x.is_lt)) = l :=
begin
  induction l with hd tl hl,
  { simp only [enum_some_nil, enum_some_fin, pmap, map_nil]},
  { nth_rewrite_rhs 0 ←hl,
    simp only [enum_some_fin],
    cases hd,
    { change (none :: tl).reduce_option with tl.reduce_option,
      simp only [enum_some_cons_none, map, eq_self_iff_true, pmap,
                 option.pmap, and_self, option.map_none'] },
    { change (some hd :: tl).reduce_option.length with tl.reduce_option.length + 1,
      simp only [pmap_map, map_pmap, nat.succ_pos', option.pmap_some, fin.mk_zero, map, length,
                 enum_some_cons_some, pmap, fin.mk_eq_subtype_mk, option.pmap,
                 reduce_option_cons_of_some, option.map_eq_some', fin.coe_zero, nth_le],
      split,
      { use 0,
        simp, },
      { refine pmap_congr _ _,
        rintro (_ | x) hx hx',
        { simp only [option.pmap, option.map_none'] },
        { simpa only } } } }
end

lemma reduce_option_all_none : l.reduce_option.length = 0 ↔ ∀ k ∈ l, k = none :=
begin
  induction l with hd tl hl,
  { simp only [forall_const, reduce_option_nil, not_mem_nil, forall_prop_of_false,
               eq_self_iff_true, length, not_false_iff] },
  { cases hd,
    { simp only [hl, true_and, mem_cons_iff, forall_eq_or_imp,
                 reduce_option_cons_of_none, eq_self_iff_true] },
    { simp only [mem_cons_iff, forall_eq_or_imp, length, add_eq_zero_iff, one_ne_zero,
                 reduce_option_cons_of_some, and_false, false_and] } }
end

lemma enum_some_exists :
  (∃ (k : ℕ), some k ∈ l.enum_some) ↔ ∃ (x : α), some x ∈ l :=
begin
  induction l with hd tl hl,
  { simp only [enum_some_nil, not_mem_nil, exists_false, exists_const] },
  { cases hd,
    { simp only [hl, mem_cons_iff, false_or, enum_some_cons_none] },
    { split,
      { intro,
        use hd,
        simp only [mem_cons_iff, true_or, eq_self_iff_true] },
      { intro,
        use 0,
        simp only [mem_cons_iff, enum_some_cons_some, true_or, eq_self_iff_true] } } }
end

def enum_2d_some : list (list (option α)) → list (list (option ℕ))
| [] := []
| (l :: ls) := l.enum_some :: (enum_2d_some ls).map (map (option.map (+ l.reduce_option.length)))

@[simp] lemma enum_2d_some_nil : @enum_2d_some α [] = [] := rfl

@[simp] lemma enum_2d_some_cons (l : list (option α)) (ls : list (list (option α))) :
  enum_2d_some (l :: ls) = enum_some l :: (enum_2d_some ls).map (map (option.map (+ l.reduce_option.length))) :=
rfl

@[simp] lemma enum_2d_some_nth0 (l : list (list (option α))) :
  l.enum_2d_some.nth 0 = option.map enum_some (l.nth 0) :=
begin
  induction l with l ls hl,
  { simp only [nth, enum_2d_some_nil, option.map_none'] },
  { simp only [option.map_some', nth, enum_2d_some_cons] }
end

lemma enum_some_bind_reduce_option_append {α : Type*} (l ls : list (option α)) :
  (enum_some l).map (>>= (l ++ ls).reduce_option.nth) = l :=
begin
  induction l with hd tl hl,
  { simp only [enum_some_nil, map] },
  { cases hd,
    { simp only [hl, cons_append, enum_some_cons_none, eq_self_iff_true,
                 and_self, reduce_option_cons_of_none, map, option.none_bind] },
    { have : (λ (x : option ℕ), x >>= (hd :: (tl ++ ls).reduce_option).nth) ∘ option.map nat.succ
        = (>>= (tl ++ ls).reduce_option.nth),
        { funext i,
          cases i,
          { simp only [function.comp_app, option.map_none', option.none_bind]},
          { simp only [option.some_bind, option.map_some', function.comp_app, nth] } },
      simp only [this, hl, reduce_option_cons_of_some, option.some_bind, cons_append,
                 eq_self_iff_true, nth, enum_some_cons_some, and_self, map_map, map, map_eq_map] } }
end

lemma enum_2d_some_bind_reduce_option {α : Type*} (L : list (list (option α))) :
  (enum_2d_some L).map (map (>>= L.join.reduce_option.nth)) = L :=
begin
  induction L with l ls hL,
  { simp only [enum_2d_some_nil, map] },
  { cases l with hd tl,
    { have : @option.map ℕ _ (λ x, x) = id,
      { funext x, cases x; simp },
      simp [this, hL] },
    { cases hd,
      { have : ((λ (_x : option ℕ), _x >>= (tl ++ ls.join).reduce_option.nth) ∘
                 option.map (+ tl.reduce_option.length)) =
                (>>= ls.join.reduce_option.nth),
          { funext i,
            cases i,
            { simp only [function.comp_app, option.map_none', option.none_bind] },
            { simp only [option.some_bind, option.map_some', function.comp_app,
                         reduce_option_append, nth_append_right (nat.le_add_left _ i),
                         nat.add_sub_cancel] } },
        simp [enum_some_bind_reduce_option_append, this, hL] },
      { have h : ∀ (m : α) (ms : list (option α)),
          (λ (k : option ℕ), k >>= (m :: ms.reduce_option).nth) ∘ option.map (+ 1) =
            λ (k : option ℕ), k >>= ms.reduce_option.nth,
          { intros, funext k, cases k; simp },
        have : ((λ (_x : option ℕ), _x >>= (hd :: (tl ++ ls.join).reduce_option).nth) ∘
                 option.map (+ (tl.reduce_option.length + 1))) =
                (>>= ls.join.reduce_option.nth),
          { funext i,
            cases i,
            { simp only [function.comp_app, option.map_none', option.none_bind] },
            { rw [reduce_option_append, ←cons_append, ←reduce_option_cons_of_some],
              simp only [option.some_bind, option.map_some', function.comp_app,
                         reduce_option_cons_of_some, nth_append_right, nat.add_sub_cancel,
                         length, zero_le, le_add_iff_nonneg_left] } },
        simp [h, this, enum_some_bind_reduce_option_append, hL] } } }
end

lemma enum_2d_some_lt (L : list (list (option α))) :
  ∀ (l ∈ L.enum_2d_some) (x ∈ l) (a ∈ x), a < L.join.reduce_option.length :=
begin
  induction L with hd tl hl,
  { simp only [forall_const, not_mem_nil, forall_prop_of_false, enum_2d_some_nil, not_false_iff] },
  { simp only [reduce_option_append, and_imp, mem_cons_iff, join,
               forall_eq_or_imp, mem_map, enum_2d_some_cons, option.mem_def,
               exists_imp_distrib, length_append],
    split,
    { rintros x hx a rfl,
      exact nat.lt_add_right a _ _ (enum_some_lt' _ (some a) hx _ rfl) },
    { rintros x m hm hx _ ha a rfl,
      rw ←hx at ha,
      simp only [mem_map, option.map_eq_some'] at ha,
      obtain ⟨_, hk, k, rfl, rfl⟩ := ha,
      rw [add_comm, add_lt_add_iff_left],
      exact hl _ hm (some _) hk _ rfl } }
end

@[simp] lemma length_enum_2d_some (l : list (list (option α))) : (enum_2d_some l).length = l.length :=
begin
  induction l with hd tl hl,
  { simp only [length, enum_2d_some_nil]},
  { cases hd,
    { simp only [hl, length, enum_2d_some_cons, length_map] },
    { simp only [hl, length, length_map, enum_2d_some_cons] } }
end

lemma length_enum_2d_some_nth {l : list (list (option α))} {lx : list (option ℕ)}
  (h : lx ∈ l.enum_2d_some) :
  lx.length ≤ list.foldr max 0 (list.map list.length l) :=
begin
  induction l with l ls hl generalizing lx h,
  { simpa only [not_mem_nil, enum_2d_some_nil] using h },
  { cases l with hd tl,
    { simp only [mem_cons_iff, map_id'', add_zero, enum_some_nil, option.map_id'',
                 reduce_option_nil, id.def, length, enum_2d_some_cons] at h,
      cases h,
      { simp only [h, length, zero_le] },
      { simpa only [max_eq_right, map, length, zero_le, foldr] using hl h } },
    { simp only [mem_cons_iff, mem_map, enum_2d_some_cons] at h,
      rcases h with (rfl | ⟨lx', h, rfl⟩),
      { simpa only [length_enum_some, le_max_iff, foldr, foldr_map] using or.inl (le_refl _) },
      { simpa only [le_max_iff, foldr, length_map, foldr_map] using or.inr (hl h) } } }
end

lemma nth_enum_2d_some {l : list (list (option α))}
  (h : n < l.length) :
  l.enum_2d_some.nth n = (l.nth n).map (λ l', list.map (option.map (+ (l.take n).join.reduce_option.length)) l'.enum_some) :=
begin
  induction n with n hn generalizing l,
  { simp only [map_id'', add_zero, join, option.map_id'', reduce_option_nil, id.def, length, enum_2d_some_nth0, take] },
  { cases l with l ls,
    { simp only [nth, enum_2d_some_nil, option.map_none']},
    { simp only [length] at h,
      specialize hn (nat.lt_of_succ_lt_succ h),
      ext,
      simp only [join, nth, enum_2d_some_cons, nth_map, take, hn, option.map_map,
                 reduce_option_append, add_comm, option.map_comp_map, function.comp_app,
                 option.mem_def, option.map_eq_some', length_append, comp_add_semigroup_right,
                 map_map] } }
end

lemma take_enum_2d_some {L : list (list (option α))} {n : ℕ} :
  take n L.enum_2d_some = (L.take n).enum_2d_some :=
begin
  induction L with l ls hL generalizing n,
  { simp only [take_nil, enum_2d_some_nil] },
  { cases n,
    { simp only [take, enum_2d_some_nil] },
    { cases l,
      { simp only [hL, eq_self_iff_true, and_self, take, enum_2d_some, map_id'', add_zero,
                   option.map_id'', reduce_option_nil, id.def, length] },
      { simp only [←hL, map_take, eq_self_iff_true, and_self, take, enum_2d_some_cons] } } },
end

lemma enum_2d_some_some_injective {L : list (list (option α))} :
  ∀ x < L.enum_2d_some.length, (∃ z : ℕ, some z ∈ L.enum_2d_some.nth_le x H) →
  ∀ y, L.enum_2d_some.nth x = L.enum_2d_some.nth y → x = y :=
begin
  rintros x hx ⟨z, hz⟩ y h,
  simp [mem_iff_nth] at hz,
  have hy : y < L.enum_2d_some.nth := list.nth_eq_some
  rcases lt_trichotomy x y with H|rfl|H,
  { simp at hx,

    rw [nth_enum_2d_some hx] at h, },
  {  },
  {  },
end

lemma enum_2d_some_some_injective {L : list (list (option α))} :
  ∀ ⦃a₁ b₁⦄, (L.enum_2d_some.nth a₁ >>= λ l, l.nth b₁).join ≠ none →
  ∀ ⦃a₂ b₂⦄, (L.enum_2d_some.nth a₁ >>= λ l, l.nth b₁) = (L.enum_2d_some.nth a₂ >>= λ l, l.nth b₂) →
  a₁ = a₂ ∧ b₁ = b₂ :=
begin
  intros a b hx c d hy,
  simp only [ne.def, option.bind_eq_some, option.join_ne_none'] at hx,
  obtain ⟨ix, lx, hlx, hix⟩ := hx,
  have hy' := hy.symm,
  simp [nth_enum_2d_some, hlx, hix] at hy',
  obtain ⟨ly, hly, hix'⟩ := hy',
  have ha : a < L.length,
    { obtain ⟨H, _⟩ := list.nth_eq_some.mp hlx,
      simpa only [length_enum_2d_some] using H },
  have ha' : ix < (L.take (a + 1)).join.reduce_option.length,
    { apply enum_2d_some_lt _ lx,
      { rw [←take_enum_2d_some, mem_iff_nth],
        use a,
        simp only [nth_enum_2d_some ha, hlx, nth_take, option.map_some'] },
      { rw mem_iff_nth,
        use b,
        simp only [option.map_some', nth_map, hix] },
      { simp only [option.mem_def] }, },
  have hc : c < L.length,
    { obtain ⟨H, _⟩ := list.nth_eq_some.mp hly,
      simpa only [length_enum_2d_some] using H },
  have hc' : ix < (L.take (c + 1)).join.reduce_option.length,
    { apply enum_2d_some_lt _ ly,
      { rw [←take_enum_2d_some, mem_iff_nth],
        use c,
        simp only [nth_enum_2d_some ha, hly, nth_take, option.map_some'] },
      { rw mem_iff_nth,
        use d,
        simp only [option.map_some', nth_map, hix'] },
      { simp only [option.mem_def] }, },
  simp [nth_enum_2d_some, ha, hc] at hlx hly,
  obtain ⟨lx', hlx', rfl⟩ := hlx,
  obtain ⟨ly', hly', rfl⟩ := hly,
  simp at hix hix',
  obtain ⟨lx, hlx, m, hm', hm⟩ := hix,
  obtain ⟨k, hly, n, hn', hn⟩ := hix',
  have hac : a = c,
    { rcases lt_trichotomy a c with hac|rfl|hac,
      { obtain ⟨la, hla⟩ : take a L <+: take c L,
          { rw prefix_take_le_iff _ _ _ ha,
            exact le_of_lt hac },
        rw [←hla, join_append, reduce_option_append, length_append] at hn,
        rw ←hn at ha' hc',
        simp [length_join, take_succ, reduce_option_append, hlx', hly', option.to_list] at hc' ha',
        -- have : (take a L).join.reduce_option.length < (take c L).join.reduce_option.length,
        --   { simp only [reduce_uoption_join, map_map],
        --     apply prefix_len
        --   },
        },
      {  },
      {  },
    },
  apply enum_some_some_injective,
  { rw hi,
    simp only [option.join, ne.def, not_false_iff] },
  { rw [hi, hy'] }
end

@[simp] def enum_2d_some_fin (L : list (list (option α))) : list (list (option (fin L.join.reduce_option.length))) :=
pmap (pmap (option.pmap fin.mk)) L.enum_2d_some L.enum_2d_some_lt

@[simp] lemma enum_2d_some_fin_map_subtype_eq_enum_some (l : list (list (option α))) :
  l.enum_2d_some_fin.map (list.map (option.map subtype.val)) = l.enum_2d_some :=
begin
  simp only [map_pmap, option.map_pmap, pmap_eq_map, option.map_id'', id.def, fin.mk_eq_subtype_mk,
             option.pmap_eq_map, enum_2d_some_fin],
  simp only [map_id', forall_const, eq_self_iff_true],
end

@[simp] lemma length_enum_2d_some_fin (l : list (list (option α)) ) : (enum_2d_some_fin l).length = l.length :=
by simp only [enum_2d_some_fin, length_enum_2d_some, length_pmap]

lemma enum_2d_some_fin_map_reduce_option (L : list (list (option α))) :
  (enum_2d_some_fin L).map (list.map (option.map (λ x, L.join.reduce_option.nth_le x x.is_lt))) = L :=
begin
  induction L with l ls hL,
  { simp only [pmap, map_nil, enum_2d_some_fin, enum_2d_some_nil] },
  { nth_rewrite_rhs 0 ←hL,
    simp only [enum_2d_some_fin],
    cases l with hd tl,
    { change (nil :: ls).join.reduce_option with ls.join.reduce_option,
      have : (λ (_x : ℕ), _x) = id := rfl,
      simp only [map, eq_self_iff_true, pmap, and_self, this, map_id', add_zero, enum_some_nil,
                 forall_const, reduce_option_nil, id.def, option.map_id', length,
                 enum_2d_some_cons] },
    { nth_rewrite_rhs 0 ←enum_some_fin_map_reduce_option tl,
      simp only [pmap_map, map_pmap, cons_append, join, enum_some_fin, map, pmap, enum_2d_some_cons],
      split,
      { cases hd,
        { simp only [reduce_option_append, true_and, enum_some_cons_none,
                     reduce_option_cons_of_none, eq_self_iff_true, pmap, option.pmap,
                     option.map_none'],
          refine pmap_congr _ _,
          rintros (_ | x) hx hx',
          { simp only [option.pmap, option.map_none'] },
          { simp only [option.map_some', fin.mk_eq_subtype_mk, option.pmap, fin.coe_mk],
            rw nth_le_append } },
        { simp only [reduce_option_append, map_pmap, pmap_map, nat.succ_pos', option.pmap_some,
                     cons_append, join, map, length, enum_some_cons_some, pmap, enum_2d_some_cons,
                     fin.mk_eq_subtype_mk, option.pmap, reduce_option_cons_of_some,
                     option.map_eq_some', length_append, nth_le],
          split,
          { use 0,
            { simp only [nat.succ_pos', cons_append, join, length, reduce_option_cons_of_some] },
            { simp only [eq_self_iff_true, and_self, fin.coe_mk, nth_le] } },
          { refine pmap_congr _ _,
            rintros (_ | x) hx hx',
            { simp only [option.pmap, option.map_none'] },
            { simp only [option.map_some', fin.mk_eq_subtype_mk, option.pmap, fin.coe_mk, nth_le],
              rw nth_le_append } } } },
      { refine pmap_congr _ _,
        intros xs hxs hxs',
        refine pmap_congr _ _,
        rintros (_ | x) hx hx',
        { simp only [option.pmap, option.map_none'] },
        { simp only [option.map_some', fin.mk_eq_subtype_mk, option.pmap, fin.coe_mk],
          cases hd;
          { simp only [reduce_option_append, ←add_assoc, length, reduce_option_cons_of_none,
                       reduce_option_cons_of_some, nth_le],
            rw nth_le_append_right,
            swap,
            { exact tl.reduce_option.length.le_add_left x },
            { simp only [nat.add_sub_cancel] } } } } } }
end

lemma enum_2d_some_exists_of_lt {i : ℕ} (l : list (list (option α))) (h : i < l.join.reduce_option.length) :
  ∃ (m n : ℕ), l.enum_2d_some.nth m >>= (λ l', l'.nth n) = some (some i) :=
begin
  induction l with l ls hl generalizing i,
  { simp only [reduce_option_nil, length, join] at h,
    exact absurd h (not_lt_of_le i.zero_le) },
  { rcases lt_or_le i l.reduce_option.length with hlt|hlt,
    { obtain ⟨k, hk⟩ := enum_some_exists_of_lt l hlt,
      use 0,
      simp only [←hk, option.some_bind, nth, enum_2d_some_cons, exists_apply_eq_apply] },
    { simp only [reduce_option_append, join, length_append] at h,
      have hli : i - l.reduce_option.length < ls.join.reduce_option.length,
        { exact (nat.sub_lt_left_iff_lt_add hlt).mpr h },
      obtain ⟨m, n, hn⟩ := hl hli,
      simp only [option.bind_eq_some] at hn,
      obtain ⟨sl, hsl, hsl'⟩ := hn,
      use [m + 1, n],
      simpa only [enum_2d_some_cons, nth, nth_map, hsl, option.map_some',
                  option.some_bind, hsl'] using nat.sub_add_cancel hlt } }
end

lemma enum_2d_some_exists_unique {i : ℕ} (l : list (list (option α))) (h : i < l.join.reduce_option.length) :
  ∃! (m n : ℕ), l.enum_2d_some.nth m >>= (λ l, l.nth n) = some (some i) :=
begin
  obtain ⟨m, n, H⟩ := enum_2d_some_exists_of_lt l h,
  simp only [option.bind_eq_some] at H,
  obtain ⟨lx, hlx, hlx'⟩ := H,
  use m,
  split,
  { use n,
    simp only [hlx, hlx', true_and, option.some_bind, eq_self_iff_true],
    intro y,
    contrapose!,
    intros hne H,
  },
  {  },
end


end list
