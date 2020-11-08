import data.vector2
import data.list.range
import data.matrix.notation
import data.nat.parity
import utils.list
import utils.prod
import utils.vector
import utils.vector.fold
import utils.vector.filter
import utils.vector.pmap

variables {α β : Type*} {n : ℕ}
variables (v : vector α n) (vn : vector α 0)
variables (x : α)

open vector

namespace vector

section range

def range (n : ℕ) : vector ℕ n :=
⟨list.range n, list.length_range n⟩

lemma range_def : range n = ⟨list.range n, list.length_range n⟩ := rfl

@[simp] lemma to_list_range : (range n).to_list = list.range n := rfl

def fin_range (n : ℕ) : vector (fin n) n :=
⟨list.fin_range n, list.length_fin_range n⟩

lemma fin_range_def : fin_range n = ⟨list.fin_range n, list.length_fin_range n⟩ := rfl

@[simp] lemma to_list_fin_range : (fin_range n).to_list = list.fin_range n := rfl

end range

section enum

def enum : vector (fin n × α) n :=
of_fn (λ i, (i, v.nth i))

lemma enum_def : v.enum = of_fn (λ i, (i, v.nth i)) := rfl

lemma to_list_enum : v.enum.to_list = list.of_fn (λ i, (i, v.nth i)) :=
by simp only [enum_def, to_list_of_fn]

lemma to_list_enum_of_zip : v.enum.to_list = list.zip (list.fin_range n) v.to_list :=
begin
  simp_rw [to_list_enum, list.of_fn_eq_map, nth_eq_nth_le, list.map_prod_left_eq_zip],
  congr,
  apply list.ext_le,
  { simp only [list.length_fin_range, list.length_map, to_list_length] },
  { intros i hm h,
    simp only [list.nth_le_fin_range, list.nth_le_map'] },
end

@[simp] lemma enum_nil : vn.enum = nil :=
by simp only [eq_iff_true_of_subsingleton]

@[simp] lemma nth_enum (i : fin n) : v.enum.nth i = (i, v.nth i) :=
by simp only [enum_def, nth_of_fn]

lemma enum_cons_head : (x ::ᵥ v).enum.head = (0, x) :=
begin
  rw [←option.some.inj_eq, ←nth_zero, enum_def, nth_eq_nth_le],
  simp only [fin.val_zero', nth_cons_zero,
              to_list_of_fn, list.nth_le, list.of_fn_succ]
end

@[simp] lemma enum_cons : (x ::ᵥ v).enum = (0, x) ::ᵥ v.enum.map (prod.map fin.succ id) :=
begin
  apply ext,
  apply fin.induction,
  { simp only [fin.coe_zero, nth_cons_zero, nth_enum] },
  { simp only [nth_enum, eq_self_iff_true, nth_map,
               prod.map_mk, forall_true_iff, nth_cons_succ, id.def] }
end

def enum' : vector (ℕ × α) n :=
⟨v.to_list.enum, by rw [list.length_enum, to_list_length]⟩

lemma enum_def' : v.enum' = ⟨v.to_list.enum, by rw [list.length_enum, to_list_length]⟩ := rfl

lemma to_list_enum' : v.enum'.to_list = v.to_list.enum := rfl

lemma to_list_enum_of_zip' : v.enum'.to_list = list.zip (list.range n) v.to_list :=
by simp only [to_list_enum', list.enum_eq_zip_range, to_list_length]

@[simp] lemma enum_map_snd' : v.enum'.map prod.snd = v :=
by { apply vector.eq, simp only [to_list_enum', list.enum_map_snd, to_list_map] }

@[simp] lemma enum_nil' : vn.enum' = nil :=
by simp only [eq_iff_true_of_subsingleton]

lemma enum_cons_head' : (x ::ᵥ v).enum'.head = (0, x) :=
begin
  rw [←option.some.inj_eq, ←nth_zero, enum_def', nth_eq_nth_le],
  simp only [←list.nth_le_nth, option.map_some, list.nth, fin.val_zero',
             to_list_cons, list.enum_nth, to_list_mk]
end

@[simp] lemma nth_enum' (i : fin n) : v.enum'.nth i = (i, v.nth i) :=
begin
  rw [←option.some.inj_eq, nth_eq_nth_le, nth_eq_nth_le, ←list.nth_le_nth,
      to_list_enum', list.enum_nth, list.nth_le_nth],
  simp only [fin.val_eq_coe, option.map_some]
end

@[simp] lemma enum_cons' : (x ::ᵥ v).enum' = (0, x) ::ᵥ v.enum'.map (prod.map nat.succ id) :=
begin
  apply ext,
  apply fin.induction,
  { simp only [fin.coe_zero, nth_cons_zero, nth_enum'] },
  { intros,
    simp only [nth_enum', nth_map, prod.map_mk, nth_cons_succ, id.def, fin.coe_succ] }
end

lemma enum_bdd_below' (i : fin n) : 0 ≤ (v.enum'.nth i).fst :=
by simp only [zero_le]

lemma enum_bdd_above' (i : fin n) : (v.enum'.nth i).fst < n :=
by simpa only [nth_map, nth_enum'] using i.property

lemma enum_eq_pmap_enum' :
  v.enum = vector.pmap v.enum' (λ xpair h, ⟨⟨xpair.fst, h⟩, xpair.snd⟩) v.enum_bdd_above' :=
begin
  cases n,
  { simp only [eq_iff_true_of_subsingleton] },
  { apply ext,
    intro i,
    simp only [nth_enum, nth_pmap_cons, nth_enum', fin.eta] },
end

section enum_from

variable (k : ℕ)

def enum_from : vector (fin (n + k) × α) n :=
of_fn (λ i, (fin.add_nat k i, v.nth i))

lemma enum_from_def : v.enum_from k = of_fn (λ i, (fin.add_nat k i, v.nth i)) := rfl

lemma to_list_enum_from : (v.enum_from k).to_list =
  list.of_fn (λ i, (fin.add_nat k i, v.nth i)) :=
by simp only [enum_from_def, to_list_of_fn]

lemma to_list_enum_from_of_zip : (v.enum_from k).to_list =
  list.zip (list.map (fin.add_nat k) (list.fin_range n)) v.to_list :=
begin
  simp_rw [to_list_enum_from, list.of_fn_eq_map, ←list.zip_map'],
  congr,
  apply list.ext_le,
  { simp only [list.length_fin_range, list.length_map, to_list_length] },
  { intros i hm h,
    simp only [list.nth_le_fin_range, list.nth_le_map', nth_eq_nth_le] },
end

@[simp] lemma nth_enum_from (i : fin n) : (v.enum_from k).nth i =
  (fin.add_nat k i, v.nth i) :=
by simp only [enum_from_def, nth_of_fn]

def enum_from' : vector (ℕ × α) n :=
⟨v.to_list.enum_from k, by rw [list.length_enum_from, to_list_length]⟩

lemma enum_from_def' : v.enum_from' k =
  ⟨v.to_list.enum_from k, by rw [list.length_enum_from, to_list_length]⟩ := rfl

lemma to_list_enum_from' : (v.enum_from' k).to_list = v.to_list.enum_from k := rfl

lemma enum_from_eq_enum_add' : v.enum_from' k = v.enum'.map (prod.map ((+) k) id) :=
begin
  apply vector.eq,
  simp only [to_list_enum_from', to_list_enum', list.enum_from_eq_zip_range',
             list.enum_eq_zip_range, to_list_map, to_list_length,
             ←list.zip_map, list.map_id, list.range'_eq_map_range]
end

@[simp] lemma enum_from_map_snd' : (v.enum_from' k).map prod.snd = v :=
by simp only [enum_from_eq_enum_add', map_map, prod.map_snd', function.comp.left_id, enum_map_snd']

@[simp] lemma enum_from_nil' : vn.enum_from' k = nil :=
by simp only [eq_iff_true_of_subsingleton]

lemma enum_from_cons_head' : ((x ::ᵥ v).enum_from' k).head = (k, x) :=
by simp only [enum_from_eq_enum_add', map_cons, cons_head, add_zero,
              id.def, enum_cons', prod.map_mk]

@[simp] lemma nth_enum_from' (i : fin n) : (v.enum_from' k).nth i = (k + i, v.nth i) :=
by simp only [enum_from_eq_enum_add', id.def, nth_enum', nth_map, prod.map_mk]

@[simp] lemma enum_from_cons' : ((x ::ᵥ v).enum_from' k) =
  (k, x) ::ᵥ (v.enum_from' (k + 1)) :=
begin
  have : has_add.add k ∘ nat.succ = has_add.add (k + 1),
    { ext, simp only [nat.succ_add, add_zero] },
  simp only [enum_from_eq_enum_add', map_cons, map_map, prod.comp_map,
             add_zero, id.def, function.comp.right_id, enum_cons',
             prod.map_mk, this],
end

lemma to_list_enum_from_of_zip' : (v.enum_from' k).to_list =
  list.zip (list.range' k n) v.to_list :=
by simp only [to_list_enum_from', list.enum_from_eq_zip_range', to_list_length]

lemma enum_from_bdd_below' (i : fin n) : k ≤ ((v.enum_from' k).nth i).fst :=
by simp only [enum_from_eq_enum_add', nth_enum', zero_le,
              le_add_iff_nonneg_right, nth_map, prod.map_mk]

lemma enum_from_bdd_above' (i : fin n) : ((v.enum_from' k).nth i).fst < n + k :=
begin
  simp only [enum_from_eq_enum_add', nth_enum', nth_map, prod.map_mk],
  rw [add_comm, add_lt_add_iff_right],
  exact i.property
end

lemma enum_from_eq_pmap_enum_from' :
  v.enum_from k = vector.pmap (v.enum_from' k) (λ xpair h, ⟨⟨xpair.fst, h⟩, xpair.snd⟩) (v.enum_from_bdd_above' k) :=
begin
  cases n,
  { simp only [eq_iff_true_of_subsingleton] },
  { apply ext,
    intro i,
    simpa only [nth_pmap_cons, add_comm k i, and_true, nth_enum_from, nth_enum_from'] },
end

end enum_from

section enum_prop

variables {m : ℕ} (vs : vector α (n + 1)) (p : α → Prop) [decidable_pred p]

section prop_indicator

variables {ι ι' : Type} [has_zero ι] [has_zero ι'] [has_one ι] [has_one ι']

@[simp] def prop_indicator (x : α) :
  (ι × ι') := ite (p x) (1, 0) (0, 1)

lemma fst_prop_indicator (x : α) :
  prod.fst (@prop_indicator α p _ ι ι' _ _ _ _ x) = ite (p x) 1 0 :=
by { rw prop_indicator, split_ifs; refl }

lemma snd_prop_indicator (x : α) :
  prod.snd (@prop_indicator α p _ ι ι' _ _ _ _ x) = ite (p x) 0 1 :=
by { rw prop_indicator, split_ifs; refl }

end prop_indicator

def enum_prop' : vector ((ℕ × ℕ) × α) n :=
vector.zip ((v.map (prop_indicator p)).scanl (+) 0).tail v

variable {p}

lemma enum_prop_def' :
  v.enum_prop' p = vector.zip ((v.map (prop_indicator p)).scanl (+) 0).tail v := rfl

@[simp] lemma to_list_enum_prop' :
  (enum_prop' v p).to_list = (vector.zip ((v.map (prop_indicator p)).scanl (+) 0).tail v).to_list := rfl

@[simp] lemma enum_prop_nil' : enum_prop' nil p = nil := rfl

@[simp] lemma enum_prop_head' : (enum_prop' vs p).head = (prop_indicator p vs.head, vs.head) :=
begin
  rw ←cons_head_tail vs,
  simp only [enum_prop_def', scanl_head, zip_head, head_map, scanl_tail, zero_add]
end

@[simp] lemma enum_prop_cons' : (enum_prop' (x ::ᵥ v) p) = (prop_indicator p x, x) ::ᵥ
  (v.enum_prop' p).map (prod.map ((+) (prop_indicator p x)) id) :=
begin
  simp only [enum_prop_def', map_cons, cons_tail, map_zip, scanl_cons, zero_add, map_id],
  cases n,
  { simp [enum_prop_def'] },
  { rw [←cons_head_tail v, map_cons],
    simp only [cons_tail, zip_cons, cons_head_tail, scanl_cons, zero_add, scanl_assoc] },
end

@[simp] lemma enum_prop_fst' : (enum_prop' v p).map prod.fst = ((v.map (prop_indicator p)).scanl (+) 0).tail :=
by rw [enum_prop_def', map_fst_zip]

@[simp] lemma enum_prop_snd' : (enum_prop' v p).map prod.snd = v :=
by rw [enum_prop_def', map_snd_zip]

@[simp] lemma enum_prop_tail' : (enum_prop' vs p).tail = (enum_prop' vs.tail p).map (
  prod.map ((+) (prop_indicator p vs.head)) id) :=
begin
  rw [←cons_head_tail vs, enum_prop_cons'],
  simp only [cons_tail, cons_head_tail]
end

@[simp] lemma nth_enum_prop' (i : fin n) : (enum_prop' v p).nth i =
  (((v.take i).map (prop_indicator p)).foldl (+) 0 + prop_indicator p (v.nth i), v.nth i) :=
begin
  induction n with n hn,
  { exact fin_zero_elim i },
  { refine fin.cases _ _ i,
    { simp only [nth_zero, enum_prop_head', foldl_nil', zero_add] },
    { intro i',
      rw [←cons_head_tail v, enum_prop_cons', nth_cons_succ, nth_map, fin.coe_succ,
          take_succ, map_cast, map_cons, foldl_of_cast, foldl_cons,
          foldl_add _ (0 + prop_indicator _ _)],
      simp [add_assoc, map_take, hn] } }
end

lemma enum_prop_flip_eq_swap' : v.enum_prop' (not ∘ p) = (v.enum_prop' p).map (prod.map prod.swap id) :=
begin
  induction n with n hn,
  { simp only [eq_iff_true_of_subsingleton] },
  { rw ←cons_head_tail v,
    by_cases H : p v.head;
    { simp only [H, hn, map_cons, map_map, prop_indicator, if_true, id.def,
                 function.comp_app, not_true, if_false, not_false_iff,
                 enum_prop_cons', prod.swap_prod_mk, prod.map_mk],
      congr } }
end

lemma fst_nth_enum_prop' (i : fin n) :
  ((v.enum_prop' p).nth i).fst = ((v.take (i + 1)).map (prop_indicator p)).foldl (+) 0 :=
begin
  cases n,
  { exact fin_zero_elim i },
  { rw [←cons_head_tail v, enum_prop_def', nth_zip, nth_tail,
        nth_scanl_eq_foldl_of_take, fin.coe_succ],
    simp only [map_cast, map_cons, cons_head_tail, map_take, tail_map, head_map] }
end

@[simp] lemma nth_enum_prop_of_succ' (i : fin n) : (enum_prop' vs p).nth i.succ =
  (((enum_prop' vs p).nth i.cast_succ).fst + prop_indicator p (vs.nth i.succ), vs.nth i.succ) :=
begin
  induction n with n hn,
  { exact fin_zero_elim i },
  { refine fin.cases _ _ i,
    { simp only [nth_zero, fin.cast_succ_zero, and_true, prop_indicator,
                 nth_enum_prop', add_left_inj, prod.mk.inj_iff, foldl_nil',
                 eq_self_iff_true, fin.succ_zero_eq_one, zero_add],
      rw fin.coe_one,
      simp only [take_succ, map_cons, foldl_cons, prop_indicator,
                 take_zero, cast_id, foldl_nil, zero_add, map_nil] },
    { intros i',
      specialize hn vs.tail i',
      simp only [and_true, prop_indicator, nth_enum_prop',
                 add_left_inj, prod.mk.inj_iff, nth_tail, eq_self_iff_true] at hn,
      rw [fin.coe_succ, fin.coe_cast_succ] at hn,
      simp only [take_succ, map_cast, map_cons, map_take,
                 foldl_cons, prop_indicator, foldl_of_cast, zero_add] at hn,
      simp only [prop_indicator, nth_enum_prop', add_left_inj],
      rw [fin.coe_succ, fin.coe_succ, fin.coe_cast_succ, fin.coe_succ],
      simp only [take_succ, map_cast, map_cons, map_take, foldl_cons,
                 and_true, prop_indicator, add_left_inj, prod.mk.inj_iff,
                 foldl_of_cast, eq_self_iff_true, zero_add],
      rw foldl_add at hn ⊢,
      rw [foldl_add _ (ite _ _ _), add_assoc, add_assoc, fin.cast_succ_fin_succ, ←hn] } }
end

lemma enum_prop_filter_eq_map_enum_from_filter' (h : v.filter_count p = m) :
  (v.filter p h).enum_prop' p = ((v.filter p h).enum_from' 1).map (prod.map (λ x, (x, 0)) id) :=
begin
  induction n with n hn generalizing m,
  { simp only [filter_count_nil] at h,
    subst h,
    simp only [eq_iff_true_of_subsingleton] },
  { cases m,
    { simp only [eq_iff_true_of_subsingleton] },
    { obtain ⟨hd, tl, hv⟩ : ∃ hd tl, v = hd ::ᵥ tl :=
        ⟨v.head, v.tail, v.cons_head_tail.symm⟩,
      simp_rw hv,
      by_cases H : p hd,
      { simp only [H, hn, map_cons, map_map, prod.map_comp_map,
                   enum_from_eq_enum_add', enum_from_cons', eq_split,
                   true_and, cons_head, cons_tail, prop_indicator, if_true,
                   id.def, eq_self_iff_true, function.comp.right_id,
                   prod.map_mk, enum_prop_cons', filter_cons_of_pos],
        congr' 1,
        ext;
        simp only [prod.mk_add_mk, prod_map, function.comp_app, add_assoc] },
      { simp only [H, filter_cons_of_neg, not_false_iff, hn] } } }
end

@[simp] lemma filter_count_of_map_snd_enum_prop' :
  (v.enum_prop' p).filter_count (λ xpair, p xpair.snd) = v.filter_count p :=
by rw [←filter_count_of_map, enum_prop_snd']

lemma map_filter_enum_prop_eq_enum_from_filter' {m : ℕ} (h : v.filter_count p = m) :
  ((v.enum_prop' p).filter (λ xpair, p xpair.snd)
    (by rw [filter_count_of_map_snd_enum_prop', h])).map (prod.map prod.fst id) =
  (v.filter p h).enum_from' 1 :=
begin
  induction n with n hn generalizing m,
  { simp only [filter_count_nil] at h,
    subst h,
    simp only [eq_iff_true_of_subsingleton] },
  { cases m,
    { simp only [eq_iff_true_of_subsingleton] },
    { obtain ⟨hd, tl, hv⟩ : ∃ hd tl, v = hd ::ᵥ tl :=
        ⟨v.head, v.tail, v.cons_head_tail.symm⟩,
      simp_rw hv,
      by_cases H : p hd,
      { have h' : tl.filter_count p = m,
        { rwa [hv, filter_count_cons_of_pos _ _ H, nat.succ_inj'] at h, },
        have prod_comm : prod.map prod.fst (@id α) ∘ (prod.map ((+) (1, 0)) id) = prod.map ((+) 1) id ∘ (prod.map prod.fst id),
          { funext, simp only [prod_map, function.comp_app, prod.fst_add] },
        have he : ∀ {n' : ℕ} (v' : vector α n') (k l : ℕ), v'.enum_from' (k + l) = (v'.enum_from' l).map (prod.map ((+) k) id),
          { intros n' v' k l,
            have : ((+) k) ∘ ((+) l) = ((+) (k + l)),
            { intros, funext, rw add_assoc },
            simp only [enum_from_eq_enum_add', map_map, prod.map_comp_map, this,
                       function.comp.right_id] },
        have hp : p ((prop_indicator p hd, hd) : (ℕ × ℕ) × α).snd,
          { simp only [H] },
        simp only [H, hp, map_cons, prop_indicator, if_true,
                   filter_count_of_map_snd_enum_prop', id.def,
                   add_left_inj, enum_prop_cons', filter_cons_of_pos,
                   prod.map_mk, enum_from_cons'],
        congr,
        rw [filter_map, map_map, prod_comm, ←map_map, he, ←hn],
        congr, },
      { have prod_comm : prod.map prod.fst id ∘ (prod.map ((+) (0, 1)) id) = prod.map prod.fst id,
          { funext,
            simp only [prod_map, function.comp_app, prod.fst_add, id.def, zero_add] },
        simp only [H, ←hn, filter_map, map_map, prop_indicator,
                   filter_cons_of_neg, filter_count_of_map_snd_enum_prop',
                   if_false, not_false_iff, enum_prop_cons'],
        rw prod_comm,
        congr } } }
end

lemma enum_prop_fst_bdd_above' (h : v.filter_count p = m) (i : fin n) :
  ((v.enum_prop' p).nth i).fst.fst ≤ m :=
begin
  induction m with m hm generalizing n,
  { induction n with n hn,
    { exact fin_zero_elim i },
    { rw [←cons_head_tail v, enum_prop_cons'],
      have H : ¬ p v.head,
        { rw filter_count_zero_iff at h,
          simpa only [nth_zero] using h 0 },
      have ht : v.tail.filter_count p = 0,
        { rwa [←filter_count_cons_head_tail, filter_count_cons_of_neg _ _ H] at h },
      specialize hn v.tail ht,
      simp only [prop_indicator, nth_enum_prop', le_zero_iff_eq,
                 nth_tail, prod.fst_add, add_eq_zero_iff] at hn,
      refine fin.cases _ _ i,
      { simp only [H, nth_cons_zero, prop_indicator, if_false] },
      { intro i',
        simp only [hn, H, prop_indicator, nth_tail, nth_map, prod.fst_add,
                   if_false, prod.map_mk, nth_cons_succ, nth_enum_prop'] } } },
  { induction n with n hn,
    { exact fin_zero_elim i },
    { rw [←cons_head_tail v, enum_prop_cons'],
      by_cases H : p v.head,
      { refine fin.cases _ _ i,
        { simp only [H, nat.succ_le_succ_iff, nth_cons_zero, prop_indicator, if_true, zero_le] },
        { intro i',
          have ht : v.tail.filter_count p = m,
            { rw [←filter_count_cons_head_tail, filter_count_cons_of_pos _ _ H] at h,
              exact nat.succ.inj h },
          specialize hm v.tail ht i',
          rw [←nat.succ_le_succ_iff, nat.succ_eq_add_one, add_comm] at hm,
          rw [prop_indicator, if_pos H, nth_cons_succ, nth_map],
          refine le_trans _ hm,
          simp only [nth_enum_prop', prod.fst_add, prod.map_mk] } },
      { refine fin.cases _ _ i,
        { simp only [H, nth_cons_zero, prop_indicator, zero_le, if_false] },
        { have ht : v.tail.filter_count p = m + 1,
            { rwa [←filter_count_cons_head_tail, filter_count_cons_of_neg _ _ H] at h },
          intro i',
          specialize hn v.tail ht,
          simp only [prop_indicator, nth_enum_prop', nth_tail, prod.fst_add] at hn,
          simp only [hn, H, prop_indicator, nth_tail, nth_map, prod.fst_add,
                     if_false, prod.map_mk, nth_cons_succ, nth_enum_prop', zero_add] } } } }
end

lemma enum_prop_snd_bdd_above' (h : v.filter_count p = m) (i : fin n) :
  ((v.enum_prop' p).nth i).fst.snd ≤ n - m :=
begin
  have hm : m ≤ n,
    { simpa only [h] using v.filter_count_le_length p },
  have : prod.swap ∘ prod.fst = prod.fst ∘ prod.map prod.swap id,
    { funext, simp only [prod_map, function.comp_app] },
  rw filter_count_flip v hm at h,
  rw [←prod.fst_swap, ←nth_map _ prod.fst, ←nth_map _ prod.swap, map_map,
      this, ←map_map, ←enum_prop_flip_eq_swap', nth_map],
  exact enum_prop_fst_bdd_above' v h i,
end

variable (p)

lemma enum_prop_bdd_above' (hm : v.filter_count p = m) (i : fin n) :
  (λ (xpair : ((ℕ × ℕ) × α)),
    xpair.fst.fst ≤ m ∧ xpair.fst.snd ≤ n - m)
    ((v.enum_prop' p).nth i) :=
begin
  rw ←hm,
  split,
  { apply enum_prop_fst_bdd_above',
    refl },
  { apply enum_prop_snd_bdd_above',
    refl }
end

def enum_prop (hm : v.filter_count p = m) : vector ((fin (m + 1) × fin (n - m + 1)) × α) n :=
vector.pmap (v.enum_prop' p)
  (λ xpair (h : (xpair.fst.fst ≤ m ∧
                 xpair.fst.snd ≤ n - m)),
    ((fin.mk xpair.fst.fst (nat.lt_succ_iff.mpr h.left),
      fin.mk xpair.fst.snd (nat.lt_succ_iff.mpr h.right)), xpair.snd))
  (λ i, enum_prop_bdd_above' v p hm i)

variable {p}

lemma enum_prop_def (hm : v.filter_count p = m) : v.enum_prop p hm = vector.pmap (v.enum_prop' p)
  (λ xpair (h : (xpair.fst.fst ≤ m ∧
                 xpair.fst.snd ≤ n - m)),
    ((fin.mk xpair.fst.fst (nat.lt_succ_iff.mpr h.left),
      fin.mk xpair.fst.snd (nat.lt_succ_iff.mpr h.right)), xpair.snd))
  (λ i, enum_prop_bdd_above' v p hm i) := rfl

@[simp] lemma to_list_enum_prop (hm : v.filter_count p = m) :
  (enum_prop v p hm).to_list = (vector.pmap (v.enum_prop' p)
    (λ xpair (h : (xpair.fst.fst ≤ m ∧
                  xpair.fst.snd ≤ n - m)),
      ((fin.mk xpair.fst.fst (nat.lt_succ_iff.mpr h.left),
        fin.mk xpair.fst.snd (nat.lt_succ_iff.mpr h.right)), xpair.snd))
    (λ i, enum_prop_bdd_above' v p hm i)).to_list := rfl

@[simp] lemma enum_prop_nil : enum_prop nil p (filter_count_nil _) = nil := rfl

@[simp] lemma enum_prop_cons_of_pos (hm : (x::ᵥv).filter_count p = m + 1) (hx : p x) :
  (enum_prop (x ::ᵥ v) p hm) = ((1, 0), x) ::ᵥ
  (v.enum_prop p (nat.succ.inj (by rwa [filter_count_cons_of_pos _ _ hx] at hm))).map
    (prod.map (λ xpair, (xpair.fst.succ, xpair.snd.cast_succ)) id) :=
begin
  induction n with n hn generalizing m x,
  { cases m,
    { simp only [hx, enum_prop_def, fin.mk_zero, fin.coe_coe_eq_self, prop_indicator,
                 if_true, le_zero_iff_eq, fin.coe_cast_succ, pmap_cons, eq_self_iff_true,
                 fin.mk_eq_subtype_mk, enum_prop_cons', and_self, le_add_iff_nonneg_left,
                 fin.mk_one, coe_coe],
      congr },
    { rw [filter_count_cons_of_pos _ _ hx, filter_count_nil, nat.succ_inj'] at hm,
      contradiction } },
  { induction m with m hm generalizing x,
    { have hv : v.filter_count p = 0,
      { rwa [filter_count_cons_of_pos _ _ hx, nat.succ_inj'] at hm },
      simp [hx, enum_prop_def],
    },
  },
  -- induction m with m IH generalizing n x,
  -- {
  --   induction n with n hn generalizing x,
  --   { have : v = nil := by simp only [eq_iff_true_of_subsingleton],
  --     simp [this, enum_prop_def, hx] },
  --   { obtain ⟨hd, tl, hv⟩ : ∃ hd tl, v = hd ::ᵥ tl :=
  --       ⟨v.head, v.tail, v.cons_head_tail.symm⟩,
  --     simp_rw hv,
  --     have : (hd ::ᵥ tl).filter_count =
  --     rw hn tl hd,
  --   },
  --   -- simp [hm, hx, enum_prop_def, zero_add, sub_zero],
  --   -- congr,
  --   -- apply ext,
  -- },
  -- cases n,
  -- { simp [enum_prop_def, hx], },
  -- { rw [←cons_head_tail v, map_cons],
  --   simp only [cons_tail, zip_cons, cons_head_tail, scanl_cons, zero_add, scanl_assoc] },
end

@[simp] lemma enum_prop_head : (enum_prop vs p).head = (ite (p vs.head) (1, 0) (0, 1), vs.head) :=
begin
  cases n,
  {
    by_cases h : p vs.head,
    { have hp : vs.filter_count p = 1,
      { rw ←cons_head_tail vs,
        simp only [h, if_true, filter_count_cons, filter_count_nil] },
      have hn : vs.filter_count (not ∘ p) = 0,
        { rw [filter_count_flip' vs (zero_le _), hp] },
      rw ←cons_head_tail vs,
      rw enum_
      simp [-cons_head_tail, h, hp, hn],
    },
  },
  rw ←cons_head_tail vs,
  by_cases h : p vs.head,
  { have : ∃ n, n + 2 = vs.filter_count p,
      { rw ←cons_head_tail vs,
        simp [-cons_head_tail, h],
      },
    simp [enum_prop_def, scanl_head, zip_head, head_map, scanl_tail, zero_add, h],
    rw fin.eq_iff_veq,
    simp,
    rw fin.coe_one,
  }
end

@[simp] lemma enum_prop_fst : (enum_prop v p).map prod.fst = ((v.map (prop_indicator p)).scanl (+) 0).tail :=
by rw [enum_prop_def, map_fst_zip]

@[simp] lemma enum_prop_snd : (enum_prop v p).map prod.snd = v :=
by rw [enum_prop_def, map_snd_zip]

@[simp] lemma enum_prop_tail : (enum_prop vs p).tail = (enum_prop vs.tail p).map (
  prod.map ((+) (prop_indicator p vs.head)) id) :=
begin
  rw [←cons_head_tail vs, enum_prop_cons],
  simp only [cons_tail, cons_head_tail]
end

@[simp] lemma nth_enum_prop (i : fin n) : (enum_prop v p).nth i =
  (((v.take i).map (prop_indicator p)).foldl (+) 0 + prop_indicator p (v.nth i), v.nth i) :=
begin
  induction n with n hn,
  { exact fin_zero_elim i },
  { refine fin.cases _ _ i,
    { simp only [nth_zero, enum_prop_head, foldl_nil, zero_add] },
    { intro i,
      rw [←cons_head_tail v, enum_prop_cons, nth_cons_succ, nth_map, fin.coe_succ,
          take_succ, map_cast, map_cons, foldl_of_cast, foldl_cons,
          foldl_add _ (0 + prop_indicator _ _)],
      simp [add_assoc, map_take, hn] } }
end

end enum_prop

end enum

end vector
