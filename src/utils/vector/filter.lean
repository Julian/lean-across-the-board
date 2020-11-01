import data.matrix.notation
import data.vector2

variables {α : Type*} {n m : ℕ}
variables (l : list α) (v : vector α n) (vn : vector α 0) (vs : vector α (n + 1)) (x : α)
variables (p : α → Prop)

open vector

namespace vector

lemma prop_distribute :
  p x ∧ (∀ i, p (v.nth i)) ↔ ∀ i, p ((x ::ᵥ v).nth i) :=
begin
  split,
    { rintro ⟨hx, ht⟩ i,
      refine fin.cases _ _ i,
      { simpa only [nth_cons_zero] using hx },
      { simpa only [nth_cons_succ] using ht } },
    { intro h,
      split,
      { simpa only [nth_cons_zero] using h 0 },
      { intro i,
        simpa only [nth_cons_succ] using h i.succ } }
end

lemma prop_distribute' :
  (∀ i, p (vs.nth i)) ↔ p vs.head ∧ (∀ i', p (vs.tail.nth i')) :=
begin
  split,
  { intro h,
    split,
    { simpa only [nth_zero] using h 0 },
    { intro i,
      simpa only [nth_tail] using h i.succ } },
  { rintro ⟨hx, ht⟩ i,
    refine fin.cases _ _ i,
    { simpa only [nth_zero] using hx },
    { simpa only [nth_tail] using ht} },
end

variables [decidable_pred p]

/-- Count the number of elements of `vector α n` that match a proposition `p : α → Prop`. -/
def filter_count : ℕ := (v.to_list.filter p).length

lemma filter_count_def : v.filter_count p = (v.to_list.filter p).length := rfl

variable {p}

@[simp] lemma filter_count_nil : vn.filter_count p = 0 :=
begin
  have : vn = nil := by simp only [eq_iff_true_of_subsingleton],
  simp only [this, filter_count_def, to_list_nil, list.filter_nil, list.length],
end

@[simp] lemma filter_count_cons :
  (x ::ᵥ v).filter_count p = v.filter_count p + ite (p x) 1 0 :=
begin
  rw filter_count_def,
  simp only [list.filter, to_list_cons],
  split_ifs;
  simp only [filter_count_def, list.length, add_zero]
end

lemma filter_count_cons_head_tail :
  (vs.head ::ᵥ vs.tail).filter_count p = vs.filter_count p :=
by simp only [cons_head_tail]

lemma filter_count_cons_of_pos (hx : p x) :
  (x ::ᵥ v).filter_count p = v.filter_count p + 1 :=
by simp only [hx, filter_count_cons, if_true]

variable (p)

lemma filter_count_zero_iff : v.filter_count p = 0 ↔ ∀ i, ¬ p (v.nth i) :=
begin
  induction n with n hn,
  { have : v = nil := by simp only [eq_iff_true_of_subsingleton],
    simpa only [true_iff, filter_count_nil, eq_self_iff_true] using fin_zero_elim },
  { specialize hn v.tail,
    split,
    { intros h i,
      rw [←v.cons_head_tail, filter_count_cons, add_eq_zero_iff] at h,
      refine fin.cases _ _ i,
      { intro H,
        rw [nth_zero] at H,
        simpa only [H, if_true] using h.right },
      { intros ix Hs,
        rw [←v.cons_head_tail, nth_cons_succ] at Hs,
        exact hn.mp h.left ix Hs } },
    { intros h,
      rw [←v.cons_head_tail, filter_count_cons, ←nth_zero, if_neg (h 0)],
      apply hn.mpr,
      simp only [h, not_false_iff, nth_tail, forall_true_iff] } },
end

lemma filter_count_pos : 0 < v.filter_count p ↔ ∃ i, p (v.nth i) :=
begin
  split;
  { contrapose!,
    rw ←filter_count_zero_iff v p,
    simp only [imp_self, le_zero_iff_eq] },
end

lemma filter_count_le_length : v.filter_count p ≤ n :=
begin
  induction n with n hn,
  { simp only [filter_count_nil] },
  { rw [←cons_head_tail v, filter_count_cons],
    specialize hn v.tail,
    simp_rw nat.succ_eq_add_one n,
    refine add_le_add hn _,
    split_ifs,
    { refl },
    { exact nat.zero_le 1 } }
end

variable {p}

lemma filter_count_imp_head
  (hm : vs.filter_count p = m + 1) (hl : n + 1 ≤ m + 1) :
  p vs.head :=
begin
  by_contradiction H,
  rw [←cons_head_tail vs, filter_count_cons,
      if_neg H, add_zero] at hm,
  have := vs.tail.filter_count_le_length p,
  rw [hm, nat.add_succ_sub_one, add_zero] at this,
  exact absurd (le_trans hl this) (nat.lt_irrefl n),
end

lemma filter_count_tail (hm : vs.filter_count p = m + 1)
  (hl : n + 1 ≤ m + 1):
  vs.tail.filter_count p = m :=
begin
  have hx : p vs.head := filter_count_imp_head _ hm hl,
  rw [←cons_head_tail vs, filter_count_cons] at hm,
  simpa only [hx, if_true, add_left_inj] using hm,
end

@[simp] lemma nth_cons_nil' {ix : fin 1}
  (x : α) : nth (x ::ᵥ nil) ix = x :=
by convert nth_cons_zero x nil

lemma filter_count_iff : v.filter_count p = n ↔ ∀ i, p (v.nth i) :=
begin
  induction n with n IH,
  { simpa only [true_iff, eq_self_iff_true, filter_count_nil] using fin_zero_elim },
  { rw prop_distribute',
    split,
    { intro hn,
      have hx : p v.head := filter_count_imp_head _ hn (le_refl _),
      refine ⟨hx, _⟩,
      intro i,
      specialize IH v.tail,
      apply IH.mp,
      exact filter_count_tail v hn (le_refl _) },
    { intro h,
      rw [←filter_count_cons_head_tail, filter_count_cons_of_pos _ _ h.left],
      rw [add_left_inj 1, IH],
      exact h.right } }
end

lemma filter_count_imp_tail (hn : vs.filter_count p = n + 1) :
  ∀ i, p (vs.tail.nth i) :=
by rw [←filter_count_iff, filter_count_tail _ hn (le_refl _),
       nat.add_succ_sub_one, add_zero]

variable (p)

/--
Retain the 'm = v.filter_count p = m of elements of `vector α n`
that match a proposition `p : α → Prop`,
-/
def filter (h : v.filter_count p = m) : vector α m :=
⟨v.to_list.filter p, h⟩

variables (hm : v.filter_count p = m)

variable {p}

lemma filter_def : v.filter p hm = ⟨v.to_list.filter p, hm⟩ := rfl

@[simp] lemma filter_length : (v.filter p hm).length = m := rfl

@[simp] lemma to_list_filter : (v.filter p hm).to_list = v.to_list.filter p := rfl

@[simp] lemma filter_nil (hm : vn.filter_count p = 0) :
  (vn.filter p hm) = nil :=
by simp only [eq_iff_true_of_subsingleton]

lemma filter_cons_of_pos' (hx : p x) :
  x ::ᵥ v.filter p hm = (x ::ᵥ v).filter p (by rw [filter_count_cons, if_pos hx, hm]) :=
by simp only [filter_def, list.filter, hx, cons, and_self,
              to_list_cons, if_true, eq_self_iff_true, subtype.mk_eq_mk]

@[simp] lemma filter_cons_of_pos (hx : p x) (hm : (x ::ᵥ v).filter_count p = m + 1) :
  (x ::ᵥ v).filter p hm =
  x ::ᵥ v.filter p (by simpa only [hx, add_left_inj, filter_count_cons_of_pos] using hm) :=
by rw filter_cons_of_pos' _ _ _ hx

lemma filter_head_tail (hm : vs.filter_count p = m + 1) :
  (vs.head ::ᵥ vs.tail).filter p (by simp [hm]) = vs.filter p hm :=
by simp only [cons_head_tail]

@[simp] lemma filter_head (hm : vs.filter_count p = m + 1)
  (hl : n + 1 ≤ m + 1) :
  (vs.filter p hm).head = vs.head :=
begin
  have hx : p vs.head := filter_count_imp_head _ hm hl,
  rw [←filter_head_tail, filter_cons_of_pos _ _ hx],
  refl
end

lemma eq_split (v v' : vector α (n + 1)) :
  v = v' ↔ v.head = v'.head ∧ v.tail = v'.tail :=
begin
  split,
  { intro h,
    simp only [h, eq_self_iff_true, and_self] },
  { rintro ⟨h, ht⟩,
    rw [←cons_head_tail v, ←cons_head_tail v', h, ht] }
end

@[simp] lemma filter_tail (hn : vs.filter_count p = n + 1) :
  (vs.filter p hn).tail = vs.tail :=
begin
  have hx : p vs.head := filter_count_imp_head _ hn (le_refl _),
  rw [←filter_head_tail, filter_cons_of_pos _ _ hx],
  induction n with n IH,
  { simp only [eq_iff_true_of_subsingleton] },
  { have ht : vs.tail.filter_count p = n + 1 := filter_count_tail vs hn (le_refl _),
    have hx' : p vs.tail.head := filter_count_imp_head _ ht (le_refl _),
    rw [tail_cons, ←filter_head_tail vs.tail,
        filter_cons_of_pos _ _ hx', eq_split],
    simp only [IH, cons_head, eq_self_iff_true, and_self] }
end

lemma filter_nth_succ (hn : vs.filter_count p = n + 1) (i : fin n) :
  (vs.filter p hn).nth i.succ = (vs.tail.filter p (vs.filter_count_tail hn (le_refl (n + 1)))).nth i :=
begin
  have hx : p vs.head := filter_count_imp_head _ hn (le_refl _),
  rw [←filter_head_tail, filter_cons_of_pos _ _ hx],
  simp only [nth_cons_succ]
end

@[simp] lemma filter_count_filter : (v.filter p hm).filter_count p = m :=
begin
  simp only [←hm, filter_count_def, filter_def,
             to_list_mk, list.filter_filter, and_self],
  congr,
end

lemma filter_imp_head (hn : vs.filter_count p = n + 1) :
  p (vs.filter p hn).head ↔ p vs.head :=
by simp only [filter_head]

lemma filter_imp_tail (hn : vs.filter_count p = n + 1) (i : fin n) :
  p ((vs.filter p hn).tail.nth i) ↔ p (vs.tail.nth i) :=
by simp only [filter_tail]

lemma cons_filter_is_neg (hm' : (x ::ᵥ v.filter p hm).filter_count p = m) :
  ¬ p x :=
begin
  intro H,
  simp only [H, filter_count_cons_of_pos, filter_count_filter] at hm',
  exact (nat.succ_ne_self m) hm',
end

lemma filter_valid (hm : v.filter_count p = m) : ∀ i, p ((v.filter p hm).nth i) :=
begin
  cases n,
  { have hm' : m = 0,
      { simpa only [filter_count_nil] using hm.symm },
    unify_equations hm',
    exact fin_zero_elim },
  { cases m,
    { exact fin_zero_elim },
    { rw prop_distribute',
      have hx : p (v.filter p hm).head,
        { refine filter_count_imp_head _ _ (le_refl (m + 1)),
          simp only [filter_count_filter] },
      simp only [hx, true_and],
      apply filter_count_imp_tail,
      simp only [filter_count_filter] } }
end

end vector
