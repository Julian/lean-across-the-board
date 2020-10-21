import data.matrix.notation
import data.vector2

variables {α : Type*} {n m : ℕ}
variables (l : list α) (v : vector α n)
variables (p : α → Prop) [decidable_pred p]

def vector.filter_count : ℕ := (v.to_list.filter p).length


lemma vector.filter_count_def : v.filter_count p = (v.to_list.filter p).length := rfl

variable {p}

@[simp] lemma vector.filter_count_nil (v : vector α 0) : v.filter_count p = 0 :=
begin
  have : v = vector.nil := by simp only [eq_iff_true_of_subsingleton],
  simp only [this, vector.filter_count_def, vector.to_list_nil, list.filter_nil, list.length],
end

@[simp] lemma vector.filter_count_cons (x : α) :
  (x ::ᵥ v).filter_count p = v.filter_count p + ite (p x) 1 0 :=
begin
  rw vector.filter_count_def,
  simp only [list.filter, vector.to_list_cons],
  split_ifs;
  simp only [vector.filter_count_def, list.length, add_zero]
end

@[simp] lemma vector.filter_count_cons_head_tail (v : vector α (n + 1)) :
  (v.head ::ᵥ v.tail).filter_count p = v.filter_count p :=
by simp only [vector.cons_head_tail]

@[simp] lemma vector.filter_count_cons_of_pos (x : α) (hx : p x) :
  (x ::ᵥ v).filter_count p = v.filter_count p + 1 :=
by simp only [hx, vector.filter_count_cons, if_true]

variable (p)

lemma vector.filter_count_zero_iff : v.filter_count p = 0 ↔ ∀ i, ¬ p (v.nth i) :=
begin
  induction n with n hn,
  { have : v = vector.nil := by simp only [eq_iff_true_of_subsingleton],
    simpa only [true_iff, vector.filter_count_nil, eq_self_iff_true] using fin_zero_elim },
  { specialize hn v.tail,
    split,
    { intros h i,
      rw [←v.cons_head_tail, vector.filter_count_cons, add_eq_zero_iff] at h,
      refine fin.cases _ _ i,
      { intro H,
        rw [vector.nth_zero] at H,
        simpa only [H, if_true] using h.right },
      { intros ix Hs,
        rw [←v.cons_head_tail, vector.nth_cons_succ] at Hs,
        exact hn.mp h.left ix Hs } },
    { intros h,
      rw [←v.cons_head_tail, vector.filter_count_cons, ←vector.nth_zero, if_neg (h 0)],
      apply hn.mpr,
      simp only [h, not_false_iff, vector.nth_tail, forall_true_iff] } },
end

lemma vector.filter_count_pos : 0 < v.filter_count p ↔ ∃ i, p (v.nth i) :=
begin
  split;
  { contrapose!,
    rw ←vector.filter_count_zero_iff v p,
    simp only [imp_self, le_zero_iff_eq] },
end

lemma vector.filter_count_le_length : v.filter_count p ≤ n :=
begin
  induction n with n hn,
  { simp only [vector.filter_count_nil] },
  { rw [←vector.cons_head_tail v, vector.filter_count_cons],
    specialize hn v.tail,
    simp_rw nat.succ_eq_add_one n,
    refine add_le_add hn _,
    split_ifs,
    { refl },
    { exact nat.zero_le 1 } }
end

variable {p}

lemma vector.filter_count_imp_head (v : vector α (n + 1))
  (hm : v.filter_count p = m + 1) (hl : n + 1 ≤ m + 1) :
  p v.head :=
begin
  by_contradiction H,
  rw [←vector.cons_head_tail v, vector.filter_count_cons,
      if_neg H, add_zero] at hm,
  have := v.tail.filter_count_le_length p,
  rw [hm, nat.add_succ_sub_one, add_zero] at this,
  exact absurd (le_trans hl this) (nat.lt_irrefl n),
end

lemma vector.filter_count_tail (v : vector α (n + 1)) (hm : v.filter_count p = m + 1)
  (hl : n + 1 ≤ m + 1):
  v.tail.filter_count p = m :=
begin
  have hx : p v.head := vector.filter_count_imp_head _ hm hl,
  rw [←vector.cons_head_tail v, vector.filter_count_cons] at hm,
  simpa only [hx, if_true, add_left_inj] using hm,
end

@[simp] lemma vector.nth_cons_nil' {ix : fin 1}
  (x : α) : vector.nth (x ::ᵥ vector.nil) ix = x :=
by convert vector.nth_cons_zero x vector.nil

lemma vector.prop_distribute (v : vector α n) (x : α) :
  p x ∧ (∀ i, p (v.nth i)) ↔ ∀ i, p ((x ::ᵥ v).nth i) :=
begin
  split,
    { rintro ⟨hx, ht⟩ i,
      refine fin.cases _ _ i,
      { simpa only [vector.nth_cons_zero] using hx },
      { simpa only [vector.nth_cons_succ] using ht } },
    { intro h,
      split,
      { simpa only [vector.nth_cons_zero] using h 0 },
      { intro i,
        simpa only [vector.nth_cons_succ] using h i.succ } }
end

lemma vector.prop_distribute' (v : vector α (n + 1)) :
  (∀ i, p (v.nth i)) ↔ p v.head ∧ (∀ i', p (v.tail.nth i')) :=
begin
  split,
  { intro h,
    split,
    { simpa only [vector.nth_zero] using h 0 },
    { intro i,
      simpa only [vector.nth_tail] using h i.succ } },
  { rintro ⟨hx, ht⟩ i,
    refine fin.cases _ _ i,
    { simpa only [vector.nth_zero] using hx },
    { simpa only [vector.nth_tail] using ht} },
end

lemma vector.filter_count_iff : v.filter_count p = n ↔ ∀ i, p (v.nth i) :=
begin
  induction n with n IH,
  { simpa only [true_iff, eq_self_iff_true, vector.filter_count_nil] using fin_zero_elim },
  { rw vector.prop_distribute',
    split,
    { intro hn,
      have hx : p v.head := vector.filter_count_imp_head _ hn (le_refl _),
      refine ⟨hx, _⟩,
      intro i,
      specialize IH v.tail,
      apply IH.mp,
      exact vector.filter_count_tail v hn (le_refl _) },
    { intro h,
      rw [←vector.filter_count_cons_head_tail, vector.filter_count_cons_of_pos _ _ h.left],
      rw [add_left_inj 1, IH],
      exact h.right } }
end

lemma vector.filter_count_imp_tail (v : vector α (n + 1)) (hn : v.filter_count p = n + 1) :
  ∀ i, p (v.tail.nth i) :=
by rw [←vector.filter_count_iff, vector.filter_count_tail _ hn (le_refl _),
       nat.add_succ_sub_one, add_zero]

variable (p)

def vector.filter (h : v.filter_count p = m) : vector α m :=
⟨v.to_list.filter p, h⟩

variables (hm : v.filter_count p = m)

variable {p}

lemma vector.filter_def : v.filter p hm = ⟨v.to_list.filter p, hm⟩ := rfl

@[simp] lemma vector.filter_length : (v.filter p hm).length = m := rfl

@[simp] lemma vector.to_list_filter : (v.filter p hm).to_list = v.to_list.filter p := rfl

@[simp] lemma vector.filter_nil (v' : vector α 0) (hm : v'.filter_count p = 0) :
  (v'.filter p hm) = vector.nil :=
by simp only [eq_iff_true_of_subsingleton]

lemma vector.filter_cons_of_pos' (x : α) (hx : p x) :
  x ::ᵥ v.filter p hm = (x ::ᵥ v).filter p (by rw [vector.filter_count_cons, if_pos hx, hm]) :=
by simp only [vector.filter_def, list.filter, hx, vector.cons, and_self,
              vector.to_list_cons, if_true, eq_self_iff_true, subtype.mk_eq_mk]

@[simp] lemma vector.filter_cons_of_pos (x : α) (hx : p x) (hm : (x ::ᵥ v).filter_count p = m + 1) :
  (x ::ᵥ v).filter p hm =
  x ::ᵥ v.filter p (by simpa only [hx, add_left_inj, vector.filter_count_cons_of_pos] using hm) :=
by rw vector.filter_cons_of_pos' _ _ _ hx

lemma vector.filter_head_tail (v : vector α (n + 1)) (hm : v.filter_count p = m + 1) :
  (v.head ::ᵥ v.tail).filter p (by simp [hm]) = v.filter p hm :=
by simp only [vector.cons_head_tail]

@[simp] lemma vector.filter_head (v : vector α (n + 1)) (hm : v.filter_count p = m + 1)
  (hl : n + 1 ≤ m + 1) :
  (v.filter p hm).head = v.head :=
begin
  have hx : p v.head := vector.filter_count_imp_head _ hm hl,
  rw [←vector.filter_head_tail, vector.filter_cons_of_pos _ _ hx],
  refl
end

lemma vector.eq_split (v v' : vector α (n + 1)) :
  v = v' ↔ v.head = v'.head ∧ v.tail = v'.tail :=
begin
  split,
  { intro h,
    simp only [h, eq_self_iff_true, and_self] },
  { rintro ⟨h, ht⟩,
    rw [←vector.cons_head_tail v, ←vector.cons_head_tail v', h, ht] }
end

@[simp] lemma vector.filter_tail (v : vector α (n + 1)) (hn : v.filter_count p = n + 1) :
  (v.filter p hn).tail = v.tail :=
begin
  have hx : p v.head := vector.filter_count_imp_head _ hn (le_refl _),
  rw [←vector.filter_head_tail, vector.filter_cons_of_pos _ _ hx],
  induction n with n IH,
  { simp only [eq_iff_true_of_subsingleton] },
  { have ht : v.tail.filter_count p = n + 1 := vector.filter_count_tail v hn (le_refl _),
    have hx' : p v.tail.head := vector.filter_count_imp_head _ ht (le_refl _),
    rw [vector.tail_cons, ←vector.filter_head_tail v.tail,
        vector.filter_cons_of_pos _ _ hx', vector.eq_split],
    simp only [IH, vector.cons_head, eq_self_iff_true, and_self] }
end

lemma vector.filter_nth_succ (v : vector α (n + 1)) (hn : v.filter_count p = n + 1) (i : fin n) :
  (v.filter p hn).nth i.succ = (v.tail.filter p (v.filter_count_tail hn (le_refl (n + 1)))).nth i :=
begin
  have hx : p v.head := vector.filter_count_imp_head _ hn (le_refl _),
  rw [←vector.filter_head_tail, vector.filter_cons_of_pos _ _ hx],
  simp only [vector.nth_cons_succ]
end

@[simp] lemma vector.filter_count_filter : (v.filter p hm).filter_count p = m :=
begin
  simp only [←hm, vector.filter_count_def, vector.filter_def,
             vector.to_list_mk, list.filter_filter, and_self],
  congr,
end

lemma vector.filter_imp_head (v : vector α (n + 1)) (hn : v.filter_count p = n + 1) :
  p (v.filter p hn).head ↔ p v.head :=
by simp only [vector.filter_head]

lemma vector.filter_imp_tail (v : vector α (n + 1)) (hn : v.filter_count p = n + 1) (i : fin n) :
  p ((v.filter p hn).tail.nth i) ↔ p (v.tail.nth i) :=
by simp only [vector.filter_tail]

@[simp] lemma vector.cons_filter_is_neg (x : α) (hm' : (x ::ᵥ v.filter p hm).filter_count p = m) :
  ¬ p x :=
begin
  intro H,
  simp only [H, vector.filter_count_cons_of_pos, vector.filter_count_filter] at hm',
  exact (nat.succ_ne_self m) hm',
end

lemma vector.filter_valid (hm : v.filter_count p = m) : ∀ i, p ((v.filter p hm).nth i) :=
begin
  cases n,
  { have hm' : m = 0,
      { simpa only [vector.filter_count_nil] using hm.symm },
    unify_equations hm',
    exact fin_zero_elim },
  { cases m,
    { exact fin_zero_elim },
    { rw vector.prop_distribute',
      have hx : p (v.filter p hm).head,
        { refine vector.filter_count_imp_head _ _ (le_refl (m + 1)),
          simp only [vector.filter_count_filter] },
      simp only [hx, true_and],
      apply vector.filter_count_imp_tail,
      simp only [vector.filter_count_filter] } }
end
