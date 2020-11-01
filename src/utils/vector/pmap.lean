import data.vector2

variables {α β γ : Type*} {n : ℕ}
variables (v : vector α n) (vn : vector α 0) (vs : vector α (n + 1))
variables (x : α)

open vector

namespace vector

variables {v vn vs x}
variables {p q : α → Prop}

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

lemma nth_of_mem (h : x ∈ v.to_list) : ∃ i, v.nth i = x :=
mem_iff_nth.mp h

lemma forall_mem_to_list_iff : (∀ x ∈ v.to_list, p x) ↔ ∀ (i : fin n), p (v.nth i) :=
⟨ λ h i, h _ (mem_iff_nth.mpr ⟨i, rfl⟩), λ h _ hx, exists.elim (nth_of_mem hx) (λ _ H, H ▸ h _)⟩

section pmap

variables (v)

def pmap (f : Π (x : α), p x → β)
  (h : ∀ i : fin n, p (v.nth i)) : vector β n :=
⟨list.pmap f v.to_list (forall_mem_to_list_iff.mpr h), by rw [list.length_pmap, to_list_length]⟩

lemma pmap_def (f : Π (x : α), p x → β) (h : ∀ i : fin n, p (v.nth i)) :
  v.pmap f h = ⟨list.pmap f v.to_list (forall_mem_to_list_iff.mpr h),
                by rw [list.length_pmap, to_list_length]⟩ := rfl

lemma to_list_pmap (f : Π (x : α), p x → β)
  (h : ∀ i : fin n, p (v.nth i)) : (v.pmap f h).to_list = v.to_list.pmap f (forall_mem_to_list_iff.mpr h) := rfl

variable (p)

lemma pmap_eq_map (f : α → β) (h) : @pmap _ _ _ v p (λ x _, f x) h = v.map f :=
vector.eq _ _ (by simp only [to_list_map, to_list_pmap, list.pmap_eq_map])

variable {p}

lemma pmap_congr {f : Π (x : α), p x → β} {g : Π (x : α), q x → β} {H₁ H₂}
  (h : ∀ x h₁ h₂, f x h₁ = g x h₂) :
  v.pmap f H₁ = v.pmap g H₂ :=
vector.eq _ _ (v.to_list.pmap_congr h)

lemma map_pmap (g : β → γ) (f : Π (x : α), p x → β) (H) :
  (v.pmap f H).map g = v.pmap (λ a h, g (f a h)) H :=
vector.eq _ _ (list.map_pmap g f v.to_list (forall_mem_to_list_iff.mpr H))

@[simp] lemma pmap_nil {f : Π (x : α), p x → β} {h} :
  nil.pmap f h = nil := rfl

lemma pmap_nil' {f : Π (x : α), p x → β} {h} :
  vn.pmap f h = nil := by simp only [eq_iff_true_of_subsingleton]

@[simp] lemma pmap_singleton {f : Π (x : α), p x → β} {h} :
  (x ::ᵥ nil).pmap f h = f x (h 0) ::ᵥ nil := rfl

@[simp] lemma pmap_cons {f : Π (x : α), p x → β} {h} (hx : p x) :
  (x ::ᵥ v).pmap f h = f x hx ::ᵥ v.pmap f (prop_distribute.mpr h).right :=
by simpa only [pmap_def, to_list_cons]

@[simp] lemma pmap_head {f : Π (x : α), p x → β} : Π {vs : vector α (n + 1)} {h},
  (vs.pmap f h).head = f vs.head (prop_distribute'.mp h).left
| ⟨[],     hl⟩ _ := by contradiction
| ⟨x :: l, hl⟩ _ := rfl

@[simp] lemma nth_pmap_cons {f : Π (x : α), p x → β} {H i} :
  (v.pmap f H).nth i = f (v.nth i) (H i) :=
begin
  induction n with n hn generalizing f H i,
  { exact fin_zero_elim i },
  { have : ∃ h t, h ::ᵥ t = v := ⟨v.head, v.tail, cons_head_tail v⟩,
    rcases this with ⟨x, t, hv⟩,
    simp_rw ←hv at H ⊢,
    have hx : p x := (prop_distribute.mpr H).left,
    refine fin.cases _ _ i,
    { simp only [nth_zero, pmap_head] },
    { rw pmap_cons _ hx,
      simp_rw nth_cons_succ,
      apply hn } }
end

end pmap

end vector
