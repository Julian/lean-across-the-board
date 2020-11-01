import data.matrix.notation
import data.vector2

open vector

local attribute [-simp] cons_head_tail

namespace vector

section enum

variables {α : Type*} {n : ℕ}
variables (v : vector α n) (vn : vector α 0) (vs : vector α (n + 1))
variables (x : α)

lemma prop_distribute (p : α → Prop) :
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

lemma prop_distribute' (p : α → Prop) :
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

def enum : vector (fin n × α) n :=
vector.of_fn (λ i, (i, v.nth i))

lemma enum_def : v.enum = vector.of_fn (λ i, (i, v.nth i)) := rfl


end enum

section snoc

variables {α : Type*} {n m : ℕ}
variables (v : vector α n) (vn : vector α 0) (vs : vector α (n + 1))
variables (x : α)


#check vector.nth_mem

end snoc

section pmap

variables {α : Type*} {n : ℕ}
variables (v : vector α n) (vn : vector α 0) (vs : vector α (n + 1)) (x : α)

variables {v x}
lemma nth_of_mem (h : x ∈ v.to_list) : ∃ i, v.nth i = x :=
mem_iff_nth.mp h

variables (v)

@[simp] def pmap {α β : Type*} {n : ℕ} (v : vector α n) {p : α → Prop}
  (f : Π a, p a → β) (h : ∀ i : fin n, p (v.nth i)) : vector β n :=
⟨list.pmap f v.to_list (λ x hx, exists.elim (nth_of_mem hx) (λ i hi, hi ▸ h i)),
  by rw [list.length_pmap, to_list_length]⟩

#check pmap v.enum' (λ xpair h, ((⟨xpair.fst, h⟩ : fin n), xpair.snd)) (v.enum_bdd_above'')

end pmap

section dmap

#check list.length_pmap

-- | []     H := []
-- | (a::l) H := f a (forall_mem_cons.1 H).1 :: pmap l (forall_mem_cons.1 H).2

def dmap' {α β : Type*} (m : ℕ) (p : β → Prop) (γ : ℕ → Type* → Type*)
         (g : Π {k : ℕ}, vector α k → vector β k)
          :
  Π {n : ℕ} (hl : n ≤ m) (v : vector α n)
  (h : Π {k : ℕ}, ∀ (v' : vector α k), k ≤ n → ∀ i, p ((g v').nth i))
  (f : Π (b : β), n ≤ m → p b → γ m β)
     ,
  vector (γ m β) n
| 0       hl v h f := nil
| 1       hl v h f := f ((g v).nth 0) hl (h _ (le_refl _) _) ::ᵥ nil
| (n + 2) hl v h f := f ((g v).nth 0) hl (h _ (le_refl _) 0) ::ᵥ dmap'
  (le_trans (nat.sub_le (n + 2) 1) hl)
  v.tail
  (λ k v' H, h v' (le_trans H (nat.sub_le (n + 2) 1)))
  (λ b _, f b hl)

def dmap {α β : Type*} {n : ℕ} (v : vector α n) (p : β → Prop) (γ : ℕ → Type* → Type*)
         (g : Π {k : ℕ}, vector α k → vector β k)
         (h : Π {k : ℕ}, ∀ (v' : vector α k), k ≤ n → ∀ i, p ((g v').nth i))
         (f : Π (b : β), p b → γ n β) :
         vector (γ n β) n :=
dmap' n p γ (λ _, g) (le_refl n) v (λ _, h) (λ _ _, f _)

variables {α : Type*} {n : ℕ}
variables (v : vector α n) (vn : vector α 0) (vs : vector α (n + 1))

#check @dmap' α (ℕ × α) n (λ i, i.fst < n) (λ k x, fin k × x) (@enum' α)
        n (le_refl _) v
          (λ k v' h i, by { rw ←nth_map v'.enum' prod.fst i,
          refine lt_of_lt_of_le (@enum_bdd_above' _ k v' i) h, })
          (λ ⟨i, x⟩ h H, ⟨⟨i, H⟩, ⟨i, x⟩⟩)
#check dmap' n (λ i, prod.fst i < n) (λ k x, fin k × x) (@enum' α)
        (le_refl _) v
          (λ k v' h i, by { rw ←nth_map v'.enum' prod.fst i,
          refine lt_of_lt_of_le (@enum_bdd_above' _ k v' i) h, })
          (λ ⟨i, x⟩ h H, ⟨⟨i, H⟩, ⟨i, x⟩⟩)
          -- (vector.of_fn ![10, 9, 8])

def prodFst {α β : Type*} (x : α × β) : Type* := α

def prodSnd {α β : Type*} (x : α × β) : Type* := β

#check v.dmap (λ b, prod.fst b < n) (λ k t, fin k × _) (λ _, enum')
          (λ _ v' h i, lt_of_lt_of_le (enum_bdd_above'' v' i) h)
          (λ ⟨i, x⟩ H, ((⟨i, H⟩ : fin n), x))


end dmap

#exit
section enum_from

variables {α : Type*} {n : ℕ} (v : vector α n) (vn : vector α 0) (x : α) (m : ℕ)

local attribute [-simp] cons_head_tail

def enum_from : vector (ℕ × α) n :=
⟨v.to_list.enum_from m, by rw [list.length_enum_from, to_list_length]⟩

lemma enum_from_def : v.enum_from m = ⟨v.to_list.enum_from m,
                                       by rw [list.length_enum_from, to_list_length]⟩ := rfl

lemma to_list_enum_from : (v.enum_from m).to_list = v.to_list.enum_from m := rfl

@[simp] lemma enum_from_nil : vn.enum_from m = nil :=
by simp only [eq_iff_true_of_subsingleton]

@[simp] lemma enum_from_cons :
  (x ::ᵥ v).enum_from m = (m, x) ::ᵥ v.enum_from (m + 1) :=
by simpa only [enum_from_def, to_list_cons]

@[simp] lemma nth_enum_from (i : fin n) : (v.enum_from m).nth i = (m + i, v.nth i) :=
begin
  induction n with n hn generalizing m,
  { exact fin_zero_elim i },
  { rw ←cons_head_tail v,
    refine fin.cases _ _ i,
    { simp only [add_zero, fin.coe_zero, nth_cons_zero, enum_from_cons] },
    { simp only [enum_from_cons, nth_cons_succ, fin.coe_succ, hn, eq_self_iff_true,
                 nat.succ_add_eq_succ_add, forall_true_iff] } }
end

lemma enum_from_bdd_below (i : fin n) : m ≤ ((v.enum_from m).map prod.fst).nth i :=
by simp only [nth_map, nth_enum_from, zero_le, le_add_iff_nonneg_right]

lemma enum_from_bdd_above (i : fin n) : ((v.enum_from m).map prod.fst).nth i < m + n :=
by simpa only [nth_map, nth_enum_from, add_lt_add_iff_left] using i.property

#check enum_from_bdd_above v m
end enum_from

#check vector.map₂

def dmap {α β γ : Type*} (p : ℕ → β → Prop) (g : Π {k : ℕ}, vector α k → vector β k)
  (h : Π {k : ℕ}, ∀ (v : vector α k) i, p k ((g v).nth i))
  (f : Π {k : ℕ} (x : β), p k x → α → γ) : Π {n : ℕ} (v : vector α n), vector γ n
| 0       _ := nil
| (n + 1) v := (f ((g v).nth 0) (h v 0) (v.nth 0)) ::ᵥ dmap v.tail

def dmap' {α β γ : Type*} (g : Π {k : ℕ}, vector α k → vector β k) :
  Π {n : ℕ} (p : ℕ → β → Prop), (Π (v : vector α n) (i : fin n), p n ((g v).nth i)) →
  (Π {k : ℕ} (i : fin k), p n ((g v).nth i → α → γ) → vector α n → vector γ n
| 0       _ := nil
| (n + 1) v := (f ((g v).nth 0) (h v 0) (v.nth 0)) ::ᵥ dmap v.tail

#check @fin
#check list.range'

def dt : Π {α β : Type*} {n : ℕ} (f : vector α n → vector β n) (p : β → Prop)
         (h : Π (v : vector α n), ∀ (i : fin n), p ((f v).nth i)) (v : vector α n), vector β n
| _ _ n f p h := _

#check dt v m (enum_from_bdd_above v m)

#check @vector.map

#check @enum_from_bdd_above

#check @vector.dmap α ℕ (fin (m + n) × α) (λ n' x', x' < m + n')
  -- (λ k v, vector.map prod.fst (enum_from v m))
  (λ {n'} v, (v.enum_from m).map prod.fst)
  (λ n' v i, enum_from_bdd_above v m i)
  (λ n' ix h x', (⟨ix, by {convert h, }⟩, x))
  -- (λ k i h x, (_, x))
  n v

-- def enum_fin_from {α : Sort*} {n : ℕ} (v : vector α n) (m : ℕ) : vector (fin (n + m) × α) n :=
-- vector.dmap (λ


def enumerate_from {α : Type*} : Π {n} m : ℕ, vector α n → vector (fin (m + n) × α) n
| 0       _ _           := nil
| (n + 1) m v := (⟨m, (lt_add_iff_pos_right m).mpr nat.succ_pos'⟩, v.head) ::ᵥ
                           (map (prod.map fin.succ id) (enumerate_from m v.tail))

def enumerate {α : Type*} {n : ℕ} (v : vector α n) : vector (fin n × α) n :=
map (prod.map (fin.cast (zero_add n)) id) $ enumerate_from 0 v

def enumerate2d {α : Type*} : Π {n m : ℕ}, vector (vector α m) n → vector (vector (fin (n + m) × α) m) n
| 0       _       _ := nil
| (n + 1) 0       _ := repeat nil (n + 1)
| (n + 1) (m + 1) v := _
