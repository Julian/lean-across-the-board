import data.list.zip
import data.vector2
import utils.vector

variables {α β : Type*} {n : ℕ}
variables (v : vector α n) (vn : vector α 0) (vs : vector α (n + 1))
variables (x : α)

open vector

namespace vector

section take

variable {k : ℕ}

@[simp] lemma take_zero : v.take 0 = nil :=
vector.eq _ _ (to_list_take v)

@[simp] lemma take_nil' : vn.take k = nil.cast (by simp) :=
vector.eq _ _ (by simp only [list.take_nil, to_list_take, to_list_cast, to_list_nil'])

@[simp] lemma take_nil : (@nil α).take k = nil.cast (by simp) :=
vector.eq _ _ (by simp only [list.take_nil, to_list_take, to_list_cast, to_list_nil'])

@[simp] lemma take_cons : (x::ᵥv).take (k + 1) = (x::ᵥ(v.take k)).cast (nat.min_succ_succ k n).symm :=
vector.eq _ _ (by simp only [to_list_cons, list.take, eq_self_iff_true, to_list_take, and_self, to_list_cast])

lemma take_succ : vs.take (k + 1) = (vs.head::ᵥvs.tail.take k).cast (nat.min_succ_succ k n).symm :=
begin
  rw [←cons_head_tail vs, take_cons],
  apply vector.eq,
  simp only [cons_head_tail, to_list_cast]
end

@[simp] lemma take_last : v.take n = v.cast (min_self n).symm :=
begin
  induction n with n hn,
  { have : v = nil := by simp only [eq_iff_true_of_subsingleton],
    simp only [this, take_nil] },
  { apply vector.eq,
    rw ←cons_head_tail v,
    simp only [take_succ, hn, cons_head, to_list_cons,
               cons_tail, eq_self_iff_true, and_self, to_list_cast] },
end

lemma map_take {f : α → β} : (v.take k).map f = (v.map f).take k :=
vector.eq _ _ (by simp only [list.map_take, to_list_map, to_list_take])

end take

section fold

def foldr (f : α → β → β) (b : β) : β := list.foldr f b v.to_list

variables (f : β → α → β) (b : β)

def foldl : β := list.foldl f b v.to_list

lemma foldl_def : v.foldl f b = list.foldl f b v.to_list := rfl

@[simp] lemma foldl_nil' : vn.foldl f b = b :=
begin
  have : vn = nil, by simp only [eq_iff_true_of_subsingleton],
  simpa only [this]
end

@[simp] lemma foldl_nil : nil.foldl f b = b := rfl

@[simp] lemma foldl_list_nil : foldl (⟨@list.nil α, by simp⟩ : vector α 0) f b = b := rfl

@[simp] lemma foldl_of_cast {m : ℕ} {h : n = m} : (v.cast h).foldl f b = v.foldl f b := rfl

@[simp] lemma foldl_cons : (x::ᵥv).foldl f b = v.foldl f (f b x) :=
by simp only [foldl_def, to_list_cons, list.foldl]

lemma foldl_mul [monoid α] : v.foldl (*) x = x * (v.foldl (*) (1 : α)) :=
begin
  induction n with n hn generalizing x,
  { simp only [map_cons, foldl_nil', mul_one, map_nil] },
  { rw [←cons_head_tail v, foldl_cons, foldl_cons,
        hn, hn _ (1 * _), mul_assoc, one_mul] }
end

lemma foldl_add [add_monoid α] : v.foldl (+) x = x + (v.foldl (+) (0 : α)) :=
begin
  induction n with n hn generalizing x,
  { simp only [map_cons, foldl_nil', add_zero, map_nil] },
  { rw [←cons_head_tail v, foldl_cons, foldl_cons,
        hn, hn _ (0 + _), add_assoc, zero_add] }
end

lemma nth_scanl_eq_foldl_of_take (i : fin (n + 1)) : (v.scanl f b).nth i = (v.take i).foldl f b :=
begin
  induction n with n hn generalizing b,
  { simpa only [scanl_nil', nth_cons_nil, take_nil'] },
  { refine fin.cases _ _ i,
    { simp only [nth_zero, scanl_head, foldl_nil'] },
    { intros i',
      rw [←cons_head_tail v, fin.coe_succ],
      simp only [fin.coe_succ, hn, foldl_cons, foldl_of_cast,
                  scanl_cons, take_cons, nth_cons_succ] } },
end

@[simp] lemma scanl_last : (v.scanl f b).last = v.foldl f b :=
begin
  rw [last_def, nth_scanl_eq_foldl_of_take, fin.coe_last],
  simp only [foldl_of_cast, take_last],
end

end fold

section zip

variables (v' : vector β n) (vn' : vector β 0) (vs' : vector β (n + 1)) (x' : β)

def zip : vector (α × β) n :=
⟨v.to_list.zip v'.to_list, by simp only [list.length_zip, min_eq_right, to_list_length]⟩

lemma zip_def : v.zip v' =
  ⟨v.to_list.zip v'.to_list, by simp only [list.length_zip, min_eq_right, to_list_length]⟩ := rfl

@[simp] lemma to_list_zip : (v.zip v').to_list = v.to_list.zip v'.to_list := rfl

@[simp] lemma map_fst_zip : (v.zip v').map prod.fst = v :=
vector.eq _ _ (by simp only [list.map_fst_zip, to_list_map, to_list_zip, to_list_length])

@[simp] lemma map_snd_zip : (v.zip v').map prod.snd = v' :=
vector.eq _ _ (by simp only [list.map_snd_zip, to_list_map, to_list_zip, to_list_length])

@[simp] lemma map_zip {γ δ : Type*} (f : α → γ) (g : β → δ) :
  (v.zip v').map (prod.map f g) = (v.map f).zip (v'.map g) :=
vector.eq _ _ (by simp only [list.zip_map, to_list_map, to_list_zip])

@[simp] lemma zip_nil : vn.zip vn' = nil := by simp only [eq_iff_true_of_subsingleton]

lemma zip_cons_head : ((x::ᵥv).zip (x'::ᵥv')).head = (x, x') :=
by simpa only [zip_def, to_list_cons]

@[simp] lemma zip_head : (vs.zip vs').head = (vs.head, vs'.head) :=
by rw [←cons_head_tail vs, ←cons_head_tail vs', zip_cons_head, cons_head, cons_head]

@[simp] lemma nth_zip (i : fin n) : (v.zip v').nth i = (v.nth i, v'.nth i) :=
begin
  rw [←option.some.inj_eq, nth_eq_nth_le, nth_eq_nth_le, nth_eq_nth_le, ←list.nth_le_nth,
      to_list_zip, list.nth_le_nth, list.nth_le_zip],
  { simp only [to_list_length] },
  { simpa only [list.length_zip, min_eq_right, to_list_length] using i.property }
end

@[simp] lemma zip_cons : ((x::ᵥv).zip (x'::ᵥv')) = (x, x') ::ᵥ v.zip v' :=
begin
  apply ext,
  apply fin.induction,
  { simp only [fin.coe_zero, nth_cons_zero, nth_zip] },
  { intros,
    simp only [nth_zip, nth_map, prod.map_mk, nth_cons_succ, id.def, fin.coe_succ] }
end

end zip

section accum

variables {σ : Type} (f : α → σ → σ × β) (s : σ)

def map_accuml : σ × vector β n :=
prod.map id reverse $ map_accumr f v.reverse s

lemma map_accuml_def : v.map_accuml f s = (v.reverse.map_accumr f s).map id reverse := rfl

lemma map_accuml_fst : (v.map_accuml f s).fst = (v.reverse.map_accumr f s).fst := rfl

lemma map_accuml_snd : (v.map_accuml f s).snd = (v.reverse.map_accumr f s).snd.reverse := rfl

lemma reverse_map_accuml : (v.map_accuml f s).map id reverse = v.reverse.map_accumr f s :=
by simp only [map_accuml_def, prod.mk.eta, reverse_reverse, id.def, prod_map]

end accum

end vector
