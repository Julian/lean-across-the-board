import data.vector2
import data.list.range
import utils.fin
import utils.list
import utils.prod
import utils.vector

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

@[simp] lemma nth_enum (i : fin n) : v.enum.nth i = (i, v.nth i) :=
by simp only [enum_def, nth_of_fn]

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

@[simp] lemma enum_cons_head' : (x ::ᵥ v).enum'.head = (0, x) :=
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

@[simp] lemma enum_cons' : (x ::ᵥ v).enum' = (0, x) ::ᵥ v.enum'.map (prod.map ((+) 1) id) :=
begin
  apply ext,
  intro i,
  apply fin.induction_on i,
  { simp only [fin.coe_zero, nth_cons_zero, nth_enum'] },
  { simp only [fin.coe_succ, nth_enum', eq_self_iff_true, nth_map,
               prod.map_mk, forall_true_iff, nth_cons_succ, id.def, add_comm] }
end

lemma enum_bdd_below' (i : fin n) : 0 ≤ (v.enum'.map prod.fst).nth i :=
by simp only [zero_le]

lemma enum_bdd_above' (i : fin n) : (v.enum'.map prod.fst).nth i < n :=
by simpa only [nth_map, nth_enum'] using i.property

lemma enum_eq_pmap_enum' := v.enum = pmap _ _ _

section enum_from

variable (k : ℕ)

def enum_from : vector (fin (n + k) × α) n :=
of_fn (λ i, (i.add_of_cast_add k, v.nth i))

lemma enum_from_def : v.enum_from k = of_fn (λ i, (i.add_of_cast_add k, v.nth i)) := rfl

lemma to_list_enum_from : (v.enum_from k).to_list =
  list.of_fn (λ i, (fin.add_of_cast_add k i, v.nth i)) :=
by simp only [enum_from_def, to_list_of_fn]

lemma to_list_enum_from_of_zip : (v.enum_from k).to_list =
  list.zip (list.map (fin.add_of_cast_add k) (list.fin_range n)) v.to_list :=
begin
  simp_rw [to_list_enum_from, list.of_fn_eq_map, ←list.zip_map'],
  congr,
  apply list.ext_le,
  { simp only [list.length_fin_range, list.length_map, to_list_length] },
  { intros i hm h,
    simp only [list.nth_le_fin_range, list.nth_le_map', nth_eq_nth_le] },
end

@[simp] lemma nth_enum_from (i : fin n) : (v.enum_from k).nth i =
  (fin.add_of_cast_add k i, v.nth i) :=
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

@[simp] lemma enum_from_cons_head' : ((x ::ᵥ v).enum_from' k).head = (k, x) :=
by simp only [enum_from_eq_enum_add', map_cons, cons_head, add_zero,
              id.def, enum_cons', prod.map_mk]

@[simp] lemma nth_enum_from' (i : fin n) : (v.enum_from' k).nth i = (k + i, v.nth i) :=
by simp only [enum_from_eq_enum_add', id.def, nth_enum', nth_map, prod.map_mk]

@[simp] lemma enum_from_cons' : ((x ::ᵥ v).enum_from' k) =
  (k, x) ::ᵥ (v.enum_from' (k + 1)) :=
begin
  have : ∀ {x y : ℕ}, has_add.add x ∘ has_add.add y = has_add.add (x + y),
    { intros, ext, rw add_assoc },
  simp only [enum_from_eq_enum_add', map_cons, map_map, prod.comp_map, add_zero,
             id.def, function.comp.right_id, enum_cons', prod.map_mk, this]
end

lemma enum_from_bdd_below' (i : fin n) : k ≤ ((v.enum_from' k).map prod.fst).nth i :=
by simp only [enum_from_eq_enum_add', nth_enum', zero_le,
              le_add_iff_nonneg_right, nth_map, prod.map_mk]

lemma enum_from_bdd_above' (i : fin n) : ((v.enum_from' k).map prod.fst).nth i < n + k :=
begin
  simp only [enum_from_eq_enum_add', nth_enum', nth_map, prod.map_mk],
  rw [add_comm, add_lt_add_iff_right],
  exact i.property
end

end enum_from

end enum

end vector
