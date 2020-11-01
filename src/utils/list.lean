import data.list.range
import data.list.zip

open list

namespace list

section list

variables {α β : Type*} (l : list α) (l' : list β) (x : α) (x' : β)

@[simp] lemma init_cons (y : α) :
  (x :: y :: l).init = x :: (y :: l).init :=
by simp only [init, true_and, eq_self_iff_true]

@[simp] lemma nth_le_pmap {p : α → Prop} (f : Π a, p a → β) :
  ∀ l n h hl, nth_le (pmap f l h) n hl = f (nth_le l n (by simpa only [length_pmap] using hl))
                                           (h _ (nth_le_mem _ _ _))
| []       n     h hl := by simpa only [n.not_lt_zero, length, pmap] using hl
| (a :: l) 0     h hl := rfl
| (a :: l) (n+1) h hl := nth_le_pmap l _ _ _

@[simp] lemma nth_le_fin_range {n : ℕ} {i : ℕ} (h) :
  (fin_range n).nth_le i h = ⟨i, length_fin_range n ▸ h⟩ :=
by simp [fin_range]

@[simp] lemma nth_le_range' {n m} (i) (H : i < (range' n m).length) :
  nth_le (range' n m) i H = n + i :=
option.some.inj $ by rw [← nth_le_nth _, nth_range' _ (by simpa using H)]

variables {l l'}

lemma nth_le_zip {i : ℕ} (h : i < (l.zip l').length) (hl : l.length = l'.length) :
  (l.zip l').nth_le i h =
    (l.nth_le i ((@lt_min_iff _ _ i l.length l'.length).mp (list.length_zip l l' ▸ h)).left,
    l'.nth_le i ((@lt_min_iff _ _ i l.length l'.length).mp (list.length_zip l l' ▸ h)).right) :=
begin
  rw [length_zip, lt_min_iff] at h,
  rw [←option.some.inj_eq, ←nth_le_nth, nth_zip_eq_some, nth_le_nth h.left, nth_le_nth h.right],
  simp only [eq_self_iff_true, and_self]
end

lemma zip_of_prod {lp : list (α × β)} (hl : lp.map prod.fst = l) (hr : lp.map prod.snd = l') :
  lp = l.zip l' :=
by rw [←hl, ←hr, ←zip_unzip lp, ←unzip_left, ←unzip_right, zip_unzip, zip_unzip]

variables (l l')

lemma map_prod_left_eq_zip (f : α → β) : l.map (λ x, (x, f x)) = l.zip (l.map f) :=
by { rw ←zip_map', congr, convert map_id _ }

lemma map_prod_right_eq_zip (f : α → β) : l.map (λ x, (f x, x)) = (l.map f).zip l :=
by { rw ←zip_map', congr, convert map_id _ }

lemma enum_eq_zip_range : l.enum = (range l.length).zip l :=
zip_of_prod (enum_map_fst _) (enum_map_snd _)

lemma enum_from_eq_zip_range' {n : ℕ} : l.enum_from n = (range' n l.length).zip l :=
zip_of_prod (enum_from_map_fst _ _) (enum_from_map_snd _ _)

end list

end list
