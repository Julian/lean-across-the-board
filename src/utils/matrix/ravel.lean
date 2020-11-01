import data.matrix.notation
import tactic.unify_equations

variables {α : Type*} {n m : ℕ}

open matrix

namespace matrix

def ravel : Π {n m : ℕ}, (matrix (fin n) (fin m) α) → fin (n * m) → α
| _       0 _ i      := vec_empty i
| 0       m M ⟨i, h⟩ := vec_empty ⟨i, nat.zero_mul m ▸ h⟩
| (n + 1) m M i      := fin.append
                          (by rw [nat.succ_mul, add_comm])
                          (vec_head M) (ravel (vec_tail M)) i

lemma heqtest {α : Type*} {β : Π (x : α), Type*} {x y : α} (h : x = y) : β x = β y :=
begin
  exact congr_arg β h,
end

@[simp] lemma ravel_def_nil_row (M : matrix (fin n) (fin 0) α) :
  M.ravel = vec_empty := by { ext i, exact fin_zero_elim i }

@[simp] lemma ravel_def_nil_column (M : matrix (fin 0) (fin m) α) :
  M.ravel = (λ x, vec_empty (eq.mp (congr_arg _ (zero_mul m)) x)) :=
begin
  ext ⟨x, hx⟩,
  rw zero_mul at hx,
  exact absurd hx (not_lt_of_ge (nat.zero_le x)),
end

lemma ravel_def (M : matrix (fin (n + 1)) (fin (m + 1)) α) :
  M.ravel = fin.append (by rw [nat.succ_mul, add_comm]) M.vec_head (ravel M.vec_tail) := rfl

end matrix
