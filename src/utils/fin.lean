import data.fin

namespace fin

def add_of_cast_add {n : ℕ} (k : ℕ) (i : fin n) : fin (n + k) :=
⟨k, show k < n + k, from
  (eq_or_lt_of_le (nat.zero_le n)).elim (λ h, by { subst h, exact fin_zero_elim i }) nat.lt_add_of_pos_left
⟩ + fin.cast_add k i

lemma add_of_cast_add_def {n : ℕ} (k : ℕ) (i : fin n) : add_of_cast_add k i =
  ⟨k, show k < n + k, from
    (eq_or_lt_of_le (nat.zero_le n)).elim (λ h, by { subst h, exact fin_zero_elim i }) nat.lt_add_of_pos_left
  ⟩ + fin.cast_add k i := rfl

lemma add_of_cast_add_of_succ {n : ℕ} (k : ℕ) (i : fin n) :
  add_of_cast_add (k + 1) i = fin.succ (add_of_cast_add k i) :=
begin
  sorry
end

end fin
