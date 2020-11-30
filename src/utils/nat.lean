import data.nat.basic

open nat

namespace nat

attribute [simp] succ_le_succ_iff

@[simp] lemma succ_lt_succ_iff {n m : ℕ} : n.succ < m.succ ↔ n < m :=
⟨lt_of_succ_lt_succ, succ_lt_succ⟩

end nat
