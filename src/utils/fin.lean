import data.fin

open fin

namespace fin

variables {n m k : ℕ}

@[simp] lemma cast_trans (h : n = m) (h' : m = k) {i : fin n} :
  (i.cast h).cast h' = i.cast (eq.trans h h') := rfl

@[simp] lemma cast_id {h : n = n} {i : fin n} : i.cast h = i :=
by { ext, refl }

end fin
