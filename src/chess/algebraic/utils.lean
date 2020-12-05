import data.sum

instance has_repr_sum {α β : Type*} [has_repr α] [has_repr β] : has_repr (α ⊕ β) :=
⟨sum.elim (λ x, "sum.inl " ++ repr x) (λ x, "sum.inr " ++ repr x)⟩

def asum {α : Type*} {m : Type* → Type*} [alternative m] (xs : list (m α)) : m α :=
xs.foldl (<|>) failure
