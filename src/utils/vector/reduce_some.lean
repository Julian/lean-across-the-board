import utils.vector.filter
import utils.vector.enum

variables {α : Type*} {n m : ℕ} (v : vector (option α) n)

def vector.count_some : ℕ :=
v.filter_count (λ x, option.is_some x)

lemma vector.count_some_def :
  v.count_some = v.filter_count (λ x, option.is_some x) := rfl

def vector.filter_some (hm : v.count_some = m) :
  vector (option α) m :=
v.filter (λ x, option.is_some x) hm

lemma vector.filter_some_pred (hm : v.count_some = m) :
  ∀ i, ((v.filter_some hm).nth i).is_some :=
vector.filter_valid _ hm

def vector.reduce_some (hm : v.count_some = m) :
  vector α m :=
vector.of_fn (λ i, option.get ((v.filter_some_pred hm) i))
