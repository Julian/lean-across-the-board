import data.vector2
import utils.list

open vector

namespace vector

variables {α β γ : Type*} {n m : ℕ}
variables (v : vector α n) (vn : vector α 0) (vs : vector α (n + 1))
variables (x : α)

lemma map_map {f : α → β} {g : β → γ} : (v.map f).map g = v.map (g ∘ f) :=
by { apply vector.eq, simp only [to_list_map, list.map_map] }

@[simp] lemma to_list_nil' : vn.to_list = [] :=
begin
  have : vn = nil, by simp only [eq_iff_true_of_subsingleton],
  simp only [this, to_list_nil],
end

@[simp] lemma last_nil : (x ::ᵥ nil).last = x := rfl

@[simp] lemma last_cons : (x ::ᵥ vs).last = vs.last :=
by rw [←vector.cons_head_tail vs, last_def, last_def, ←fin.succ_last, nth_cons_succ]

lemma last_tail (v : vector α (n + 2)) : v.tail.last = v.last :=
by { rw ←vector.cons_head_tail v, simp only [last_cons, cons_tail] }

lemma to_list_tail : v.tail.to_list = v.to_list.tail :=
begin
  cases n,
  { simp only [list.tail_nil, to_list_nil'] },
  { rw ←cons_head_tail v,
    simp only [to_list_cons, cons_tail, list.tail_cons]}
end

protected def cast (h : n = m) : vector α n → vector α m :=
λ v, ⟨v.val, h ▸ v.property⟩

lemma cast_def (h : n = m) : v.cast h = ⟨v.to_list, h ▸ v.to_list_length⟩ := rfl

@[simp] lemma to_list_cast (h : n = m) :
  (v.cast h).to_list = v.to_list :=
by { simpa only }

@[simp] lemma cast_id {h : n = n} : v.cast h = v :=
by { apply vector.eq, simp only [to_list_cast] }

lemma cons_append (v : vector α n) (v' : vector α m) :
  x ::ᵥ (v.append v') = ((x ::ᵥ v).append v').cast (nat.succ_add_eq_succ_add _ _) :=
begin
  apply vector.eq,
  simp only [to_list_cons, list.cons_append, eq_self_iff_true,
             to_list_append, and_self, to_list_cast]
end

@[simp] lemma append_nil : vn.append v = v.cast (zero_add _).symm :=
begin
  apply vector.eq,
  simp [to_list_nil, list.nil_append, to_list_append, to_list_cast],
end

lemma append_cons (v : vector α n) (v' : vector α m) :
  (x ::ᵥ v).append v' = (x ::ᵥ (v.append v')).cast (nat.succ_add_eq_succ_add _ _).symm :=
begin
  apply vector.eq,
  simp only [to_list_cons, list.cons_append, eq_self_iff_true,
             to_list_append, and_self, to_list_cast]
end

def snoc : vector α (n + 1) :=
⟨v.to_list ++ [x], by simp only [list.length_append, list.length, to_list_length]⟩

lemma snoc_def : v.snoc x = ⟨v.to_list ++ [x],
                             by simp only [list.length_append, list.length, to_list_length]⟩ := rfl

@[simp] lemma snoc_nil : nil.snoc x = x ::ᵥ nil := rfl

@[simp] lemma snoc_nil' : vn.snoc x = x ::ᵥ vn :=
begin
  have : vn = nil, by simp only [eq_iff_true_of_subsingleton],
  simp only [this, snoc_nil],
end

@[simp] lemma to_list_snoc : (v.snoc x).to_list = v.to_list ++ [x] := rfl

lemma snoc_append (v : vector α n) (v' : vector α m) : (v.append v').snoc x = v.append (v'.snoc x) :=
begin
  induction n with n hn generalizing m x,
  { have : v = nil, by simp only [eq_iff_true_of_subsingleton],
    simpa only [append_nil] },
  { rw ←cons_head_tail v,
    apply vector.eq,
    simp only [to_list_snoc, list.append_assoc, to_list_append] },
end

lemma snoc_cons_comm (y : α) : (x ::ᵥ v).snoc y = x ::ᵥ (v.snoc y) :=
begin
  apply vector.eq,
  simp only [to_list_cons, list.cons_append,
             eq_self_iff_true, to_list_snoc, and_self],
end


def init : vector α (n - 1) :=
⟨v.to_list.init, by simp only [list.length_init, to_list_length]⟩

lemma init_def : v.init = ⟨v.to_list.init, by simp only [list.length_init, to_list_length]⟩ := rfl

lemma to_list_init : v.init.to_list = v.to_list.init :=
by simp only [init_def, to_list_mk]

@[simp] lemma init_nil : nil.init = @nil α := rfl

@[simp] lemma init_singleton : (x ::ᵥ nil).init = nil :=
by simp only [eq_iff_true_of_subsingleton]

@[simp] lemma init_cons : (x ::ᵥ vs).init = x ::ᵥ vs.init :=
begin
  induction n with n hn generalizing x,
  { rw ←cons_head_tail vs,
    simpa only [singleton_tail] },
  { apply vector.eq,
    rw ←cons_head_tail vs,
    simp only [hn, to_list_cons, to_list_init, list.init_cons, true_and, eq_self_iff_true],
    simp only [←to_list_cons, ←to_list_init, hn] },
end

lemma init_append (v : vector α n) (v' : vector α (m + 1)) :
  (v.append v').init = v.append v'.init :=
begin
  apply vector.eq,
  induction n with n hn generalizing m,
  { simp only [append_nil, to_list_init, list.nil_append, to_list_append,
               to_list_cast, to_list_nil'] },
  { rw [←cons_head_tail v, append_cons,
        to_list_init, to_list_cast, ←to_list_init],
    simp only [hn, to_list_cons, list.cons_append, eq_self_iff_true,
               to_list_append, and_self, init_cons] },
end

lemma init_eq_take : v.init = (v.take (n - 1)).cast (min_eq_left n.pred_le) :=
begin
  apply vector.eq,
  cases n,
  { simp only [to_list_nil'] },
  induction n with n hn,
  { simp only [to_list_nil'] },
  { rw ←cons_head_tail v,
    simp only [hn, to_list_cons, nat.succ_sub_succ_eq_sub, list.take,
               eq_self_iff_true, to_list_take, nat.sub_zero, and_self,
               to_list_cast, init_cons] },
end

lemma tail_init_comm : v.init.tail = v.tail.init :=
begin
  cases n,
  { simp only [eq_iff_true_of_subsingleton] },
  induction n with n hn,
  { simp only [eq_iff_true_of_subsingleton] },
  { rw ←cons_head_tail v,
    simp only [cons_tail, init_cons] }
end

@[simp] theorem snoc_init_last : vs.init.snoc vs.last = vs :=
begin
  induction n with n hn,
  { ext i,
    have hn : vs.init = nil := by simp only [eq_iff_true_of_subsingleton],
    have hi : i = 0 := by simp only [eq_iff_true_of_subsingleton],
    simpa only [hi, nth_cons_zero, snoc_nil'] },
  { rw ←cons_head_tail vs,
    simp only [snoc_cons_comm, hn, last_cons, init_cons] },
end

end vector
