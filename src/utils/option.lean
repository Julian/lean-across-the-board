import data.option.basic
import data.list

open option

namespace option

/--
Composing an `option.map` with another `option.map` is equal to
a single `option.map` of a composition of functions, fully applied.
This is the reverse direction of `option.comp_map`.
-/
@[simp] lemma map_map {α β γ : Type*}
  (h : β → γ) (g : α → β) (x : option α) :
  option.map h (option.map g x) = option.map (h ∘ g) x :=
by { cases x; simp only [map_none', map_some'] }

/--
A single `option.map` of a composition of functions is equal to
composing an `option.map` with another `option.map`, fully applied.
This is the reverse direction of `option.map_map`.
-/
lemma comp_map {α β γ : Type*}
  (h : β → γ) (g : α → β) (x : option α) :
  option.map (h ∘ g) x = option.map h (option.map g x) := (map_map _ _ _).symm

/--
Composing an `option.map` with another `option.map` is equal to a single `option.map` of composed functions.
-/
@[simp] lemma map_comp_map {α β γ : Type*} (f : α → β) (g : β → γ) :
  option.map g ∘ option.map f = option.map (g ∘ f) :=
by { ext x, rw comp_map }

@[simp] lemma map_eq_map {α β : Type*} {f : α → β} : (<$>) f = option.map f := rfl

lemma map_congr {α β : Type*} {f g : α → β} {x : option α} (h : ∀ a ∈ x, f a = g a) :
  option.map f x = option.map g x :=
by { cases x; simp only [map_none', map_some', h, mem_def] }

@[simp] lemma map_id'' {α : Type*} : @option.map α α (λ x, x) = id :=
by { funext x, cases x; refl }

@[simp] lemma map_of_id {α β : Type*} {f : α → β} :
  (λ (a : option α), option.map f (id a)) = option.map f :=
by { funext x, cases x; refl }

@[simp] lemma map_eq_none_iff {α β : Type*} {f : α → β} {x : option α} :
  x.map f = none ↔ x = none :=
by { cases x; simp only [map_none', map_some', eq_self_iff_true] }

lemma subtype_exists {α β : Type*} {p : β → Prop} {f : α → option (subtype p) } {i : subtype p} :
  (∃ x, f x = some i) ↔ ∃ (x : α), (f x).map (subtype.val) = some i.val :=
begin
  split,
  { rintro ⟨x, h⟩,
    exact ⟨x, h.symm ▸ rfl⟩ },
  { rintro ⟨x, h⟩,
    obtain ⟨y, hy, hs⟩ := map_eq_some'.mp h,
    use x,
    rw [hy, some_inj],
    exact subtype.eq hs },
end

lemma subtype_exists' {α β : Type*} {p : β → Prop} {f : α → option (subtype p) } {a : α} :
  (∃ i, f a = some i) ↔ ∃ (i : β), (f a).map (subtype.val) = some i :=
begin
  split,
  { rintro ⟨x, h⟩,
    exact ⟨x, h.symm ▸ rfl⟩ },
  { rintro ⟨x, h⟩,
    obtain ⟨y, hy, hs⟩ := map_eq_some'.mp h,
    use y,
    rw [hy, some_inj] },
end

lemma subtype_exists_unique {α β : Type*} {p : β → Prop} {f : α → option (subtype p) } {i : subtype p} :
  (∃! x, f x = some i) ↔ ∃! (x : α), (f x).map (subtype.val) = some i.val :=
begin
  split,
  { rintro ⟨x, h, h'⟩,
    use x,
    split,
    { simp only [h, map_some'] },
    { intros y hy,
      apply h',
      simp only [exists_prop, exists_and_distrib_right, exists_eq_right, subtype.coe_eta,
                 map_eq_some', subtype.exists, subtype.coe_mk, subtype.val_eq_coe] at hy,
      exact hy.right } },
  { rintro ⟨x, h, h'⟩,
    obtain ⟨y, hy, hs⟩ := map_eq_some'.mp h,
    use x,
    split,
    { simpa only [hy] using subtype.eq hs },
    { intros z hz,
      apply h',
      simp only [hz, map_some'] } },
end

lemma subtype_exists_unique' {α β : Type*} {p : β → Prop} {f : α → option (subtype p) } {a : α} :
  (∃! i, f a = some i) ↔ ∃! (i : β), (f a).map (subtype.val) = some i :=
begin
  split,
  { rintro ⟨x, h, h'⟩,
    use x,
    split,
    { simp only [h, map_some', subtype.val_eq_coe] },
    { intros y hy,
      simp only [exists_and_distrib_right, exists_eq_right, subtype.forall, map_eq_some',
                 subtype.exists, subtype.coe_mk] at h' hy,
      obtain ⟨py, hy⟩ := hy,
      specialize h' y py hy,
      simp only [←h', subtype.coe_mk] } },
  { rintro ⟨x, h, h'⟩,
    obtain ⟨y, hy, hs⟩ := map_eq_some'.mp h,
    simp only [exists_and_distrib_right, exists_eq_right, subtype.forall, map_eq_some',
                subtype.exists, subtype.coe_mk] at h' hy h,
    obtain ⟨px, hx⟩ := h,
    use ⟨x, px⟩,
    split,
    { simpa only using hx },
    { intros z hz,
      rw ←option.some_inj,
      simp only [←hz, ←hx]} },
end

section bind

@[simp] def join {α : Type*} : option (option α) → option α
| none            := none
| (some (none))   := none
| (some (some x)) := some x

@[simp] lemma join_eq_some {α : Type*} {x : option (option α)} {a : α} :
  x.join = some a ↔ x = some (some a) :=
by { rcases x with _ | _ | x; simp }

@[simp] lemma join_ne_none {α : Type*} {x : option (option α)} :
  x.join ≠ none ↔ ∃ z, x = some (some z) :=
by { rcases x with _ | _ | x; simp }

@[simp] lemma join_ne_none' {α : Type*} {x : option (option α)} :
  ¬(x.join = none) ↔ ∃ z, x = some (some z) :=
by { rcases x with _ | _ | x; simp }

lemma bind_eq_bind {α β : Type*} {f : α → option β} {x : option α} :
  x.bind f = x >>= f := rfl

lemma bind_map_comm {α β : Type*} {x : option (option α) } {f : α → β} :
  x >>= option.map f = x.map (option.map f) >>= id :=
by { cases x; simp }

@[simp] lemma bind_id_eq_join {α : Type*} {x : option (option α)} :
  x >>= id = x.join :=
by { rcases x with _ | _ | x; simp }

lemma join_map_eq_map_join {α β : Type*} {f : α → β} {x : option (option α)} :
  (x.map (option.map f)).join = x.join.map f :=
by { rcases x with _ | _ | x; simp }

@[simp] def pbind {α β : Type*} : Π (x : option α), (Π (a : α), a ∈ x → option β) → option β
| none _       := none
| x@(some a) f := f a rfl

lemma pbind_eq_none {α β : Type*} {x : option α} {f : Π (a : α), a ∈ x → option β}
  (h' : ∀ a ∈ x, f a H = none → x = none) :
  x.pbind f = none ↔ x = none :=
begin
  cases x,
  { simp },
  { simp only [pbind, iff_false],
    intro h,
    specialize h' x rfl h,
    contradiction }
end

lemma pbind_eq_some {α β : Type*} {x : option α} {f : Π (a : α), a ∈ x → option β} {y : β}
   :
  x.pbind f = some y ↔ ∃ (z ∈ x), f z H = some y :=
begin
  cases x,
  { simp },
  { simp only [pbind],
    split,
    { intro h,
      use x,
      simpa only [mem_def, exists_prop_of_true] using h },
    { rintro ⟨z, H, hz⟩,
      simp only [mem_def] at H,
      simpa only [H] using hz } }
end

@[simp] lemma pbind_eq_bind {α β : Type*} {x : option α} {f : α → option β} :
  x.pbind (λ a _, f a) = x.bind f :=
by { cases x; simp only [pbind, none_bind', some_bind'] }

lemma map_bind {α β γ : Type*} (x : option α) {g : α → option β} {f : β → γ} :
  option.map f (x >>= g) = (x >>= λa, option.map f (g a)) :=
by rw [←map_eq_map, ←bind_pure_comp_eq_map,is_lawful_monad.bind_assoc]; simp [bind_pure_comp_eq_map]

lemma map_pbind {α β γ : Type*} (x : option α) {f : β → γ} {g : Π a, a ∈ x → option β} :
  option.map f (x.pbind g) = (x.pbind (λ a H, option.map f (g a H))) :=
by { cases x; simp only [pbind, map_none'] }

lemma mem_map_of_mem {α β : Type*} {a : α} {x : option α} (g : α → β) (h : a ∈ x) : g a ∈ x.map g :=
mem_def.mpr ((mem_def.mp h).symm ▸ map_some')

lemma mem_of_mem_join {α : Type*} {a : α} {x : option (option α)} (h : a ∈ x.join) : some a ∈ x :=
mem_def.mpr ((mem_def.mp h).symm ▸ join_eq_some.mp h)

lemma pbind_map {α β γ : Type*} (x : option α) {f : α → β} {g : Π (b : β), b ∈ x.map f → option γ} :
  pbind (option.map f x) g = x.pbind (λ a h, g (f a) (mem_map_of_mem _ h)) :=
by { cases x; refl }

end bind

section pmap

/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f x h` is essentially the same as `map f x`
  but is defined only when all members of `x` satisfy `p`, using the proof
  to apply `f`. -/
@[simp] def pmap {α β : Type*} {p : α → Prop} (f : Π (a : α), p a → β) :
  Π x : option α, (∀ a ∈ x, p a) → option β
| none     _ := none
| (some a) H := some (f a (H a (mem_def.mpr rfl)))

@[simp] def pmap_with {α β : Type*} {p : α → Prop} (f : Π (a : α), p a → β) (g : option β) :
  Π x : option α, (∀ a ∈ x, p a) → option β
| none     _ := g
| (some a) H := some (f a (H a (mem_def.mpr rfl)))

variables {α β γ : Type*} {p : α → Prop} (f : Π (a : α), p a → β)
variable {f}

@[simp] lemma pmap_none {H} : pmap f (@none α) H = none := rfl

@[simp] lemma pmap_some {x : α} {h : p x} : pmap f (some x) = λ _, some (f x h) := rfl

@[simp] lemma pmap_eq_none_iff {x : option α} {h} :
  pmap f x h = none ↔ x = none :=
by { cases x; simp }

@[simp] lemma pmap_eq_some_iff {x : option α} {hf} {y : β} :
  pmap f x hf = some y ↔ ∃ (a : α) (H : x = some a), f a (hf a H) = y :=
begin
  cases x,
  { simp only [not_mem_none, exists_false, pmap, not_false_iff, exists_prop_of_false] },
  { split,
    { intro h,
      simp only [pmap] at h,
      exact ⟨x, rfl, h⟩ },
    { rintro ⟨a, H, rfl⟩,
      simp only [mem_def] at H,
      simp only [H, pmap] } }
end

section pmap_with

variable {g : option β}

lemma pmap_with_none' {H} : pmap_with f g (@none α) H = g := rfl

@[simp] lemma pmap_with_none : pmap_with f g (@none α) = λ _, g := rfl

@[simp] lemma pmap_with_some {x : α} {h : p x} : pmap_with f g (some x) = λ _, f x h := rfl

end pmap_with

-- lemma mem_map_of_pmem {a : α} {x : option α} (g : α → β) (h : a ∈ x) : g a ∈ pmap g x H :=
-- mem_def.mpr ((mem_def.mp h).symm ▸ map_some')

lemma pmap_map (g : γ → α) (x : option γ) (H) :
  pmap f (x.map g) H = pmap (λ a h, f (g a) h) x (λ a h, H _ (mem_map_of_mem _ h)) :=
by { cases x; simp only [map_none', map_some', pmap] }

lemma map_pmap (g : β → γ) (f : Π a, p a → β) (x H) :
  option.map g (pmap f x H) = pmap (λ a h, g (f a h)) x H :=
by { cases x; simp only [map_none', map_some', pmap] }

@[simp] lemma pmap_eq_map (p : α → Prop) (f : α → β) (x : option α) (H) :
  @pmap _ _ p (λ a _, f a) x H = option.map f x :=
by { cases x; simp only [map_none', map_some', pmap] }

lemma pmap_bind {α β γ : Type*} (x : option α) {g : α → option β} {p : β → Prop} {f : Π b, p b → γ}
  (H) (H' : ∀ (a : α) b ∈ g a, b ∈ x >>= g) :
  pmap f (x >>= g) H = (x >>= λa, pmap f (g a) (λ b h, H _ (H' a _ h))) :=
by { cases x; simp only [pmap, none_bind, some_bind] }

lemma bind_pmap {α β γ : Type*} (x : option α) {p : α → Prop} {f : Π a, p a → β} {g : β → option γ} (H) :
  (pmap f x H) >>= g = x.pbind (λ a h, g (f a (H _ h))) :=
by { cases x; simp only [pmap, none_bind, some_bind, pbind] }

@[simp] lemma join_pmap_eq_pmap_join {f : Π a, p a → β} {x : option (option α)} (H) :
  (pmap (pmap f) x H).join = pmap f x.join (λ a h, H (some a) (mem_of_mem_join h) _ rfl) :=
by { rcases x with _ | _ | x; simp }

end pmap

end option
