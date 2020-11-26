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

section bind

lemma bind_eq_bind {α β : Type*} {f : α → option β} {x : option α} :
  x.bind f = x >>= f := rfl

lemma bind_map_comm {α β : Type*} {x : option (option α) } {f : α → β} :
  x >>= option.map f = x.map (option.map f) >>= id :=
by { cases x; simp }

end bind

section pmap

variables {α β γ : Type*} {p : α → Prop} (f : Π (a : α), p a → β)

/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f x h` is essentially the same as `map f x`
  but is defined only when all members of `x` satisfy `p`, using the proof
  to apply `f`. -/
@[simp] def pmap :
  Π x : option α, (∀ a ∈ x, p a) → option β
| none     _ := none
| (some a) H := some (f a (H a (mem_def.mpr rfl)))

@[simp] def pmap_with (g : option β) :
  Π x : option α, (∀ a ∈ x, p a) → option β
| none     _ := g
| (some a) H := some (f a (H a (mem_def.mpr rfl)))

variable {f}

@[simp] lemma pmap_none {H} : pmap f (@none α) H = none := rfl

@[simp] lemma pmap_some {x : α} {h : p x} : pmap f (some x) = λ _, f x h := rfl

@[simp] lemma pmap_eq_none_iff {x : option α} {h} :
  pmap f x h = none ↔ x = none :=
by { cases x; simp }

@[simp] lemma pmap_eq_some_iff {x : option α} {hf} {y : β} :
  pmap f x hf = some y ↔ ∃ (a : α) (H : a ∈ x), f a (hf a H) = y :=
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

lemma mem_map_of_mem {a : α} {x : option α} (g : α → β) (h : a ∈ x) : g a ∈ x.map g :=
mem_def.mpr ((mem_def.mp h).symm ▸ map_some')

lemma pmap_map (g : γ → α) (x : option γ) (H) :
  pmap f (x.map g) H = pmap (λ a h, f (g a) h) x (λ a h, H _ (mem_map_of_mem _ h)) :=
by { cases x; simp only [map_none', map_some', pmap] }

lemma map_pmap (g : β → γ) (f : Π a, p a → β) (x H) :
  option.map g (pmap f x H) = pmap (λ a h, g (f a h)) x H :=
by { cases x; simp only [map_none', map_some', pmap] }

@[simp] lemma pmap_eq_map (p : α → Prop) (f : α → β) (x : option α) (H) :
  @pmap _ _ p (λ a _, f a) x H = option.map f x :=
by { cases x; simp only [map_none', map_some', pmap] }

end pmap

end option
