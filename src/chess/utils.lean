import data.vector2

/-!

Helpers that don't currently fit elsewhere...

-/

section scan

variables
variable {n : ℕ}

def vector.scanr {α β : Type*} (f : α → β → β) (b : β) (v : vector α n) : vector β n :=
prod.snd ((vector.map_accumr (λ x acc, (f x acc, f x acc)) v b))

def vector.scanl {α β : Type*} (f : β → α → β) (b : β) (v : vector α n) : vector β n :=
vector.reverse (vector.scanr (λ acc x, f x acc) b (vector.reverse v))

@[elab_as_eliminator] protected lemma vector.scanl.induction_on
  {α β : Type*} {n : ℕ}
  {P : β → Prop}
  (f : β → α → β)
  (b : β)
  (v : vector α n)
  (h_b: P b)
  (h_ih: ∀ y : β, ∀ x : α, P y → P (f y x)) :
    ∀ e : fin n, P ((vector.scanl f b v).nth e) := begin
  sorry,
end

end scan

-- For `playfield`s, the piece type.
variables (K : Type*)
variables [has_repr K]

namespace chess.utils

/--
An auxiliary wrapper for `option K` that allows for overriding the `has_repr` instance
for `option`, and rather, output just the value in the `some` and a custom provided
`string` for `none`.
-/
structure option_wrapper :=
(val : option K)
(none_s : string)

instance wrapped_option_repr : has_repr (option_wrapper K) :=
⟨λ ⟨val, s⟩, (option.map has_repr.repr val).get_or_else s⟩

variables {K}
/--
Construct an `option_wrapper` term from a provided `option K` and the `string`
that will override the `has_repr.repr` for `none`.
-/
def option_wrap (val : option K) (none_s : string) : option_wrapper K := ⟨val, none_s⟩

end chess.utils
