import data.vector2

/-!

Helpers that don't currently fit elsewhere...

-/

def vector.scanr {α β : Type*} {n : ℕ} (f : α → β → β) (v : vector α n) (b : β) : vector β n :=
prod.snd ((vector.map_accumr (λ x acc, (f x acc, f x acc)) v b))

def vector.scanl {α β : Type*} {n : ℕ} (f : β → α → β) (b : β) (v : vector α n) : vector β n :=
vector.reverse (vector.scanr (λ acc x, f x acc) (vector.reverse v) b)

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
