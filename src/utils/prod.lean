import data.prod

open prod

namespace prod

lemma comp_map {α β γ δ ε ζ : Type*}
  (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) :
  prod.map g g' ∘ prod.map f f' = prod.map (g ∘ f) (g' ∘ f') := rfl

end prod
