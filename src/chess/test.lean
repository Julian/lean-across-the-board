def node := ℕ×ℕ

inductive back_walk (s : node) : ℕ → node → Type
| start : back_walk 0 s
| d : Π {n x y : ℕ}, back_walk n ⟨ x, y ⟩ → back_walk n ⟨ x+1, y ⟩
| r : Π {n x y : ℕ}, back_walk n ⟨ x, y ⟩ → back_walk n ⟨ x, y+1 ⟩
| l : Π {n x y : ℕ}, back_walk n ⟨ x+1, y ⟩ → back_walk (n+1) ⟨ x, y ⟩
| u : Π {n x y : ℕ}, back_walk n ⟨ x, y+1 ⟩ → back_walk (n+1) ⟨ x, y ⟩

open back_walk

instance {x y x' y' n : ℕ} : has_repr (back_walk ⟨x, y⟩ n ⟨x', y'⟩) :=
⟨λ _, string.intercalate ", " ["end: " ++ repr (x, y), "steps: " ++ repr n, "start: " ++ repr (x', y')]⟩

#eval (start : back_walk (5,5) _ _).u.d.l.d.l.d.r
/-
end: (5, 5), steps: 3, start: (6, 5)
-/
