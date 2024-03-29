import chess.utils
import data.matrix.notation
import data.set.finite

/-!

# Definitions and theorems about the chess board field

## Summary

The field on which chess pieces are placed is a 2D plane, where each
position corresponds to a piece index. This is because we think of
defining pieces and moves, usually, by indicating which position
they are at, and which position they are moved to.

## Main definitions

1. The playfield itself (`playfield`)
2. Conversion from a `matrix` of (possibly) occupied spaces to a `playfield`
3. Moving a piece by switching the indices at two specified positions using `move_piece`
4. Making a sequence of moves at once using `move_sequence`

## Implementation details

1. The `playfield` type itself has no requirements to be finite in any dimension,
or that the indices used are finite. We represent the actual index wrapped by
`option`, such that the empty square can be an `option.none`. The playfield definition
wraps the two types used to define the dimensions of the board into a pair.

2. In the current implementation, the way to construct a `playfield` is to provide
a matrix. This limits the `playfield` to a finite 2D plane. Another possible implementation
is of a "sparse matrix", where for each index, we can look up where the piece is.
This now allows for an infinite playfield, but still complicates using infinite pieces.
For now, the closely-tied `matrix` definition makes `playfield` a light type wrapper
on top of `matrix`, i.e. a function of two variables.

3. Currently, `move_piece` just swaps the (potentially absent) indices at two positions.
This is done by using an `equiv.swap` as an updating function. For now, this means that
moves that use `move_piece` are non-capturing. Additionally, no math or other requirements
on the positions or their contents is required. This means that `move_piece` supports a
move from a position to itself. A separate `move` is defined in `chess.move` that has
more chess-like rule constraints.

4. Index presence on the board is not limited to have each index on at-most-one position.
Preventing duplication of indices is not enforced by the `playfield` itself. However,
any given position can hold at-most-one index on it. The actual chess-like rule constraints
are in `chess.board`.

5. Sequences of moves are implemented on top of `move`s, rather than vice versa (`move`s
being defined as sequences of length one). This *probably* causes a bit of duplication,
which may warrant flipping things later.

-/

-- The height and width of the playfield
variables (m n : Type*)
-- The index type at (possibly) each position
variables (ι : Type*)

/--
A `playfield m n ι` represents a `matrix (m × n) option ι`, which is
a model for a `m × n` shaped game board where not every square is
occupied.
-/
def playfield : Type* := m × n → option ι

section playfield

-- The dimensions and index type of the playfield can be assumed
variables {m n ι}

/--
A conversion function to turn a bare `matrix` into a `playfield`.
A `matrix` requires the dimensions to be finite.

An example empty 3 × 3 playfield for 4 pieces could be generated by:
```
matrix_to_playfield ((
  ![![none, none, none],
    ![none, none, none],
    ![none, none, none]] : matrix (fin 3) (fin 3) (option (fin 4))
```

where the positions are 0-indexed, with the origin in the top-left,
first dimension for the row, and second dimension for the column
(0,0) (0,1) (0,2)
(1,0) (1,1) (1,2)
(2,0) (2,1) (2,2)

-/
def matrix_to_playfield [fintype m] [fintype n]
  (M : matrix m n (option ι)) : playfield m n ι :=
λ ⟨x, y⟩, M x y

-- Provide a short notation to be used for `playfield` construction when
-- using matrix notation
notation `PF` M := matrix_to_playfield M

/--
A `playfield` is by default `inhabited` by empty squares everywhere.
-/
instance playfield.inhabited : inhabited (playfield m n ι) :=
⟨λ ⟨x, y⟩, none⟩

-- Definitions and lemmas in this section will be accessible as `pf.___`
-- for a `pf : playfield m n ι`
namespace playfield

section repr

-- The size of the "vectors" for a `fin n' → ι`, for `has_repr` definitions
variables {m' n' : ℕ}
-- Require an index to be `repr`esentable to be able to represent a "vector" of it
variable [has_repr ι]

-- A finite `playfield` is just a uncurried `matrix`.
instance playfield_repr_instance :
  has_repr (playfield (fin n') (fin m') ι) := ⟨chess.utils.matrix_repr ∘ function.curry⟩

end repr

/--
A piece, identified by an index, is on the board, if there is any position
such that the index at that position is the one we're inquiring about.
Providing a `has_mem` instance allows using `ix ∈ pf` for `ix : ι, pf : playfield m n ι`.
This definition does not preclude duplicated indices on the playfield.
See "Implementation details".
-/
instance : has_mem ι (playfield m n ι) :=
⟨λ ix p, ∃ pos, p pos = some ix⟩

instance playfield_decidable_in [fintype m] [fintype n] [decidable_eq ι]
  {pf : playfield m n ι} {ix : ι} : decidable (ix ∈ pf) := fintype.decidable_exists_fintype

instance fintype
  [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]
  [fintype ι] :
  fintype (playfield m n ι) := pi.fintype

-- Fix a `pf : playfield m n ι` to use in definitions and lemmas below
variables (pf : playfield m n ι)

section occupied

/--
A wrapper to indicate that there is some `ix : ι` such that
for a `pf : playfield m n ι`, at `pos : m × n`, `pf pos = some ix`.
-/
@[reducible] def occupied_at (pos : m × n) : Prop := ∃ ix, pf pos = some ix

/--
The predicate that `pf.occupied_at pos` for some pos is decidable
if the indices `ix : ι` are finite and decidably equal.
-/
instance occupied_at.decidable_pred [fintype ι] [decidable_eq ι] : decidable_pred pf.occupied_at :=
  set.decidable_set_of (λ (a : m × n), ∃ (ix : ι), pf a = some ix)

variable {pf}

/--
A wrapper to indicate that there is some `ix : ι` such that
for a `pf : playfield m n ι`, at `pos : m × n`, `pf pos = some ix`.
-/
lemma occupied_at_def {pos : m × n} (h : pf.occupied_at pos) : ∃ ix, pf pos = some ix := h

/--
A wrapper to indicate that there is some `ix : ι` such that
for a `pf : playfield m n ι`, at `pos : m × n`, `pf pos = some ix`.
-/
lemma occupied_at_iff {pos : m × n} : pf.occupied_at pos ↔ ∃ ix, pf pos = some ix := iff.rfl

/--
A `pos : m × n` is unoccupied iff it is `none`.
-/
lemma not_occupied_at_iff {pos : m × n} : ¬ pf.occupied_at pos ↔ pf pos = none :=
by simp only [option.eq_none_iff_forall_not_mem, not_exists, option.mem_def]

/--
A `pf : playfield m n ι` maps any occupied `pos` uniquely.
-/
lemma occupied_at_unique {pos : m × n} (h : pf.occupied_at pos) : ∃! ix : ι, pf pos = some ix :=
begin
  refine exists_unique_of_exists_of_unique h _,
  intros _ _ H H',
  apply option.some.inj,
  rw [←H, ←H']
end

/--
If for some `pf : playfield m n ι`, at `pos : m × n`, `pf pos = some ix`,
then that is equivalent to `pf.occupied_at pos`.
-/
lemma occupied_at_of_some {pos : m × n} {ix : ι} (h : pf pos = some ix) :
  pf.occupied_at pos :=
⟨ix, h⟩

/--
If for some `pf : playfield m n ι`, at `pos : m × n`, `pf.occupied_at pos`,
then for a `pos' : m × n` such that `pf pos = pf pos'`, we have that
`pf.occupied_at pos'`.
-/
lemma occupied_at_transfer {pos pos' : m × n} (h : pf.occupied_at pos) (H : pf pos = pf pos') :
  pf.occupied_at pos' :=
exists.elim h (λ ix hix, ⟨ix, H ▸ hix⟩)

/--
If for some `pf : playfield m n ι`, at `pos : m × n`, `pf pos ≠ none`,
then that is equivalent to `pf.occupied_at pos`.
-/
lemma occupied_at_of_ne {pos : m × n} (hne : pf pos ≠ none) : pf.occupied_at pos :=
option.ne_none_iff_exists'.mp hne

/-- A wrapper API for underlying `option.is_some` propositions. -/
lemma occupied_has_some {pos : m × n} :
  (pf pos).is_some ↔ pf.occupied_at pos :=
option.is_some_iff_exists

/-- A wrapper API for converting between inequalities and existentials. -/
lemma occupied_has_not_none {pos : m × n} :
  pf pos ≠ none ↔ pf.occupied_at pos :=
option.ne_none_iff_exists'

/--
If for some `pf : playfield m n ι`, at `pos : m × n`, `pf pos = none`,
then that is equivalent to `¬ pf.occupied_at pos`.
-/
lemma not_occupied_has_none {pos : m × n} :
  (pf pos).is_none ↔ ¬ pf.occupied_at pos :=
by simpa only [not_occupied_at_iff] using option.is_none_iff_eq_none

variable (pf)

/-- The `set` of all positions that are `occupied_at`. -/
def occupied_positions : set (m × n) := {p : m × n | pf.occupied_at p}

/--
The `pos : m × n` that is in `pf.occupied_positions`
by definition is the proposition that `pf.occupied_at pos`.
-/
@[simp] lemma occupied_positions_in (pos : m × n) :
  pos ∈ pf.occupied_positions ↔ pf.occupied_at pos := iff.rfl

/--
The predicate that `λ p, p ∈ pf.occupied_positions` for some pos is
decidable if the indices `ix : ι` are finite and decidably equal.
-/
instance occcupied_positions_mem_decidable [fintype ι] [decidable_eq ι] :
  decidable_pred (∈ pf.occupied_positions) :=
occupied_at.decidable_pred (λ (pos : m × n), pf pos)

variables [fintype m] [fintype n]

/--
When the `playfield` dimensions are all finite,
the `occupied_positions`–all positions that are `occupied_at`–is a `fintype`.
-/
lemma finite_occupied : pf.occupied_positions.finite :=
set.finite.of_fintype pf.occupied_positions

variables [fintype ι] [decidable_eq ι]

/--
When the `playfield` dimensions are all finite,
the `occupied_positions_set` of all positions that are `occupied_at` is finite.
-/
instance fintype_occupied : fintype (pf.occupied_positions) :=
by { unfold occupied_positions, exact set_fintype _ }

/--
The `finset` of all positions that are `occupied_at`,
when all the dimensions of the `playfield` are `fintype`.
-/
def occupied_position_finset : finset (m × n) := pf.occupied_positions.to_finset

end occupied

section injective

/-- A `playfield` on which every index that appears, appears only once. -/
def some_injective : Prop :=
∀ ⦃a₁⦄, pf.occupied_at a₁ → ∀ ⦃a₂⦄, pf a₁ = pf a₂ → a₁ = a₂

/-- The injectivity of `some_injective` is equivalent to the `set.inj_on` proposition. -/
lemma inj_on_occupied : pf.some_injective ↔ set.inj_on pf pf.occupied_positions :=
⟨λ h _ hp _ _ H, h hp H, λ h _ hp _ H, h hp (occupied_at_transfer hp H) H⟩

/--
Explicitly state that the proposition that `pf.some_injective`
is `decidable`, when the `ι` is itself `decidable_eq`.
-/
instance some_injective_decidable
  [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]
  [fintype ι] [decidable_eq ι] :
  decidable (pf.some_injective) := fintype.decidable_forall_fintype

variable (h_inj : pf.some_injective)
include h_inj

/--
When a `pf : playfield m n ι` is `some_injective`,
if it is occupied at some `pos : m × n`, then it
is injective at that `pos`.
-/
protected lemma inj_iff {pos pos'} (h : pf.occupied_at pos) :
pf pos = pf pos' ↔ pos = pos' :=
⟨λ H, h_inj h H, congr_arg pf⟩

/--
When a `pf : playfield m n ι` is `some_injective`,
if it is not empty at some `pos : m × n`, then it
is injective at that `pos`.
-/
protected lemma injective {pos pos'} {ix : ι} (h : pf pos = some ix) (h' : pf pos' = some ix) :
  pos = pos' :=
begin
  apply h_inj,
  { exact ⟨_, h⟩ },
  { rw [h, h'] }
end

/--
When a `pf : playfield m n ι` is `some_injective`, every index
`ix : ι ∈ pf` exists in the `pf` uniquely.
-/
lemma unique_of_injective {ix : ι} (h : ix ∈ pf) :
  ∃! pos, pf pos = some ix :=
begin
  refine exists_unique_of_exists_of_unique h _,
  intros _ _,
  exact pf.injective h_inj
end

end injective

section decidable

variables [fintype m] [fintype n]
variables [fintype ι] [decidable_eq ι]

/--
The `occupied_positions` of a `pf : playfield m n ι` are finite
if the dimensions of the playfield and the indices are finite.
-/
instance occupied_fintype : fintype pf.occupied_positions := subtype.fintype pf.occupied_at

end decidable

/-- A `pos : pf.occupied_positions` can be used as a `pos : m × n`. -/
lemma coe_occ_val {pos : pf.occupied_positions} : (pos : m × n) = pos.val := rfl

/--
A `pos : pf.occupied_positions` has the property
that there is an not-necessarily-unique `ix : ι` such that `pf pos = some ix`.
-/
lemma exists_of_occupied (pos : pf.occupied_positions) : pf.occupied_at pos :=
pos.property

/--
A `pos : pf.occupied_positions` has the property
that there is a necessarily-unique `ix : ι` such that `pf pos = some ix`.
-/
lemma exists_unique_of_occupied (pos : pf.occupied_positions) : ∃! ix : ι, pf pos = ix :=
occupied_at_unique (pf.exists_of_occupied pos)

/-- A `pos : pf.occupied_positions` has the property that `pf pos` is occupied. -/
lemma occupied_is_some (pos : pf.occupied_positions) : (pf pos).is_some :=
occupied_has_some.mpr pos.property

variables (pf)

/--
Given some `ix : ι` such that for `pf : playfield m n ι` and `pos : m × n`,
`pf pos = some ix`, we can subtype into `pos : pf.occupied_positions`.
-/
def occupied_positions.mk {pos : m × n} {ix : ι} (h : pf pos = some ix) : pf.occupied_positions :=
⟨pos, exists.intro ix h⟩

/--
Given some `ix : ι` such that for `pf : playfield m n ι` and `pos : m × n`,
`pf pos = some ix`, we can subtype into `pos : pf.occupied_positions`.
-/
lemma occupied_positions_def {pos : m × n} {ix : ι} {h : pf pos = some ix} :
  pf (occupied_positions.mk pf h) = pf pos := rfl

/-- The injectivity of `pf.some_injective` extends to the `pf.occupied_positions` subtype. -/
lemma occupied_some_injective (h_inj : pf.some_injective) :
  ∀ ⦃a₁ a₂ : pf.occupied_positions⦄, pf a₁ = pf a₂ → a₁ = a₂ :=
λ p p' h, subtype.eq (h_inj p.property h)

/--
When a `pf : playfield m n ι` is `some_injective`, every `pos : pf.occupied_positions`
maps to a unique index via `pf pos`.
-/
lemma unique_of_occupied (h_inj : pf.some_injective) (pos : pf.occupied_positions) :
  ∃! (pos' : pf.occupied_positions), pf pos' = pf pos :=
begin
  use pos,
  split,
  { simp only [eq_self_iff_true] },
  { intros _ h,
    exact pf.occupied_some_injective h_inj h }
end

section index_at

variables (pos pos' : pf.occupied_positions)

variables (pf)

/-- Extract the `ix : ι` that is at `pf pos = some ix`. -/
def index_at := option.get (occupied_has_some.mpr pos.property)

variables {pf}

/-- Extract the `ix : ι` that is at `pf pos = some ix`. -/
lemma index_at_def : pf.index_at pos = option.get (occupied_has_some.mpr pos.property) := rfl

/--
For a `pos : pf.occupied_positions`, the wrapped index
given by `pf.index_at pos` is precisely `pf pos`.
-/
@[simp] lemma index_at_some : some (pf.index_at pos) = pf pos :=
by simp only [index_at_def, option.some_get, subtype.val_eq_coe]

/--
For a `pos : pf.occupied_positions`, the wrapped index `ix : ι`
given by `pf.index_at pos` is precisely `pf pos`, in iff form.
-/
@[simp] lemma index_at_iff {ix : ι} : pf pos = some ix ↔ pf.index_at pos = ix :=
⟨λ h, option.some.inj (h ▸ index_at_some pos), λ h, h ▸ (index_at_some pos).symm⟩

/--
For a `pos : m × n`, and the hypothesis that `h : pf pos = some ix`,
the index given by `pf.index_at (occupied_positions.mk _ h)` is precisely `ix`.
-/
@[simp] lemma index_at_mk {pos : m × n} {ix : ι} {h : pf pos = some ix} :
pf.index_at (occupied_positions.mk _ h) = ix :=
begin
  apply option.some.inj,
  rw ←h,
  simp only [index_at_some, pf.occupied_positions_def],
end

/-- The index retrieved via `pf.index_at` is known to be in the `pf`. -/
lemma index_at_in : pf.index_at pos ∈ pf :=
⟨pos, (index_at_some pos).symm⟩

/-- The index retrieved via `pf.index_at` is known to be in the `pf`, in existential format. -/
lemma index_at_exists : ∃ pos', pf pos' = some (pf.index_at pos) :=
⟨pos, (index_at_some pos).symm⟩

/--
The index retrieved via `pf.index_at` is known to be in the `pf`,
in existential format, operating on the `pf.occupied_positions` subtype.
-/
lemma index_at_exists' : ∃ (pos' : pf.occupied_positions), pf pos' = some (pf.index_at pos) :=
⟨pos, (index_at_some pos).symm⟩

/--
The index retrieved via `pf.index_at` is known to be unique in the `pf`,
given an injectivity condition via `pf.some_injective`.
-/
lemma occupied_unique_of_injective (h_inj : pf.some_injective) :
  ∃! (pos' : pf.occupied_positions), pf pos' = some (pf.index_at pos) :=
begin
  refine exists_unique_of_exists_of_unique (index_at_exists' pos) _,
  intros _ _ h h',
  apply pf.occupied_some_injective h_inj,
  rw [h, h']
end

/--
Index retrieval via `pf.index_at` is known to be injective,
given an injectivity condition via `pf.some_injective`.
-/
lemma index_at_inj (h_inj : pf.some_injective) {pos pos' : pf.occupied_positions} :
  pf.index_at pos = pf.index_at pos' ↔ pos = pos' :=
begin
  split,
  { intro h,
    rw ←option.some_inj at h,
    simp only [index_at_some, coe_coe] at h,
    exact pf.occupied_some_injective h_inj h },
  { intro h,
    rw h },
end

/--
Index retrieval via `pf.index_at` is known to be injective,
given an injectivity condition via `pf.some_injective`.
-/
lemma index_at.injective (h_inj : pf.some_injective) : function.injective pf.index_at :=
λ p p' h, (index_at_inj h_inj).mp h

/--
Index retrieval via `pf.index_at` is known to be surjective,
given an surjectivity condition via `function.surjective pf`.
-/
lemma index_at.surjective (h : function.surjective pf) :
  function.surjective pf.index_at :=
begin
  intro ix,
  obtain ⟨pos, hpos⟩ := h ix,
  use pos,
  { exact occupied_at_of_some hpos },
  { apply option.some.inj,
    simpa only [index_at_some] },
end

/--
Index retrieval via `pf` is known to be surjective,
given an surjectivity condition via `function.surjective pf.index_at`
and an unoccupied square somewhere.
-/
lemma index_at.implies_surjective (h : function.surjective pf.index_at)
  {unocc_pos : m × n} (h_unocc : ¬ pf.occupied_at unocc_pos) :
  function.surjective pf :=
begin
  intro ix,
  cases ix,
  { use unocc_pos,
    rwa [←occupied_has_not_none, not_not] at h_unocc },
  { obtain ⟨pos, hpos⟩ := h ix,
    use pos,
    simp only [←hpos, index_at_some] },
end

end index_at

section pos_from

variables (pf)
variables (ix : ι)

/--
A helper subtype definition describing all the positions that match an index.

No inhabited instance exists because the type could be empty,
if none of the positions of the playfield have this index.
-/
@[nolint has_inhabited_instance]
def pos_from_aux : Type* := {pos // pf.index_at pos = ix}

instance : has_coe (pf.pos_from_aux ix) pf.occupied_positions := ⟨subtype.val⟩

/-- A helper subtype definition describing all the positions that match an index. -/
@[simp] lemma pos_from_aux_subtype (pos : pf.pos_from_aux ix) :
  pf.index_at (pos : pf.occupied_positions) = ix := pos.property

/-- A helper set definition describing all the positions that match an index. -/
lemma pos_from_auxf_set (pos : pf.pos_from_aux ix) :
  (pos : pf.occupied_positions) ∈ {pos | pf.index_at pos = ix} := pos.property

/--
Given an injectivity condition of `pf.some_injective`, the type
of `pos : pf.occupied_positions` that identify a particular index is a subsingleton.
-/
lemma subsingleton_pos (h_inj : pf.some_injective) : subsingleton (pf.pos_from_aux ix) :=
begin
  refine subsingleton.intro _,
  intros pos pos',
  apply subtype.eq,
  rw ←index_at_inj h_inj,
  simp only [pos_from_aux_subtype, subtype.val_eq_coe]
end

/--
Given a surjectivity condition of `pf.index_at`, the type
of `pos : pf.occupied_positions` that identify a particular index is a nonempty.
-/
lemma nonempty_pos (surj : function.surjective pf.index_at) : nonempty (pf.pos_from_aux ix) :=
nonempty_subtype.mpr (surj ix)

variables [fintype m] [fintype n]
variables [fintype ι] [decidable_eq ι]

/-- A helper finset definition describing all the positions that match an index. -/
def pos_from_auxf : finset pf.occupied_positions := {pos | pf.index_at pos = ix}.to_finset

/-- A helper finset definition describing all the positions that match an index. -/
lemma pos_from_auxf_finset (pos : pf.pos_from_aux ix) :
  (pos : pf.occupied_positions) ∈ pf.pos_from_auxf ix :=
begin
  unfold pos_from_auxf,
  simp only [set.mem_to_finset],
  exact pos.property,
end

/-- A helper finset definition describing all the positions that match an index. -/
@[simp] lemma pos_from_auxf_in {pos : pf.occupied_positions} (h : pf.index_at pos = ix) :
  pos ∈ pf.pos_from_auxf ix :=
begin
  unfold pos_from_auxf,
  simp only [set.mem_to_finset],
  exact h,
end

variables (h_inj : pf.some_injective) (surj : function.surjective pf.index_at)
include h_inj surj

/--
Given a surjectivity condition of `pf.index_at`,
and an injectivity condition of `pf.some_injective`, the type
of `pos : pf.occupied_positions` that identify a particular index is a unique.
-/
lemma unique_pos :
  ∃! (pos : pf.occupied_positions), pos ∈ pf.pos_from_auxf ix ∧ pf.index_at pos = ix :=
begin
  obtain ⟨pos, hpos⟩ := surj ix,
  use pos,
  split,
  { simp only [hpos, and_true, eq_self_iff_true, pos_from_auxf_in] },
  { intros pos' h',
    rw ←index_at_inj h_inj,
    simp only [hpos, h'] }
end

/--
Given a surjectivity condition of `pf.index_at`,
and an injectivity condition of `pf.some_injective`,
we can retrieve the `pos : pf.occupied_positions`
such that `pf.index_at pos = ix`.
-/
def pos_from' (ix : ι) : pf.occupied_positions :=
finset.choose (λ pos, pf.index_at pos = ix) (pf.pos_from_auxf ix) (pf.unique_pos ix h_inj surj)

variable {pf}

/--
Given a surjectivity condition of `pf.index_at`,
and an injectivity condition of `pf.some_injective`,
we can retrieve the `pos : pf.occupied_positions`
such that `pf.index_at pos = ix`.
-/
lemma pos_from_def' : pf.pos_from' h_inj surj ix =
  finset.choose (λ pos, pf.index_at pos = ix) (pf.pos_from_auxf ix) (pf.unique_pos ix h_inj surj) :=
rfl

/--
Given a surjectivity condition of `pf.index_at`,
and an injectivity condition of `pf.some_injective`,
round-tripping to get the `pf.index_at (pf.pos_from' ix _ _)` is exactly `ix`.
-/
@[simp] lemma pos_from_index_at' : pf.index_at (pf.pos_from' h_inj surj ix) = ix :=
by { rw [pos_from_def'], exact finset.choose_property (λ pos, pf.index_at pos = ix) _ _ }

/--
Given a surjectivity condition of `pf.index_at`,
and an injectivity condition of `pf.some_injective`,
round-tripping to get the `pf (pf.pos_from' ix _ _)` is exactly `some ix`,
which goes through the coercion down to `pos : m × n`.
-/
lemma pos_from_at' : pf (pf.pos_from' h_inj surj ix) = some ix :=
by simp only [index_at_iff, pos_from_index_at']

/--
Given a surjectivity condition of `pf.index_at`,
and an injectivity condition of `pf.some_injective`,
the left inverse of `pf.index_at` is `pf.pos_from'`.
-/
lemma pos_from_inv_index_at' : function.left_inverse pf.index_at (pf.pos_from' h_inj surj) :=
λ ix, pos_from_index_at' ix h_inj surj

/--
Given a surjectivity condition of `pf.index_at`,
and an injectivity condition of `pf.some_injective`,
the right inverse of `pf.index_at` is `pf.pos_from'`.
-/
lemma index_at_inv_pos_from' : function.right_inverse pf.index_at (pf.pos_from' h_inj surj) :=
function.right_inverse_of_injective_of_left_inverse
  (index_at.injective h_inj)
  (pos_from_inv_index_at' h_inj surj)

variable (pf)

/--
Given a surjectivity condition of `pf.index_at`,
and an injectivity condition of `pf.some_injective`, the type
there exists a `pos : m × n' such that `pf pos = some ix`.
-/
def pos_from (ix : ι) : m × n := pf.pos_from' h_inj surj ix

variable {pf}

/--
Given a surjectivity condition of `pf.index_at`,
and an injectivity condition of `pf.some_injective`, the type
there exists a `pos : m × n' such that `pf pos = some ix`.
-/
lemma pos_from_def : pf.pos_from h_inj surj ix = pf.pos_from' h_inj surj ix := rfl

/--
Given a surjectivity condition of `pf.index_at`,
and an injectivity condition of `pf.some_injective`,
round-tripping to get the `pf (pf.pos_from ix _ _)` is exactly `some ix`,
-/
lemma pos_from_at : pf (pf.pos_from h_inj surj ix) = some ix :=
by simp only [pos_from_def, index_at_iff, pos_from_index_at']

/--
Given a surjectivity condition of `pf.index_at`,
and an injectivity condition of `pf.some_injective`,
the position retrieved via `pf.pos_from` means that
the `pf` is `occupied_at` it.
-/
lemma pos_from_occupied : pf.occupied_at (pf.pos_from h_inj surj ix) :=
⟨ix, pos_from_at _ _ _⟩

/--
Given a surjectivity condition of `pf.index_at`,
and an injectivity condition of `pf.some_injective`,
the partial inverse of `pf.pos_from` is `pf` itself.
-/
lemma pos_from_inv : function.is_partial_inv (pf.pos_from h_inj surj) pf :=
begin
  intros ix pos,
  split,
  { intro h,
    apply h_inj,
    { exact pos_from_occupied _ _ _ },
    { rw h,
      exact pos_from_at ix _ _ } },
  { intro h,
    rw ←h,
    exact pos_from_at ix _ _ }
end

/--
Given a surjectivity condition of `pf.index_at`,
and an injectivity condition of `pf.some_injective`,
the function `pf.pos_from` is injective.
-/
lemma pos_from.injective : function.injective (pf.pos_from h_inj surj) :=
function.injective_of_partial_inv (pos_from_inv h_inj surj)

end pos_from

section equiv

variables [fintype m] [fintype n]
variables [fintype ι] [decidable_eq ι]
variables (h_inj : pf.some_injective) (surj : function.surjective pf.index_at)
include h_inj surj

/--
Given a surjectivity condition of `pf.index_at`,
and an injectivity condition of `pf.some_injective`,
there is an explicit equivalence from the indices `ι` to
the type of positions in `pf.occupied_positions`.
-/
def index_equiv : ι ≃ pf.occupied_positions :=
{ to_fun := pf.pos_from' h_inj surj,
  inv_fun := pf.index_at,
  left_inv := pos_from_inv_index_at' h_inj surj,
  right_inv := index_at_inv_pos_from' h_inj surj}

end equiv

-- To be able to state whether two positions are equal
-- we need to be able to make the equality on each of the dimensions `decidable`
variables [decidable_eq m] [decidable_eq n]

section move_piece

-- Fix `start_square` and `end_square : m × n` to use in definitions and lemmas below
variables (start_square end_square : m × n)

/--
Move an (optional) index from `start_square` to `end_square` on a `playfield`,
swapping the indices at those squares.

Does not assume anything about occupancy.
-/
def move_piece : playfield m n ι :=
λ pos, pf (equiv.swap start_square end_square pos)

/--
Equivalent to to `move_piece`, but useful for `rewrite`\ ing.
-/
lemma move_piece_def : pf.move_piece start_square end_square =
    λ pos, pf (equiv.swap start_square end_square pos) := rfl

/--
Moving an (optional) index that was at `start_square` places it at `end_square`
-/
@[simp] lemma move_piece_start :
pf.move_piece start_square end_square start_square = pf end_square :=
by simp only [move_piece_def, equiv.swap_apply_left]

/--
Moving an (optional) index that was at `end_square` places it at `start_square`
-/
@[simp] lemma move_piece_end :
pf.move_piece start_square end_square end_square = pf start_square :=
by simp only [move_piece_def, equiv.swap_apply_right]

/--
Moving an (optional) index retains whatever (optional) indices that were at other squares.
-/
@[simp] lemma move_piece_diff
  {start_square end_square other_square : m × n}
  (ne_start : other_square ≠ start_square)
  (ne_end : other_square ≠ end_square) :
pf.move_piece start_square end_square other_square = pf other_square :=
by simp only [move_piece_def, equiv.swap_apply_of_ne_of_ne ne_start ne_end]

/--
The `pf : playfield m n ι` is `occupied_at start_square` after a `move_piece`
iff it is `occupied_at end_square` before the piece move.
-/
@[simp] lemma move_piece_occupied_start :
(pf.move_piece start_square end_square).occupied_at start_square ↔ pf.occupied_at end_square :=
by simp only [occupied_at, move_piece_start]

/--
The `pf : playfield m n ι` is `occupied_at end_square` after a `move_piece`
iff it is `occupied_at start_square` before the piece move.
-/
@[simp] lemma move_piece_occupied_end :
(pf.move_piece start_square end_square).occupied_at end_square ↔ pf.occupied_at start_square :=
by simp only [occupied_at, move_piece_end]

/--
The `pf : playfield m n ι` is `occupied_at other_square` after a `move_piece`,
for a `pos` that is neither `start_square` nor `end_square`,
iff it is `occupied_at other_square` before the piece move.
-/
@[simp] lemma move_piece_occupied_diff
  {start_square end_square other_square : m × n}
  (ne_start : other_square ≠ start_square)
  (ne_end : other_square ≠ end_square) :
(pf.move_piece start_square end_square).occupied_at other_square ↔ pf.occupied_at other_square :=
by simp only [occupied_at, pf.move_piece_diff ne_start ne_end]

/-- Pieces do not disappear after a `move_piece`. -/
lemma retains_pieces (pf : playfield m n ι) (start_square end_square : m × n) (ix : ι)
  (h_pf : ix ∈ pf) :
    ix ∈ pf.move_piece start_square end_square :=
begin
  obtain ⟨pos, h⟩ := h_pf,
  by_cases hs : pos = start_square;
  by_cases he : pos = end_square,
  { use pos,
    simp [←hs, ←h, he] },
  { use end_square,
    simp [hs, he, ←h] },
  { use start_square,
    simp [hs, he, ←h] },
  { use pos,
    simp [hs, he, ←h] }
end

/--
Each index that is present on the playfield and appears only once,
appears only once after a `move_piece`.
-/
lemma retains_injectivity (pf : playfield m n ι) (h : pf.some_injective)
  {start_square end_square : m × n} (h_occ : pf.occupied_at start_square) :
  (pf.move_piece start_square end_square).some_injective :=
begin
  intros pos h_some pos' h_eq,
  rcases split_eq pos start_square end_square with rfl|rfl|⟨hS, hE⟩;
  rcases split_eq pos' start_square end_square with rfl|rfl|⟨hS', hE'⟩,
  { refl },
  { simp only [move_piece_start, move_piece_end] at h_eq,
    exact h h_occ h_eq.symm },
  { simp only [move_piece_diff, hS', hE', move_piece_start,
               move_piece_occupied_start, ne.def, not_false_iff] at h_eq h_some,
    have : pos' = end_square := (h h_some h_eq).symm,
    contradiction },
  { simp only [move_piece_start, move_piece_end] at h_eq,
    exact (h h_occ h_eq).symm },
  { refl },
  { simp only [move_piece_diff _ hS' hE', move_piece_end,
               move_piece_occupied_end] at h_eq h_some,
    have : pos' = start_square := (h h_some h_eq).symm,
    contradiction },
  { simp only [move_piece_diff, hS, hE, move_piece_start,
               move_piece_occupied_diff, ne.def, not_false_iff] at h_eq h_some,
    have : pos = end_square := h h_some h_eq,
    contradiction },
  { simp only [move_piece_diff, hS, hE, move_piece_end,
               move_piece_occupied_diff, ne.def, not_false_iff] at h_eq h_some,
    have : pos = start_square := h h_some h_eq,
    contradiction },
  { simp only [move_piece_diff, hS, hE, hS', hE',
               move_piece_occupied_diff, ne.def, not_false_iff] at h_eq h_some,
    exact h h_some h_eq }
end

/--
If every index and the empty square is present in the `pf : playfield m n ι`,
as given by a `function.surjective pf` proposition, then each index
is present on the playfield after a `move_piece`.
-/
lemma retains_surjectivity (pf : playfield m n ι) (h : function.surjective pf)
  {start_square end_square : m × n} (h_occ : pf.occupied_at start_square) :
  function.surjective (pf.move_piece start_square end_square) :=
begin
  intro ix,
  obtain ⟨six', hsi⟩ := h_occ,
  obtain ⟨P, hP⟩ := h ix,
  rw ←hP,
  rcases split_eq (P : m × n) start_square end_square with H|H|⟨hS, hE⟩,
  { use end_square,
    simp only [move_piece_end, H] },
  { use start_square,
    simp only [H, move_piece_start] },
  { use P,
    simp only [hS, hE, ne.def, not_false_iff, move_piece_diff] }
end

/--
If every index and the empty square is present in the `pf : playfield m n ι`,
as given by a `function.surjective pf` proposition, then each index
is present on the playfield after a `move_piece`.
-/
lemma index_at_retains_surjectivity (pf : playfield m n ι) (h : function.surjective pf.index_at)
  {start_square end_square : m × n} (h_occ : pf.occupied_at start_square)  :
  function.surjective (pf.move_piece start_square end_square).index_at :=
begin
  intro ix,
  obtain ⟨P, hP⟩ := h ix,
  simp_rw [←index_at_iff, ←hP],
  rcases split_eq (P : m × n) start_square end_square with H|H|⟨hS, hE⟩,
  { use end_square,
    { simpa only [move_piece_occupied_end, occupied_positions_in] using h_occ },
    { simp only [H, index_at_some, subtype.coe_mk, move_piece_end] } },
  { use start_square,
    { simpa only [H, move_piece_occupied_start, occupied_positions_in] using P.property },
    { simp only [H, move_piece_start, index_at_some, subtype.coe_mk] } },
  { use P,
    { simpa only [hS, hE, ne.def, not_false_iff,
                  move_piece_occupied_diff, occupied_positions_in] using P.property},
    { simp only [hS, hE, index_at_some, ne.def, not_false_iff,
                 move_piece_diff, subtype.coe_mk] } }
end

end move_piece

section move_sequence

-- The length of the sequence
variables {o : ℕ}
-- Fix a sequence of start and end squares.
variables (seq : vector ((m × n) × (m × n)) o)

/-- Make a sequence of `move`s all at once. -/
def move_sequence : fin (o + 1) → playfield m n ι :=
(vector.scanl (λ acc (x : prod _ _), move_piece acc x.fst x.snd) pf seq).nth

/--
Equivalent to to `move_sequence`, but useful for `rewrite`\ ing.
-/
lemma move_sequence_def : pf.move_sequence seq =
  (vector.scanl (λ acc (x : prod _ _), move_piece acc x.fst x.snd) pf seq).nth := rfl

/--
Throughout a sequence, moving an (optional) index that was at
`start_square` places it at `end_square` on the next board.
-/
lemma move_sequence_start (e : fin o) :
((pf.move_sequence seq) e.cast_succ) (seq.nth e).fst = ((pf.move_sequence seq) e.succ) (seq.nth e).snd :=
by simp only [move_sequence_def, vector.scanl_nth, move_piece_end]

/--
Throughout a sequence, moving an (optional) index that was at
`end_square` places it at `start_square` on the next board.
-/
lemma move_sequence_end (e : fin o) :
((pf.move_sequence seq) e.cast_succ) (seq.nth e).snd = ((pf.move_sequence seq) e.succ) (seq.nth e).fst :=
by simp only [move_sequence_def, vector.scanl_nth, move_piece_start]

/--
Throughout a sequence, moving an (optional) index retains whatever
(optional) indices that were at other squares on the next board.
-/
@[simp] lemma move_sequence_diff
  (other_square : m × n)
  (e : fin o)
  (ne_start : other_square ≠ (seq.nth e).fst)
  (ne_end : other_square ≠ (seq.nth e).snd) :
  ((pf.move_sequence seq) e.cast_succ) other_square = ((pf.move_sequence seq) e.succ) other_square :=
by simp only [move_sequence_def, vector.scanl_nth, ne_start, ne_end,
              ne.def, not_false_iff, move_piece_diff]

end move_sequence

end playfield

end playfield
