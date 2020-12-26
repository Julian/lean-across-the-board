import chess.move.legal

open chess

namespace chess

variables (m n : Type)

variables [fintype m] [decidable_eq m] [linear_order m]
variables [fintype n] [decidable_eq n] [linear_order n]

structure move.description (K : Type*) :=
(figure : K)
(from_sq : (option m × option n))
(to_sq : (m × n))

structure move.description.chess extends move.description m n piece :=
(capture : option capture)
(promoted : option promotions)

instance move.description.has_repr [has_repr m] [has_repr n] :
  has_repr (move.description.chess m n) :=
⟨λ ⟨⟨p, fsq, tsq⟩, cap, prom⟩, string.intercalate " "
  [repr p, repr fsq, repr tsq, repr cap, repr prom]⟩

section run_move

variables {m n}

variables {i : ℕ} (b : board m n (fin i) chess.colored_piece)
  (d : move.description m n chess.piece)
  (d' : move.description.chess m n)

namespace board

def run_move' : option ((m × n) × (m × n)) :=
option.map (λ ix, (b.pos_from ix, d.to_sq))
  (list.exactly_one (list.filter (λ ix,
    ((chess.colored_piece.piece ∘ b.pieces) ix) = d.figure ∧
    (d.from_sq.fst = none ∨ some (b.pos_from ix).fst = d.from_sq.fst) ∧
    (d.from_sq.snd = none ∨ some (b.pos_from ix).snd = d.from_sq.snd) ∧
    (chess.piece.move_rule ((chess.colored_piece.piece ∘ b.pieces) ix)
      (b.pos_from ix) d.to_sq)
  ) (list.fin_range i)))

lemma run_move'_eq_some (b') : b.run_move' d = some b' ↔
  ∃ ix : fin i, (b.pieces ix).piece = d.figure ∧
  (d.from_sq.fst = none ∨ some (b.pos_from ix).fst = d.from_sq.fst) ∧
  (d.from_sq.snd = none ∨ some (b.pos_from ix).snd = d.from_sq.snd) ∧
  (chess.piece.move_rule ((chess.colored_piece.piece ∘ b.pieces) ix) (b.pos_from ix) d.to_sq) :=
begin
  simp only [run_move', list.filter_singleton_of_nodup _ (list.fin_range i) _ (list.nodup_fin_range i), true_and,
  forall_prop_of_true, list.mem_fin_range, not_and, list.exactly_one_some, function.comp_app, ne.def,
  option.map_eq_some'],
  split,
  { rintro ⟨ix, ⟨hix, h⟩, H⟩,
    simp [hix],
  },
  {  },
  -- simp_rw ,
end

def run_move : option ((m × n) × (m × n)) :=
if d'.capture = none
  then if b.contents d'.to_description.to_sq = none
    then b.run_move' d'.to_description
    else none
  else if b.contents d'.to_description.to_sq = none
    then none
    else b.run_move' d'.to_description

@[simp] lemma run_move_eq_some (b') : b.run_move d' = some b' ↔
  b.run_move' d'.to_description = some b' ∧ (
  (d'.capture = none ∧ b.contents d'.to_description.to_sq = none) ∨
  (d'.capture ≠ none ∧ b.contents d'.to_description.to_sq ≠ none)) :=
begin
  cases hd : d'.capture;
  cases hb : b.contents d'.to_description.to_sq;
  simp [run_move, hd, hb],
end

@[simp] lemma run_move_eq_none : b.run_move d' = none ↔
  b.run_move' d'.to_description = none ∨ (
  (d'.capture = none ∧ b.contents d'.to_description.to_sq ≠ none) ∨
  (d'.capture ≠ none ∧ b.contents d'.to_description.to_sq = none)) :=
begin
  cases hd : d'.capture;
  cases hb : b.contents d'.to_description.to_sq;
  simp [run_move, hd, hb],
end

end board

open board

lemma move.description.occupied_start {pair : ((m × n) × (m × n))} (h : pair ∈ b.run_move' d) :
  b.contents.occupied_at pair.fst :=
begin
  obtain ⟨x, y⟩ := pair,
  simp only [run_move', option.mem_def, prod.mk.inj_iff, function.comp_app, option.map_eq_some',
             list.exactly_one_some] at h,
  obtain ⟨ix, h, rfl, rfl⟩ := h,
  exact playfield.pos_from_occupied ix _ _
end

lemma move.description.chess.occupied_start {pair : ((m × n) × (m × n))} (h : pair ∈ b.run_move d') :
  b.contents.occupied_at pair.fst :=
begin
  simp only [run_move, option.mem_def] at h,
  split_ifs at h,
  { exact d'.to_description.occupied_start b h },
  { exact false.elim h },
  { exact false.elim h },
  { exact d'.to_description.occupied_start b h }
end

lemma move.description.chess.unoccupied_end_of_no_capture {pair : ((m × n) × (m × n))}
  (h : pair ∈ b.run_move d') (h' : d'.capture = none) :
  ¬ b.contents.occupied_at pair.snd :=
begin
  obtain ⟨x, y⟩ := pair,
  simp only [run_move, run_move', option.mem_def, function.comp_app, h', if_true,
              eq_self_iff_true] at h,
  split_ifs at h with H H,
  { simp only [prod.mk.inj_iff, option.map_eq_some', list.head'_cons, list.exactly_one_some] at h,
    obtain ⟨ix, h, rfl, rfl⟩ := h,
    rintro ⟨p, hp⟩,
    simpa only [H] using hp },
  { exact false.elim h }
end

lemma move.description.chess.occupied_end_of_capture {pair : ((m × n) × (m × n))}
  (h : pair ∈ b.run_move d') (h' : d'.capture = some capture.capture) :
  b.contents.occupied_at pair.snd :=
begin
  obtain ⟨x, y⟩ := pair,
  simp only [run_move, run_move', option.mem_def, function.comp_app, h', if_false] at h,
  split_ifs at h with H H,
  { exact false.elim h },
  { simp only [prod.mk.inj_iff, option.map_eq_some', list.head'_cons, list.exactly_one_some] at h,
    obtain ⟨ix, h, rfl, rfl⟩ := h,
    exact playfield.occupied_at_of_ne H }
end

end run_move

end chess
