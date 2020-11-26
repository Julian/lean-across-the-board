import chess.board
import utils.list.enum_some
import utils.fin

def B : list (list (option chess.colored_piece)) := [
  [♞, __, ♞],
  [__, __, __],
  [♘, __, ♘]
]

#eval B
#eval PFL B

#eval (list.enum (B.map list.enum)).map (λ xpair, list.map (prod.map (prod.mk (prod.fst xpair)) id) (prod.snd xpair))

variable {α : Type*}

def coord (l : list (list α)) : list (list ((ℕ × ℕ) × α)) :=
(list.enum (l.map list.enum)).map
  (λ xpair, list.map (prod.map (prod.mk (prod.fst xpair)) id) (prod.snd xpair))

lemma map_subtype {α β : Type*} {l : list (list (option α))} {f : α → β} {i j : ℕ} :
  l.nth i >>= (λ y, option.map (option.map f) (y.nth j)) =
  (l.map (list.map (option.map f))).nth i >>= (λ y, y.nth j) :=
by simp_rw [list.nth_map, ←option.map_eq_map, seq_bind_eq, function.comp, option.map_eq_map, list.nth_map]

def SB (B : list (list (option chess.colored_piece))) :
  chess.board (fin B.length) (fin ((B.map (list.length)).foldr max 0)) (fin B.join.reduce_option.length) chess.colored_piece :=
{ pieces := λ i, B.join.reduce_option.nth_le i i.is_lt,
  contents := λ xpair, (B.enum_2d_some_fin.nth xpair.fst >>= λ l, l.nth xpair.snd) >>= id,
  contains :=
    begin
      intro i,
      apply playfield.index_at_of_exists,
      rw option.subtype_exists,
      simp_rw [←option.map_eq_map, map_bind, option.map_eq_map, option.map_of_id,
                option.bind_map_comm, ←option.map_eq_map, map_bind, option.map_eq_map,
                map_subtype, list.enum_2d_some_fin_map_subtype_eq_enum_some],
      obtain ⟨m, n, h⟩ := list.enum_2d_some_exists_of_lt B i.is_lt,
      obtain ⟨l, hl, hl'⟩ := option.bind_eq_some.mp h,
      rw list.nth_eq_some at hl hl',
      obtain ⟨hm, rfl⟩ := hl,
      obtain ⟨hn, hln⟩ := hl',
      refine ⟨(⟨m, _⟩, ⟨n, _⟩), _⟩,
      { simpa only [list.length_enum_2d_some] using hm },
      { refine lt_of_lt_of_le hn _,
        exact list.length_enum_2d_some_nth (list.nth_le_mem _ _ hm) },
      { simp only [fin.val_eq_coe, id.def, fin.coe_mk, h, option.some_bind] },
    end,
  injects :=
    begin
      induction B with l ls hB,
      { rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩,
        simp only [list.length] at hx,
        exact absurd hx (not_lt_of_le x.zero_le) },
      { rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨ix, hix⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ h,
        cases x,
        { cases x',
          { by_cases hne : y = y',
            { subst hne },
            simp only [list.nth_pmap, list.enum_2d_some_cons, list.enum_2d_some_fin, list.pmap,
                       option.some_bind, id.def, option.bind_eq_some, list.nth, exists_eq_right,
                       fin.coe_mk, fin.mk_eq_subtype_mk, option.pmap_eq_some_iff] at hix,
            obtain ⟨_ | z, hz, k, hk, hk'⟩ := hix,
            { simpa only using hk },
            simp only [option.mem_def] at hz,
            have he := list.enum_some_exists_unique _ (list.nth_mem hz),
            simp only [list.nth_pmap, hz, list.enum_2d_some_cons, list.enum_2d_some_fin, list.pmap,
                       option.some_bind, id.def, list.nth, fin.mk_eq_subtype_mk, option.pmap,
                       fin.coe_mk] at h,
            have h' := h.symm,
            simp only [exists_prop, id.def, option.bind_eq_some, subtype.mk_eq_mk,
                       exists_eq_right, fin.mk_eq_subtype_mk, option.mem_def,
                       option.pmap_eq_some_iff] at h',
            obtain ⟨u, H, hu⟩ := he,
            have hny := hu y hz,
            have hny' := hu y' h',
            rw [hny, hny'] at hne,
            exact absurd rfl hne },
          { simp only [list.nth_pmap, list.enum_2d_some_cons, list.enum_2d_some_fin, list.pmap,
                       option.some_bind, id.def, option.bind_eq_some, list.nth, exists_eq_right,
                       fin.mk_eq_subtype_mk, option.pmap_eq_some_iff, fin.coe_mk] at hix,
            obtain ⟨_ | z, hz, k, hk, hk'⟩ := hix,
            { simpa only using hk },
            simp only [option.mem_def] at hz,
            have h' := (congr_arg (option.map subtype.val) h).symm,
            simp_rw [←option.map_eq_map, map_bind, option.map_eq_map, option.map_of_id,
                      option.bind_map_comm, ←option.map_eq_map, map_bind, option.map_eq_map,
                      map_subtype, list.enum_2d_some_fin_map_subtype_eq_enum_some] at h',
            simp only [hz, list.enum_2d_some_cons, list.nth_map, option.some_bind, id.def,
                       option.bind_eq_some, list.nth, exists_eq_right, exists_exists_and_eq_and,
                       fin.coe_mk, option.map_eq_some'] at h',
            obtain ⟨-, -, -, -, m, -, hm⟩ := h',
            have H : z < l.reduce_option.length := list.enum_some_lt l (some z) hz z rfl,
            have H' : l.reduce_option.length ≤ z,
              { refine le_iff_exists_add.mpr ⟨m, _⟩,
                rwa [←hm, add_comm] },
            exact absurd H (not_lt_of_le H') },
        },
        { cases x',
          { simp only [list.nth_pmap, list.enum_2d_some_cons, list.enum_2d_some_fin, list.pmap,
                       id.def, option.bind_eq_some, list.nth, exists_eq_right,
                       option.pmap_eq_some_iff, fin.coe_mk, list.nth_map] at hix,
            obtain ⟨lx, ⟨ly, hm, rfl⟩, H⟩ := hix,
            simp only [option.mem_def, option.map_eq_some'] at hm,
            obtain ⟨L, hL, rfl⟩ := hm,
            simp only [list.nth_pmap, fin.mk_eq_subtype_mk, option.pmap_eq_some_iff] at H,
            obtain ⟨_ | z, hz, k, hk, hk'⟩ := H,
            { simpa only using hk },
            simp only [option.mem_def, list.nth_map, option.map_eq_some'] at hz,
            obtain ⟨n, hn, w, rfl, rfl⟩ := hz,
            have h' := (congr_arg (option.map subtype.val) h).symm,
            simp_rw [←option.map_eq_map, map_bind, option.map_eq_map, option.map_of_id,
                      option.bind_map_comm, ←option.map_eq_map, map_bind, option.map_eq_map,
                      map_subtype, list.enum_2d_some_fin_map_subtype_eq_enum_some] at h',
            simp only [hL, hn, list.enum_2d_some_cons, list.nth_map, option.some_bind, id.def,
                       option.bind_eq_some, list.nth, exists_eq_right, fin.coe_mk, option.map_some'] at h',
            have H : (w + l.reduce_option.length) < l.reduce_option.length :=
              list.enum_some_lt l (some _) (list.nth_mem h') _ rfl,
            have H' : l.reduce_option.length < l.reduce_option.length :=
              lt_of_le_of_lt (nat.le_add_left _ _) H,
            exact absurd H' (lt_irrefl _) },
          { specialize hB,  },
        },
      },
    end
  }
