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
  contents := λ xpair, (B.enum_2d_some_fin.nth xpair.fst >>= λ l, l.nth xpair.snd).join,
  contains :=
    begin
      intro i,
      apply playfield.index_at_of_exists,
      rw option.subtype_exists,
      simp_rw [←option.map_eq_map, ←option.bind_id_eq_join, map_bind, option.map_eq_map,
               option.map_of_id, option.bind_map_comm, ←option.map_eq_map, map_bind,
               option.map_eq_map, map_subtype, list.enum_2d_some_fin_map_subtype_eq_enum_some],
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
          { simp only [list.nth_pmap, list.enum_2d_some_cons, list.enum_2d_some_fin, list.pmap,
                       option.some_bind, list.nth, fin.coe_mk, fin.mk_eq_subtype_mk,
                       option.pmap_eq_some_iff, option.join_pmap_eq_pmap_join] at hix,
            obtain ⟨z, hz, hz'⟩ := hix,
            simp only [option.join_eq_some] at hz,
            have h' := h.symm,
            simp only [list.nth_pmap, list.enum_2d_some_cons, list.enum_2d_some_fin,
                       option.some_bind, list.nth, fin.coe_mk, hz, option.join,
                       fin.mk_eq_subtype_mk, option.pmap, exists_prop, option.join_eq_some,
                       subtype.mk_eq_mk, exists_eq_right, option.pmap_eq_some_iff] at h',
            have H : y = y',
              { apply list.enum_some_some_injective,
                { rw hz,
                  simp only [option.join, ne.def, not_false_iff], },
                { rw [hz, h'] } },
            simp_rw H },
          { simp only [list.nth_pmap, list.enum_2d_some_cons, list.enum_2d_some_fin, list.pmap,
                       option.some_bind, list.nth, fin.coe_mk, fin.mk_eq_subtype_mk,
                       option.pmap_eq_some_iff, option.join_pmap_eq_pmap_join] at hix,
            obtain ⟨z, hz, hz'⟩ := hix,
            simp only [option.join_eq_some] at hz,
            have h' := (congr_arg (option.map subtype.val) h).symm,
            simp only [list.enum_2d_some_cons, list.enum_2d_some_fin, option.some_bind, list.nth,
                       fin.coe_mk, option.join, fin.mk_eq_subtype_mk, option.pmap,
                       option.join_eq_some, exists_eq_right, option.pmap_eq_some_iff, list.pmap_map,
                       option.pmap_map, hz, list.nth_pmap, list.pmap, option.map_some',
                       option.bind_eq_some, exists_and_distrib_right, subtype.exists,
                       option.map_eq_some'] at h',
            obtain ⟨hzl, lx, ⟨ly, lz, rfl⟩, hlx⟩ := h',
            simp only [list.nth_pmap, exists_prop, subtype.mk_eq_mk, option.pmap_eq_some_iff] at hlx,
            obtain ⟨k, hk, m, hm, rfl⟩ := hlx,
            have H : m + l.reduce_option.length < l.reduce_option.length := list.enum_some_lt l (list.nth_mem hz),
            rw [←nat.lt_sub_right_iff_add_lt, nat.sub_self] at H,
            exact absurd H (not_lt_of_le m.zero_le) } },
        { cases x',
          {
            simp only [list.nth_pmap, list.enum_2d_some_cons, list.enum_2d_some_fin, list.pmap, list.nth, fin.coe_mk, fin.mk_eq_subtype_mk,
  option.pmap_eq_some_iff, option.join_eq_some, option.bind_pmap, list.nth_map, option.pmap_map, option.pbind_eq_some] at hix,
            obtain ⟨lx, hlx, z, hly, k, hz, hk⟩ := hix,
            simp only [option.mem_def] at hlx,
            -- simp only [option.join_eq_some] at hz,
            -- have h' := h.symm,
            have h' := (congr_arg (option.map subtype.val) h).symm,
            simp only [list.enum_2d_some_cons, list.enum_2d_some_fin, option.some_bind, list.nth, fin.coe_mk, option.join,
  fin.mk_eq_subtype_mk, option.pmap, option.join_eq_some, exists_eq_right, list.pmap_map, list.nth_pmap, list.pmap,
  option.map_some', option.map_eq_some', ←option.join_map_eq_map_join, option.map_pmap, option.pmap_eq_map, hlx, hly,
  hz] at h',
            -- rw ←option.join_map_eq_map_join at h',
            have H := list.enum_some_lt l (list.nth_mem h'),
            rw [←nat.lt_sub_right_iff_add_lt, nat.sub_self] at H,
            exact absurd H (not_lt_of_le k.zero_le) },
          {
            simp only [list.nth_pmap, list.enum_2d_some_cons, list.enum_2d_some_fin, list.pmap, list.nth, fin.coe_mk, fin.mk_eq_subtype_mk,
  option.pmap_eq_some_iff, option.join_eq_some, option.bind_pmap, list.nth_map, option.pmap_map, option.pbind_eq_some, option.bind_pmap] at hix,
            obtain ⟨lx, hlx, z, hly, k, hz, hk⟩ := hix,
            simp only [option.mem_def] at hlx,
            have h' := (congr_arg (option.map subtype.val) h).symm,
            simp only [list.enum_2d_some_cons, list.enum_2d_some_fin, option.some_bind, list.nth, fin.coe_mk, option.join,
  fin.mk_eq_subtype_mk, option.pmap, option.join_eq_some, exists_eq_right, list.pmap_map, list.nth_pmap, list.pmap,
  option.map_some', option.map_eq_some', option.join_map_eq_map_join, option.map_pmap, option.pmap_eq_map, hlx, hly,
  hz, option.bind_pmap, option.pbind_eq_bind, option.pbind_eq_some] at h',
            obtain ⟨ix, ⟨lz, hlz, hlz'⟩, hix'⟩ := h',
            simp at hlz',
            obtain ⟨m, hm, n, hn, hn'⟩ := hlz',
            simp_rw fin.eq_iff_veq at hn' hk,
            simp only [option.mem_def] at hlz,
            simp only [option.map_eq_some'] at hn,
            obtain ⟨w, hn, hw⟩ := hn,
            have hX : x < ls.length := by simpa only using nat.lt_of_succ_lt_succ hx,
            have hX' : x' < ls.length := by simpa only using nat.lt_of_succ_lt_succ hx',
            have hY : y < (ls.map list.length).foldr max 0,
              { have := list.length_enum_2d_some_nth (list.nth_mem hlx),
                obtain ⟨hY', hy''⟩ := list.nth_eq_some.mp hly,
                exact lt_of_lt_of_le hY' this },
            have hY' : y' < (ls.map list.length).foldr max 0,
              { have := list.length_enum_2d_some_nth (list.nth_mem hlz),
                obtain ⟨hY', hy''⟩ := list.nth_eq_some.mp hm,
                exact lt_of_lt_of_le hY' this },
            simp only [list.length] at hx hx',
            have hkl : k < ls.join.reduce_option.length,
              { rw [←add_lt_add_iff_left l.reduce_option.length, add_comm, ←hix'],
                simpa only [list.reduce_option_append, list.join, list.length_append] using fin.is_lt ix },
            suffices : ((⟨x, hX⟩ : fin ls.length), (⟨y, hY⟩ : fin ((ls.map list.length).foldr max 0))) =
              (⟨x', hX'⟩, ⟨y', hY'⟩),
              { simpa only [prod.mk.inj_iff, subtype.mk_eq_mk] using this },
            apply hB,
            { use ⟨k, hkl⟩,
              simp only [list.nth_pmap, hlx, hly, hz, list.enum_2d_some_fin, option.some_bind,
                         option.join, fin.mk_eq_subtype_mk, option.pmap, fin.coe_mk] },
            { simp only [list.nth_pmap, option.join, list.enum_2d_some_fin, option.some_bind,
                         subtype.mk_eq_mk, fin.mk_eq_subtype_mk, option.pmap, fin.coe_mk, hlx, hlz,
                         hly, hm, hz, hn],
              apply nat.add_right_cancel,
              rw hw,
              rw hn',
              rw hk,
                         },
          },
        },
      },
    end
  }
