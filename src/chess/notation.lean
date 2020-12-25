import chess.board
import utils.list.enum_some
import utils.fin

def listboard (B : list (list (option chess.colored_piece))) :
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
               option.map_eq_map, list.map_subtype, list.enum_2d_some_fin_map_subtype_eq_enum_some],
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
      rintro ⟨x, y⟩ ⟨ix, hix⟩ ⟨x', y'⟩ h,
      simp only at hix,
      simp only [fin.eq_iff_veq, fin.val_eq_coe, prod.mk.inj_iff],
      apply list.enum_2d_some_fin_some_injective' B,
      { rw hix,
        simp only [ne.def, not_false_iff] },
      { simp only at h,
        rw hix at h,
        have h' := h.symm,
        rw option.join_eq_some at hix h',
        rw [h', hix] },
    end
  }

section fin_instance

variables {K : Type*} {x : K} {hd : list K} {tl : list (list K)}
variables {hd' : list (option K)} {tl' : list (list (option K))}

instance board_fin0 : has_zero (fin (hd :: tl).length) :=
⟨⟨0, by simp only [nat.succ_pos', list.length]⟩⟩

instance board_fin1 : has_one (fin (hd :: tl).length) :=
⟨⟨tl.cases_on 0 1, by { cases tl; simp only [nat.succ_pos', nat.succ_lt_succ_iff, list.length, pi.one_apply]}⟩⟩

instance board_fin0' :
  has_zero (fin (list.foldr max 0 (list.map list.length ((x :: hd) :: tl)))) :=
⟨⟨0, by simp only [nat.succ_pos', list.length, lt_max_iff, true_or, list.foldr, list.map]⟩⟩

instance board_fin1' :
  has_one (fin (list.foldr max 0 (list.map list.length ((x :: hd) :: tl)))) :=
⟨⟨hd.cases_on 0 1,
  by { cases hd;
       simp only [nat.succ_pos', nat.succ_lt_succ_iff, list.length,
                  pi.one_apply, lt_max_iff, true_or, list.foldr, list.map]}⟩⟩

instance board_fin0'' :
  has_zero (fin (((x : option K) :: hd') :: tl').join.reduce_option.length) :=
⟨⟨0, by simp only [nat.succ_pos', list.join, list.reduce_option_cons_of_some, list.cons_append,
                     list.length, option.coe_eq_some]⟩⟩

-- instance board_fin1'' {y : K} :
--   has_one (fin (((x : option K) :: hd') :: tl').join.reduce_option.length) :=
-- ⟨⟨1, by { simp only [nat.succ_pos', list.join, list.reduce_option_cons_of_some, list.cons_append,
--                      list.length, option.coe_eq_some], }⟩⟩
-- instance board_fin1'' :
--   has_one (fin ((some x :: hd') :: tl').join.reduce_option.length) :=
-- ⟨⟨1, by { simp [nat.succ_pos', list.join, list.reduce_option_cons_of_some, list.cons_append,
--                    list.length],  }⟩⟩

end fin_instance
