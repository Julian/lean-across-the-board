import data.nat.cast
import data.fintype.card
import utils.list

instance has_repr_sum {α β : Type*} [has_repr α] [has_repr β] : has_repr (α ⊕ β) :=
⟨sum.elim (λ x, "sum.inl " ++ repr x) (λ x, "sum.inr " ++ repr x)⟩

@[simp] lemma dlist_singleton {α : Type*} {a : α} : dlist.singleton a = dlist.lazy_of_list ([a]) := rfl

open parser parse_result

@[simp] def parse_result.pos {α} : parse_result α → ℕ
| (done n _) := n
| (fail n _) := n

namespace parser

section numeral

def numeral (α : Type) [has_zero α] [has_one α] [has_add α] : parser α :=
nat.cast <$> nat

def numeral.of_fintype (α : Type) [has_zero α] [has_one α] [has_add α] [fintype α] : parser α :=
do
  c ← nat,
  guard (c < fintype.card α),
  pure c

def numeral.from_one (α : Type) [has_zero α] [has_one α] [has_add α] : parser α :=
do
  c ← nat,
  guard (0 < c),
  pure $ ((c - 1) : ℕ)

def numeral.from_one.of_fintype (α : Type) [has_zero α] [has_one α] [has_add α] [fintype α] : parser α :=
do
  c ← nat,
  guard (0 < c),
  guard (c ≤ fintype.card α),
  pure $ ((c - 1) : ℕ)

def numeral.char (fromc toc : char) (α : Type) [has_zero α] [has_one α] [has_add α] : parser α :=
do
  c ← sat (λ c, fromc ≤ c ∧ c ≤ toc),
  pure $ ((c.to_nat - fromc.to_nat) : ℕ)

def numeral.char.of_fintype (fromc : char) (α : Type) [has_zero α] [has_one α] [has_add α]
  [fintype α] : parser α :=
do
  c ← sat (λ c, fromc ≤ c ∧ c.to_nat - fintype.card α < fromc.to_nat),
  pure $ ((c.to_nat - fromc.to_nat) : ℕ)

end numeral

section defn_lemmas

variables {α β : Type} (msgs : thunk (list string)) (msg : thunk string)
variables (p q : parser α) (cb : char_buffer) (n n' : ℕ) {err : dlist string}
variables {a : α} {b : β}

@[simp] def failed : Prop :=
  ∃ (n' : ℕ) (err : dlist string), p cb n = fail n' err

def valid : Prop :=
  ∀ (cb : char_buffer) (n : ℕ), n ≤ (p cb n).pos ∧ ((p cb n).pos ≤ cb.size → n ≤ cb.size)

lemma fail_iff :
  (∀ pos' result, p cb n ≠ done pos' result) ↔ ∃ (pos' : ℕ) (err : dlist string), p cb n = fail pos' err :=
begin
  cases p cb n,
  { simp [exists_prop, not_not, exists_false, exists_eq_right',
               iff_false, exists_eq', not_forall] },
  { simp only [forall_const, ne.def, not_false_iff, exists_eq_right',
               exists_eq', forall_true_iff] }
end

lemma fail_iff' :
  (∀ pos' result, p cb n ≠ done pos' result) ↔ p.failed cb n :=
by { rw failed, exact fail_iff _ _ _ }

lemma success_iff :
  (∀ pos' err, p cb n ≠ fail pos' err) ↔ ∃ (pos' : ℕ) (result : α), p cb n = done pos' result :=
begin
  cases p cb n,
  { simp only [exists_eq_right', exists_eq', forall_const, ne.def, not_false_iff, forall_true_iff] },
  { simp only [exists_eq_right', exists_eq', exists_prop, not_not, exists_false, iff_false,
               not_forall] }
end

lemma success_iff' :
  (¬ p.failed cb n) ↔ ∃ (pos' : ℕ) (result : α), p cb n = done pos' result :=
by simp only [failed, not_exists, success_iff]

variables {p q cb n n' msgs msg}

lemma decorate_errors_fail (h : p cb n = fail n' err) :
  @decorate_errors α msgs p cb n = fail n ((dlist.lazy_of_list (msgs ()))) :=
begin
  dunfold decorate_errors,
  rw h,
  refl
end

lemma decorate_errors_success (h : p cb n = done n' a) :
  @decorate_errors α msgs p cb n = done n' a :=
begin
  dunfold decorate_errors,
  rw h,
  refl
end

lemma decorate_error_fail (h : p cb n = fail n' err) :
  @decorate_error α msg p cb n = fail n ((dlist.lazy_of_list ([msg ()]))) :=
decorate_errors_fail h

lemma decorate_error_success (h : p cb n = done n' a) :
  @decorate_error α msg p cb n = done n' a :=
decorate_errors_success h

@[simp] lemma decorate_errors_success_iff :
  @decorate_errors α msgs p cb n = done n' a ↔ p cb n = done n' a :=
begin
  dunfold decorate_errors,
  cases p cb n,
  { rw decorate_errors },
  { rw decorate_errors,
    simp only }
end

@[simp] lemma decorate_error_success_iff :
  @decorate_error α msg p cb n = done n' a ↔ p cb n = done n' a :=
decorate_errors_success_iff

@[simp] lemma decorate_errors_failure_iff :
  @decorate_errors α msgs p cb n = fail n err ↔
    err = dlist.lazy_of_list (msgs ()) ∧ ∃ np err', p cb n = fail np err' :=
begin
  dunfold decorate_errors,
  cases p cb n,
  { rw decorate_errors,
    simp only [exists_false, and_false] },
  { rw decorate_errors,
    simp only [true_and, and_true, eq_self_iff_true, exists_eq_right', exists_eq', eq_comm] }
end

@[simp] lemma decorate_error_failure_iff :
  @decorate_error α msg p cb n = fail n err ↔
    err = dlist.lazy_of_list ([msg ()]) ∧ ∃ np err', p cb n = fail np err' :=
decorate_errors_failure_iff

@[simp] lemma return_eq_pure : (@return parser _ _ a) = pure a := rfl

@[simp] lemma pure_eq_done : (@pure parser _ _ a) = λ _ n, done n a := rfl


section bind

variable {f : α → parser β}

@[simp] lemma bind_eq_bind : p.bind f = p >>= f := rfl

@[simp] lemma bind_eq_done :
  (p >>= f) cb n = done n' b ↔
  ∃ (np : ℕ) (a : α), p cb n = done np a ∧ f a cb np = done n' b :=
begin
  split,
  { intro h,
    simp_rw [←bind_eq_bind, parser.bind] at h,
    cases p cb n with pos r pos err,
    { refine ⟨pos, r, rfl, _⟩,
      rw ←h,
      refl },
    { simpa only using h } },
  { rintro ⟨r, pos, h⟩,
    simp only [h, ←bind_eq_bind, parser.bind, eq_self_iff_true, and_self] }
end

@[simp] lemma bind_eq_fail :
  (p >>= f) cb n = fail n' err ↔
  (p cb n = fail n' err) ∨ (∃ (np : ℕ) (a : α), p cb n = done np a ∧ f a cb np = fail n' err)
  :=
begin
  split,
  { intro h,
    simp_rw [←bind_eq_bind, parser.bind] at h,
    cases p cb n with pos r pos err,
    { rw ←h,
      simp only [false_or, exists_false],
      refine ⟨pos, r, by simp only [eq_self_iff_true, and_self], _⟩,
      refl },
    { simpa only [parser.bind, exists_false, or_false, false_and] using h } },
  { rintro (h | ⟨r, n', h, h'⟩),
    { simp only [←bind_eq_bind, parser.bind, h, eq_self_iff_true, and_self] },
    { simp only [←h', ←bind_eq_bind, parser.bind, h] } }
end

@[simp] lemma and_then_eq_bind {α β : Type} {m : Type → Type} [monad m] (a : m α) (b : m β) :
  a >> b = a >>= (λ _, b) := rfl

lemma and_then_fail :
  (p >> return ()) cb n = parse_result.fail n' err ↔ p cb n = fail n' err :=
by simp only [and_then_eq_bind, return_eq_pure, exists_false, or_false, pure_eq_done,
              bind_eq_fail, and_false]

lemma and_then_success :
  (p >> return ()) cb n = parse_result.done n' () ↔ ∃ a, p cb n = done n' a:=
by simp only [pure_eq_done, and_then_eq_bind, and_true, bind_eq_done, exists_eq_right,
              eq_iff_true_of_subsingleton, return_eq_pure, exists_and_distrib_right]

lemma mmap_empty_eq_done {l : list α} {lb : list β} :
  list.nil.mmap f cb n = done n' lb ↔ n = n' ∧ lb = [] :=
by simp only [eq_comm, pure_eq_done, list.mmap_nil]

lemma mmap_cons_eq_done {a : α} {l : list α} {b : β} {lb : list β} :
  (a :: l).mmap f cb n = done n' (b :: lb) ↔
  ∃ (na : ℕ), f a cb n = done na b ∧ l.mmap f cb na = done n' lb :=
begin
  simp only [list.mmap_cons, bind_eq_done, pure_eq_done],
  split,
  { rintro ⟨np, b', h, lb', np', h', rfl, rfl, rfl⟩,
    exact ⟨np, h, h'⟩ },
  { rintro ⟨np, h, h'⟩,
    exact ⟨np, b, h, n', lb, h', rfl, rfl, rfl⟩ }
end

lemma mmap_imp_fail {l : list α} (h : l.mmap f cb n = fail n' err) :
    ∃ (a ∈ l) (np : ℕ), f a cb np = fail n' err :=
begin
  induction l with hd tl hl generalizing n n',
  { simpa only using h },
  { simp only [list.mmap_cons, exists_false, or_false, pure_eq_done, bind_eq_fail, and_false] at h,
    simp only [exists_prop, list.mem_cons_iff],
    rcases h with h | ⟨b, nb, hb, h⟩,
    { exact ⟨hd, or.inl rfl, n, h⟩, },
    { obtain ⟨a, ha, h'⟩ := hl h,
      exact ⟨a, or.inr ha, h'⟩ } }
end

lemma mmap'_empty_eq_done {l : list α} {lb : list β} :
  list.nil.mmap' f cb n = done n' () ↔ n = n' :=
by simp only [pure_eq_done, list.mmap'_nil, and_true, eq_iff_true_of_subsingleton]

lemma mmap'_cons_eq_done {l : list α} :
  (a :: l).mmap' f cb n = done n' () ↔
  ∃ (na : ℕ) (b : β), f a cb n = done na b ∧ l.mmap' f cb na = done n' () :=
by simp only [bind_eq_done, and_then_eq_bind, list.mmap'_cons]

lemma mmap'_imp_fail {l : list α} (h : l.mmap' f cb n = fail n' err) :
    ∃ (a ∈ l) (np : ℕ), f a cb np = fail n' err :=
begin
  induction l with hd tl hl generalizing n n',
  { simpa only using h },
  { simp only [bind_eq_fail, and_then_eq_bind, exists_and_distrib_right, list.mmap'_cons] at h,
    simp only [exists_prop, list.mem_cons_iff],
    rcases h with h | ⟨nb, -, h⟩,
    { exact ⟨hd, or.inl rfl, n, h⟩, },
    { obtain ⟨a, ha, h'⟩ := hl h,
      exact ⟨a, or.inr ha, h'⟩ } }
end

end bind

section map

variable {f : α → β}

@[simp] lemma map_eq_done : (f <$> p) cb n = done n' b ↔
  ∃ (a : α), p cb n = done n' a ∧ f a = b :=
begin
  rw ←is_lawful_monad.bind_pure_comp_eq_map,
  simp only [bind_eq_done, function.comp_app, pure_eq_done],
  split,
  { rintro ⟨np, a, h, rfl, rfl⟩,
    exact ⟨a, h, rfl⟩ },
  { rintro ⟨a, h, rfl⟩,
    exact ⟨n', a, h, rfl, rfl⟩ }
end

@[simp] lemma map_eq_fail : (f <$> p) cb n = fail n' err ↔ p cb n = fail n' err :=
by simp only [←bind_pure_comp_eq_map, exists_false, function.comp_app, or_false, pure_eq_done,
              bind_eq_fail, and_false]

end map

@[simp] lemma orelse_eq_orelse : p.orelse q = (p <|> q) := rfl

@[simp] lemma orelse_eq_done : (p <|> q) cb n = done n' a ↔
  (p cb n = done n' a ∨ ((∃ err, p cb n = fail n err) ∧ q cb n = done n' a)) :=
begin
  rw ←orelse_eq_orelse,
  split,
  { intro h,
    simp_rw parser.orelse at h,
    cases p cb n with posp resp posp errp,
    { left,
      simpa only [parser.orelse] using h },
    { right,
      simp only [parser.orelse, ite_not] at h,
      split_ifs at h with H H,
      { cases q cb n with posq resq posq errq,
        { simp only [parser.orelse] at h,
          simp only [true_and, exists_eq', H, eq_self_iff_true, h] },
        { simp only [parser.orelse] at h,
          split_ifs at h;
          exact h.elim } },
      { exact h.elim } } },
  { rintro (h | ⟨⟨err, h⟩, h'⟩),
    { simp only [parser.orelse, h, eq_self_iff_true, and_self] },
    { simp only [h, parser.orelse, eq_self_iff_true, not_true, if_false, ne.def],
      cases q cb n with posq resq posq errq,
      { simpa only [parser.orelse] using h' },
      { simpa only using h' } } }
end

@[simp] lemma orelse_eq_fail_eq : (p <|> q) cb n = fail n err ↔
  (p cb n = fail n err ∧ ∃ (nq errq), n < nq ∧ q cb n = fail nq errq) ∨
  (∃ (errp errq), p cb n = fail n errp ∧ q cb n = fail n errq ∧ errp ++ errq = err)
 :=
begin
  rw ←orelse_eq_orelse,
  simp only [parser.orelse, exists_and_distrib_left],
  cases p cb n with posp resp posp errp,
  { simp only [parser.orelse, exists_false, false_and, or_self] },
  by_cases h : posp = n,
  { simp only [h, parser.orelse, true_and, eq_self_iff_true, not_true, if_false, ne.def,
               exists_eq_left'],
    cases q cb n with posq resq posq errq,
    { simp only [parser.orelse, exists_false, and_false, false_and, or_self] },
    { simp only [parser.orelse, exists_eq_right'],
      split_ifs with H H',
      { simp only [H, true_and, and_true, eq_self_iff_true, ne_of_gt H, exists_false, or_false,
                   false_and] },
      { have hn : posq ≠ n := ne_of_lt H',
        have hl : posq ≤ n := le_of_not_lt H,
        simp only [hn, hl, false_iff, not_and, not_lt, exists_false, or_false, false_and,
                   forall_true_iff] },
      { have : posq = n := le_antisymm (le_of_not_lt H) (le_of_not_lt H'),
        simp only [this, lt_irrefl, true_and, false_or, eq_self_iff_true, exists_eq_left',
                   and_false] } } },
  { simp only [h, parser.orelse, if_true, exists_false, ne.def, not_false_iff, false_and, or_self] },
end

lemma orelse_eq_fail_invalid_lt (hn : n' < n) : (p <|> q) cb n = fail n' err ↔
  (p cb n = fail n' err) ∨
  (q cb n = fail n' err ∧ (∃ (errp), p cb n = fail n errp))
 :=
begin
  rw ←orelse_eq_orelse,
  simp only [parser.orelse, exists_and_distrib_left],
  cases p cb n with posp resp posp errp,
  { simp only [parser.orelse, exists_false, or_self, and_false] },
  by_cases h : posp = n,
  { simp only [h, parser.orelse, true_and, eq_self_iff_true, not_true, if_false, ne.def, and_true,
               false_or, exists_eq', false_and, ne_of_gt hn],
    cases q cb n with posq resq posq errq,
    { simp only [parser.orelse, not_false_iff] },
    { simp only [parser.orelse],
      split_ifs with H H',
      { have : posq ≠ n' := ne_of_gt (lt_trans hn H),
        simp only [false_and, ne_of_gt hn, this] },
      { simp only [iff_self] },
      { have : posq = n := le_antisymm (le_of_not_lt H) (le_of_not_lt H'),
        simp only [ne_of_gt hn, this, false_and] } } },
  { simp only [h, parser.orelse, if_true, exists_false, ne.def, not_false_iff, false_and,
               or_false, and_false] },
end

lemma orelse_eq_fail_of_valid_ne (hq : q.valid) (hn : n ≠ n') :
  (p <|> q) cb n = fail n' err ↔ p cb n = fail n' err
 :=
begin
  rw ←orelse_eq_orelse,
  simp only [parser.orelse, exists_and_distrib_left],
  cases p cb n with posp resp posp errp,
  { simp [parser.orelse, exists_false, or_self, and_false] },
  by_cases h : posp = n,
  { simp only [h, parser.orelse, true_and, eq_self_iff_true, not_true, if_false, ne.def,
               hn, and_true, false_or, exists_eq', false_and],
    specialize hq cb n,
    cases q cb n with posq resq posq errq,
    { simp [parser.orelse] },
    { simp only [parser.orelse, if_false],
      simp only [parse_result.pos] at hq,
      rcases eq_or_lt_of_le hq.left with rfl|H,
      { simp only [lt_irrefl, hn, if_false, false_and] },
      { simp only [H, if_true, hn, false_and] } } },
  { simp only [h, parser.orelse, if_true, ne.def, not_false_iff] },
end

@[simp] lemma parser_eq_parser : @parser.failure α = failure := rfl

@[simp] lemma failure_def : (failure : parser α) cb n = fail n dlist.empty := rfl

lemma ch_of_empty (c : char) (cb : char_buffer) (h : cb.size = 0) (n : ℕ) :
  ch c cb n = parse_result.fail n (dlist.singleton c.to_string) :=
begin
  rw ch,
  rw sat,
  rw eps,
  simp only [pure_eq_done, and_then_eq_bind, decorate_error_failure_iff, true_and, dlist_singleton,
             eq_self_iff_true],
  use [n, dlist.empty],
  simp only [h, not_lt, eq_self_iff_true, exists_false, zero_le, or_false, dif_neg, and_self,
             bind_eq_fail, return_eq_pure, pure_eq_done]
end

section valid_parsers

lemma pure.valid : valid (pure a) :=
by { intros cb n, simp only [pure_eq_done, parse_result.pos, imp_self, and_true] }

@[simp] lemma valid.bind {f : α → parser β} (hp : p.valid) (hf : ∀ a, (f a).valid) :
  (p >>= f).valid :=
begin
  intros cb n,
  specialize hp cb n,
  cases hx : (p >>= f) cb n,
  { obtain ⟨n', a, h, h'⟩ := bind_eq_done.mp hx,
    specialize hf a cb n',
    simp only [h', parse_result.pos] at hf,
    simp only [h, parse_result.pos] at hp,
    simp only [parse_result.pos],
    split,
    { exact le_trans hp.left hf.left },
    { intro hn,
      simp [hn, hf, hp] } },
  { obtain h | ⟨n', a, h, h'⟩ := bind_eq_fail.mp hx,
    { simpa only [h] using hp },
    { specialize hf a cb n',
      simp only [h', parse_result.pos] at hf,
      simp only [h, parse_result.pos] at hp,
      simp only [parse_result.pos],
      split,
      { exact le_trans hp.left hf.left },
      { intro hn,
        simp only [hn, hf, hp] } } },
end

lemma valid.and_then {q : parser β} (hp : p.valid) (hq : q.valid) :
  (p >> q).valid :=
by { rw [and_then_eq_bind], exact hp.bind (λ _, hq) }

@[simp] lemma valid.map (hp : p.valid) {f : α → β} : (f <$> p).valid :=
by { rw ←is_lawful_monad.bind_pure_comp_eq_map, exact hp.bind (λ _, pure.valid) }

@[simp] lemma valid.mmap {l : list α} {f : α → parser β} (h : ∀ a ∈ l, (f a).valid) :
  (l.mmap f).valid :=
begin
  induction l with hd tl hl generalizing h,
  { exact pure.valid },
  { exact valid.bind (h _ (list.mem_cons_self _ _))
      (λ b, valid.map (hl (λ _ ha, h _ (list.mem_cons_of_mem _ ha)))) }
end

@[simp] lemma valid.mmap' {l : list α} {f : α → parser β} (h : ∀ a ∈ l, (f a).valid) :
  (l.mmap' f).valid :=
begin
  induction l with hd tl hl generalizing h,
  { exact pure.valid },
  { refine valid.and_then (h _ (list.mem_cons_self _ _))
      (hl (λ _ ha, h _ (list.mem_cons_of_mem _ ha))) }
end

@[simp] lemma failure.valid : @parser.valid α failure :=
begin
  simp only [failure_def, valid, imp_self, and_true, parse_result.pos],
  rintro - _,
  refl
end

@[simp] lemma valid.orelse (hp : p.valid) (hq : q.valid) : (p <|> q).valid :=
begin
  intros cb n,
  cases hx : (p <|> q) cb n with posx resx posx errx,
  { obtain h | ⟨⟨err, h⟩, h'⟩ := orelse_eq_done.mp hx,
    { simpa only [h] using hp cb n },
    { simpa only [h'] using hq cb n } },
  { by_cases h : n = posx,
    { simp only [hx, h, imp_self, and_true, parse_result.pos] },
    { rw orelse_eq_fail_of_valid_ne hq h at hx,
      simpa only [parse_result.pos, hx] using hp cb n } }
end

@[simp] lemma decorate_errors.valid (hp : p.valid) :
  (@decorate_errors α msgs p).valid :=
begin
  dunfold decorate_errors,
  intros cb n,
  specialize hp cb n,
  dsimp only,
  cases p cb n,
  { simpa only using hp },
  { simp only [decorate_errors, imp_self, and_true, parse_result.pos] },
end

@[simp] lemma decorate_error.valid (hp : p.valid) : (@decorate_error α msg p).valid :=
decorate_errors.valid hp

@[simp] lemma any_char.valid : valid any_char :=
begin
  intros cb n,
  simp only [any_char],
  split_ifs,
  { simpa only [true_and, zero_le, le_add_iff_nonneg_right,
                parse_result.pos] using nat.le_of_succ_le},
  { simp only [imp_self, and_true, parse_result.pos] }
end

@[simp] lemma sat.valid {p : char → Prop} [decidable_pred p] : valid (sat p) :=
begin
  intros cb n,
  simp only [sat],
  split_ifs,
  { simpa only [true_and, zero_le, le_add_iff_nonneg_right,
                parse_result.pos] using nat.le_of_succ_le },
  { simp only [imp_self, and_true, parse_result.pos] },
  { simp only [parse_result.pos, imp_self, and_true] }
end

@[simp] lemma eps.valid : valid eps := pure.valid

lemma ch.valid {c : char} : valid (ch c) := decorate_error.valid (sat.valid.and_then eps.valid)

lemma char_buf.valid {s : char_buffer} : valid (char_buf s) :=
decorate_error.valid (valid.mmap' (λ _ _, ch.valid))

end valid_parsers

end defn_lemmas

end parser
