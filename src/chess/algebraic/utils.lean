import data.fintype.card
import utils.list

instance has_repr_sum {α β : Type*} [has_repr α] [has_repr β] : has_repr (α ⊕ β) :=
⟨sum.elim (λ x, "sum.inl " ++ repr x) (λ x, "sum.inr " ++ repr x)⟩

@[simp] lemma dlist_singleton {α : Type*} {a : α} :
  dlist.singleton a = dlist.lazy_of_list ([a]) := rfl

@[simp] lemma dlist_lazy {α : Type*} {l : list α} :
  dlist.lazy_of_list l = dlist.of_list l := rfl

open parser parse_result

@[simp] def parse_result.pos {α} : parse_result α → ℕ
| (done n _) := n
| (fail n _) := n

def parse_result.map {α β} (f : α → β) : parse_result α → parse_result β
| (done n a)   := done n (f a)
| (fail n err) := fail n err

def parse_result.map_const {α β} (b : β) : parse_result α → parse_result β
| (done n _)   := done n b
| (fail n err) := fail n err

instance : functor parse_result :=
{ map := λ _ _, parse_result.map,
  map_const := λ _ _, parse_result.map_const }

instance : is_lawful_functor parse_result :=
{ map_const_eq := λ _ _, funext (λ _, by { ext a, cases a; refl }),
  id_map := λ _, by { rintro (a | a); refl },
  comp_map := λ _ _ _ f g, by { rintro (a | a); refl } }

namespace parser

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

@[simp] lemma map_const_eq_done {b'} : (b <$ p) cb n = done n' b' ↔
  ∃ (a : α), p cb n = done n' a ∧ b = b' :=
by simp only [map_const_eq, function.const_apply, iff_self, map_eq_done]

@[simp] lemma map_const_eq_fail : (b <$ p) cb n = fail n' err ↔ p cb n = fail n' err :=
by simp only [map_const_eq, map_eq_fail]

lemma map_const_rev_eq_done {b'} : (p $> b) cb n = done n' b' ↔
  ∃ (a : α), p cb n = done n' a ∧ b = b' :=
map_const_eq_done

lemma map_rev_const_eq_fail : (p $> b) cb n = fail n' err ↔ p cb n = fail n' err :=
map_const_eq_fail

end map

@[simp] lemma orelse_eq_orelse : p.orelse q = (p <|> q) := rfl

@[simp] lemma orelse_eq_done : (p <|> q) cb n = done n' a ↔
  (p cb n = done n' a ∨ (q cb n = done n' a ∧ (∃ err, p cb n = fail n err))) :=
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
  { rintro (h | ⟨h', err, h⟩),
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

section valid

variables {sep : parser unit}

namespace valid

@[simp] lemma pure : valid (pure a) :=
by { intros cb n, simp only [pure_eq_done, parse_result.pos, imp_self, and_true] }

@[simp] lemma bind {f : α → parser β} (hp : p.valid) (hf : ∀ a, (f a).valid) :
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

lemma and_then {q : parser β} (hp : p.valid) (hq : q.valid) : (p >> q).valid :=
hp.bind (λ _, hq)

@[simp] lemma map (hp : p.valid) {f : α → β} : (f <$> p).valid :=
hp.bind (λ _, pure)

@[simp] lemma seq {f : parser (α → β)} (hf : f.valid) (hp : p.valid) : (f <*> p).valid :=
hf.bind (λ _, hp.map)

@[simp] lemma mmap {l : list α} {f : α → parser β} (h : ∀ a ∈ l, (f a).valid) :
  (l.mmap f).valid :=
begin
  induction l with hd tl hl generalizing h,
  { exact pure },
  { exact bind (h _ (list.mem_cons_self _ _))
      (λ b, map (hl (λ _ ha, h _ (list.mem_cons_of_mem _ ha)))) }
end

@[simp] lemma mmap' {l : list α} {f : α → parser β} (h : ∀ a ∈ l, (f a).valid) :
  (l.mmap' f).valid :=
begin
  induction l with hd tl hl generalizing h,
  { exact pure },
  { refine and_then (h _ (list.mem_cons_self _ _))
      (hl (λ _ ha, h _ (list.mem_cons_of_mem _ ha))) }
end

@[simp] lemma failure : @parser.valid α failure :=
begin
  simp only [failure_def, valid, imp_self, and_true, parse_result.pos],
  rintro - _,
  refl
end

@[simp] lemma guard {p : Prop} [decidable p] : valid (guard p) :=
by simp only [guard, apply_ite valid, pure, failure, or_true, if_true_left_eq_or]

@[simp] lemma orelse (hp : p.valid) (hq : q.valid) : (p <|> q).valid :=
begin
  intros cb n,
  cases hx : (p <|> q) cb n with posx resx posx errx,
  { obtain h | ⟨h', err, h⟩ := orelse_eq_done.mp hx,
    { simpa only [h] using hp cb n },
    { simpa only [h'] using hq cb n } },
  { by_cases h : n = posx,
    { simp only [hx, h, imp_self, and_true, parse_result.pos] },
    { rw orelse_eq_fail_of_valid_ne hq h at hx,
      simpa only [parse_result.pos, hx] using hp cb n } }
end

@[simp] lemma decorate_errors (hp : p.valid) :
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

@[simp] lemma decorate_error (hp : p.valid) : (@decorate_error α msg p).valid :=
decorate_errors hp

@[simp] lemma any_char : valid any_char :=
begin
  intros cb n,
  simp only [any_char],
  split_ifs,
  { simpa only [true_and, zero_le, le_add_iff_nonneg_right,
                parse_result.pos] using nat.le_of_succ_le},
  { simp only [imp_self, and_true, parse_result.pos] }
end

@[simp] lemma sat {p : char → Prop} [decidable_pred p] : valid (sat p) :=
begin
  intros cb n,
  simp only [sat],
  split_ifs,
  { simpa only [true_and, zero_le, le_add_iff_nonneg_right,
                parse_result.pos] using nat.le_of_succ_le },
  { simp only [imp_self, and_true, parse_result.pos] },
  { simp only [parse_result.pos, imp_self, and_true] }
end

@[simp] lemma eps : valid eps := pure

lemma ch {c : char} : valid (ch c) := decorate_error (sat.and_then eps)

lemma char_buf {s : char_buffer} : valid (char_buf s) :=
decorate_error (mmap' (λ _ _, ch))

lemma one_of {cs : list char} : (one_of cs).valid :=
decorate_errors sat

lemma one_of' {cs : list char} : (one_of' cs).valid :=
one_of.and_then eps

lemma str {s : string} : (str s).valid :=
decorate_error (mmap' (λ _ _, ch))

lemma remaining : remaining.valid :=
λ _ _, ⟨le_refl _, λ h, h⟩

lemma eof : eof.valid :=
decorate_error (remaining.bind (λ _, guard))

lemma foldr_core {f : α → β → β} {b : β} (hp : p.valid) :
  ∀ {reps : ℕ}, (foldr_core f p b reps).valid
| 0          := failure
| (reps + 1) := orelse (hp.bind (λ _, foldr_core.bind (λ _, pure))) pure

lemma foldr {f : α → β → β} (hp : p.valid) : valid (foldr f p b) :=
λ _ _, foldr_core hp _ _

lemma foldl_core {f : α → β → α} {p : parser β} (hp : p.valid) :
  ∀ {a : α} {reps : ℕ}, (foldl_core f a p reps).valid
| _ 0          := failure
| _ (reps + 1) := orelse (hp.bind (λ _, foldl_core)) pure

lemma foldl {f : α → β → α} {p : parser β} (hp : p.valid) : valid (foldl f a p) :=
λ _ _, foldl_core hp _ _

lemma many (hp : p.valid) : p.many.valid :=
hp.foldr

lemma many_char {p : parser char} (hp : p.valid) : p.many_char.valid :=
hp.many.map

lemma many' (hp : p.valid) : p.many'.valid :=
hp.many.and_then eps

lemma many1 (hp : p.valid) : p.many1.valid :=
hp.map.seq hp.many

lemma many_char1 {p : parser char} (hp : p.valid) : p.many_char1.valid :=
hp.many1.map

lemma sep_by1 {sep : parser unit} (hp : p.valid) (hs : sep.valid) : valid (sep_by1 sep p) :=
hp.map.seq (hs.and_then hp).many

lemma sep_by {sep : parser unit} (hp : p.valid) (hs : sep.valid) : valid (sep_by sep p) :=
(hp.sep_by1 hs).orelse pure

lemma fix_core {F : parser α → parser α} (hF : ∀ (p : parser α), p.valid → (F p).valid) :
  ∀ (max_depth : ℕ), valid (fix_core F max_depth)
| 0               := failure
| (max_depth + 1) := hF _ (fix_core _)

lemma digit : digit.valid :=
decorate_error (sat.bind (λ _, pure))

lemma nat : nat.valid :=
decorate_error (digit.many1.bind (λ _, pure))

lemma fix {F : parser α → parser α} (hF : ∀ (p : parser α), p.valid → (F p).valid) :
  valid (fix F) :=
λ _ _, fix_core hF _ _ _

end valid

end valid

end defn_lemmas

section numeral

variables (α : Type) [has_zero α] [has_one α] [has_add α]

def numeral : parser α :=
nat.cast <$> nat

def numeral.of_fintype [fintype α] : parser α :=
do
  c ← nat,
  guard (c < fintype.card α),
  pure c

def numeral.from_one : parser α :=
do
  c ← nat,
  guard (0 < c),
  pure $ ((c - 1) : ℕ)

def numeral.from_one.of_fintype [fintype α] : parser α :=
do
  c ← nat,
  guard (0 < c ∧ c ≤ fintype.card α),
  pure $ ((c - 1) : ℕ)

def numeral.char (fromc toc : char) : parser α :=
do
  c ← sat (λ c, fromc ≤ c ∧ c ≤ toc),
  pure $ ((c.to_nat - fromc.to_nat) : ℕ)

def numeral.char.of_fintype [fintype α] (fromc : char) : parser α :=
do
  c ← sat (λ c, fromc ≤ c ∧ c.to_nat - fintype.card α < fromc.to_nat),
  pure $ ((c.to_nat - fromc.to_nat) : ℕ)

variable {α}

namespace valid

lemma numeral : valid (numeral α) := nat.map

lemma numeral.of_fintype [fintype α] : valid (numeral.of_fintype α) :=
nat.bind (λ _, guard.bind (λ _, pure))

lemma numeral.from_one : valid (numeral.from_one α) :=
nat.bind (λ _, guard.bind (λ _, pure))

lemma numeral.from_one.of_fintype [fintype α] : valid (numeral.from_one.of_fintype α) :=
nat.bind (λ _, guard.bind (λ _, pure))

lemma numeral.char {fromc toc : char} : valid (numeral.char α fromc toc) :=
sat.bind (λ _, pure)

lemma numeral.char.of_fintype [fintype α] {fromc : char} :
  valid (numeral.char.of_fintype α fromc) :=
sat.bind (λ _, pure)

end valid

end numeral

lemma ch_of_empty (c : char) (cb : char_buffer) (h : cb.size = 0) (n : ℕ) :
  ch c cb n = parse_result.fail n (dlist.singleton c.to_string) :=
by simp [ch, sat, h, and_then_eq_bind, dlist_singleton, decorate_error_failure_iff, not_lt,
         eq_self_iff_true, exists_false, zero_le, or_false, dif_neg, exists_eq_right', and_self,
         bind_eq_fail, exists_eq', false_and]

section mem

variables {α β : Type}

def mem (p : parser α) (a : α) : Prop :=
∃ (cb : char_buffer) (n n' : ℕ), p cb n = done n' a

instance : has_mem α (parser α) := ⟨λ a p, p.mem a⟩

instance char_buffer.inhabited : inhabited char_buffer := sigma.inhabited

variables {p q : parser α} {a : α} {b : β} {cb : char_buffer} {n n' : ℕ} {err : dlist string}

lemma mem_def : a ∈ p = ∃ (cb : char_buffer) (n n' : ℕ), p cb n = done n' a := rfl

lemma mem_def_iff : a ∈ p ↔ ∃ (cb : char_buffer) (n n' : ℕ), p cb n = done n' a := iff.rfl

lemma mem_of_done (h : p cb n = done n' a) : a ∈ p :=
⟨cb, n, n', h⟩

@[simp] lemma mem_pure (a) : a ∈ (pure a : parser α) :=
by simp only [mem_def, and_true, eq_self_iff_true, pure_eq_done, exists_eq', exists_const]

@[simp] lemma mem_decorate_errors_iff {errs} :
  a ∈ decorate_errors errs p ↔ a ∈ p :=
by simp only [mem_def, decorate_errors_success_iff]

@[simp] lemma mem_decorate_error_iff {err} :
  a ∈ decorate_error err p ↔ a ∈ p :=
by simp only [mem_def, decorate_error_success_iff]

@[simp] lemma mem_map (h : a ∈ p) ⦃f : α → β⦄ : f a ∈ f <$> p :=
begin
  obtain ⟨cb, n, n', h⟩ := h,
  simp only [mem_def, map_eq_done],
  exact ⟨cb, n, n', a, h, rfl⟩
end

@[simp] lemma mem_of_map {f : α → β} (h : b ∈ f <$> p) : ∃ (a : α), a ∈ p :=
begin
  obtain ⟨_, _, _, h⟩ := h,
  obtain ⟨_, h, -⟩ := map_eq_done.mp h,
  exact ⟨_, mem_of_done h⟩
end

@[simp] lemma mem_map_of_injective_iff {f : α → β} (hf : function.injective f) :
  f a ∈ f <$> p ↔ a ∈ p :=
by simp only [mem_def, hf, function.injective.eq_iff, map_eq_done, exists_eq_right]

@[simp] lemma mem_map_const_iff {f : β} :
  b ∈ f <$ p ↔ f = b ∧ ∃ (a : α), a ∈ p :=
begin
  simp only [mem_def, and_comm, exists_and_distrib_left, map_const_eq_done, and.congr_right_iff],
  rintro -,
  split;
  { rintro ⟨_, _, _, _, h⟩,
    exact ⟨_, _, _, _, h⟩ }
end

lemma mem_map_const_rev_iff {f : β} :
  b ∈ p $> f ↔ f = b ∧ ∃ (a : α), a ∈ p :=
mem_map_const_iff

lemma mem_orelse_iff :
  a ∈ (p <|> q) ↔ a ∈ p ∨ (∃ cb n n', q cb n = done n' a ∧ ∃ err, p cb n = fail n err) :=
begin
  simp only [mem_def, orelse_eq_done],
  split,
  { rintro ⟨_, _, _, h | ⟨h, _, h'⟩⟩,
    { exact or.inl ⟨_, _, _, h⟩ },
    { exact or.inr ⟨_, _, _, h, _, h'⟩ } },
  { rintro (⟨_, _, _, h⟩ | ⟨_, _, _, h, h'⟩),
    { exact ⟨_, _, _, or.inl h⟩ },
    { exact ⟨_, _, _, or.inr ⟨h, h'⟩⟩ } }
end

lemma mem_of_mmap {f : α → parser β} {la : list α} {lb : list β} (h : lb ∈ la.mmap f) :
  ∀ b ∈ lb, ∃ a ∈ la, b ∈ f a :=
begin
  induction lb with hd tl hl generalizing la,
  { simp only [list.not_mem_nil, forall_prop_of_false, not_false_iff, forall_true_iff] },
  { cases la with hd' tl',
    { simpa only [mem_def, list.mmap_nil, exists_false, pure_eq_done, and_false] using h },
    { simp only [mem_def, list.mmap_cons, bind_eq_done, pure_eq_done] at h,
      obtain ⟨_, _, _, _, _, hx, _, _, h, rfl, rfl, rfl⟩ := h,
      rintros b (rfl | hb),
      { exact ⟨hd', list.mem_cons_self _ _, mem_of_done hx⟩ },
      { obtain ⟨a, ha, ha'⟩ := hl ⟨_, _, _, h⟩ b hb,
        refine ⟨a, list.mem_cons_of_mem _ ha, ha'⟩ } } }
end

lemma mem_of_mfirst {α β} {f : α → parser β} {l : list α} {b}
  (h : b ∈ list.mfirst f l) :
    ∃ p ∈ f <$> l, b ∈ p :=
begin
  induction l with hd tl hl,
  { simpa [mem_def, list.mfirst] using h },
  { simp only [list.mfirst, mem_orelse_iff] at h,
    rcases h with h | ⟨_, _, _, h, -⟩,
    { exact ⟨_, list.mem_cons_self _ _, h⟩, },
    { obtain ⟨p, hp, hp'⟩ := hl (mem_of_done h),
      exact ⟨p, list.mem_cons_of_mem _ hp, hp'⟩ } }
end

end mem

section pmap

variables {α β : Type}

def pmap (p : parser α) {P : α → Prop} (f : Π a, P a → β) (H : ∀ a ∈ p, P a) :
  parser β :=
λ cb n, by clean begin
  cases ha : (p cb n) with n' a n' err,
  { exact done n' (f a (H a ⟨cb, n, n', ha⟩)) },
  { exact fail n' err }
end

def attach (p : parser α) {P : α → Prop} (H : ∀ a ∈ p, P a) : parser {a // P a} :=
pmap p subtype.mk H

end pmap

section option

variables {α : Type} {p : parser α}

def option (p : parser α) : parser (option α) :=
some <$> p <|> pure none

lemma valid.option (h : p.valid) : p.option.valid :=
h.map.orelse valid.pure

@[simp] lemma mem_option_some_iff {a : α} :
  some a ∈ p.option ↔ a ∈ p :=
by simp only [option, mem_orelse_iff, option.some_injective, exists_false, or_false,
              pure_eq_done, and_false, false_and, mem_map_of_injective_iff]

end option

section try

variables {α : Type} {p : parser α}

def try (p : parser α) : parser α :=
λ cb n, match p cb n with
| (fail _ err) := fail n err
| ok := ok
end

@[simp] lemma try_of_done_iff {cb n n' a} :
  p.try cb n = done n' a ↔ p cb n = done n' a :=
by cases hp : p cb n; simp only [hp, try, iff_self]

@[simp] lemma try_of_fail_iff {cb n n' err} :
  p.try cb n = fail n' err ↔ n = n' ∧ ∃ np, p cb n = fail np err :=
begin
  cases hp : p cb n;
  simp only [try, hp, exists_false, and_false, iff_self, exists_eq_left']
end

lemma valid.try (h : p.valid) : p.try.valid :=
begin
  intros cb n,
  cases hp : p cb n,
  { simpa only [try, hp] using h cb n },
  { simp only [try, hp, imp_self, and_true, parse_result.pos] }
end

@[simp] lemma mem_try_iff {a : α} : a ∈ p.try ↔ a ∈ p :=
by simp [mem_def]

end try

end parser
