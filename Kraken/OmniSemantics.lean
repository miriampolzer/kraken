module

public import Kraken.Layout

public section

/-
Common Kraken Temporal Logic and OmniSemantics.
-/

abbrev Post {State : Type} := State → Prop

-- NOTE: 'initial' cannot be moved to the left of the colon as a parameter
-- because it varies in the recursive call in the 'step' constructor (it becomes 'mid').
inductive Eventually {State : Type} (trans : State → Post → Prop) (post : Post) : Post
  | done (initial: State):
      post initial →
      Eventually trans post initial
  | step (initial: State):
      (mid_p: Post) →
      trans initial mid_p →
      (forall (mid: State), mid_p mid → Eventually trans post mid) →
      Eventually trans post initial

theorem eventually_trans {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (e : Eventually trans p initial)
  (h : ∀ s, p s → Eventually trans q s) :
    Eventually trans q initial
  := by
    induction e with
    | done initial hp => exact h initial hp
    | step initial mid_p ht _ ih => exact .step initial mid_p ht ih

theorem eventually_weaken {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (h : ∀ s, p s → q s) :
    Eventually trans p initial → Eventually trans q initial
  := by
    exact fun hp => eventually_trans trans p q initial hp fun s hs => .done s (h s hs)

-- A loop down to 0
theorem reg_dec_loop {State : Type} (trans : State → Post → Prop) (post : Post) (initial : State) (invariant : Nat → Post) (n : Nat) :
  -- if:
  -- invariant holds before entering the loop
  invariant n initial ∧
  -- final iteration allows proving `post`
  (∀ state, invariant 0 state → Eventually trans post state) ∧
  -- while iterating, we eventually re-establish the invariant
  (∀ state k, k ≠ 0 → invariant k state → Eventually trans (invariant (k - 1)) state) →
  -- then: we can prove the post
  Eventually trans post initial
  := by
    rintro ⟨hinv, hzero, hnz⟩
    if h : n = 0 then
      exact hzero initial (h ▸ hinv)
    else
      exact eventually_trans trans (invariant (n - 1)) post initial
        (hnz initial n h hinv) fun s hs =>
          reg_dec_loop trans post s invariant (n - 1) ⟨hs, hzero, hnz⟩

theorem tailrec_loop {State : Type} {α : Sort _}
    {trans : State → Post → Prop} {P Q : α → Post} {lt : α → α → Prop}
    (hwf : WellFounded lt)
    (hbody : ∀ a s, P a s →
      Eventually trans (fun s' => Q a s' ∨ ∃ a', P a' s' ∧ lt a' a ∧ ∀ t, Q a' t → Q a t) s)
    (a : α) {s : State} (hP : P a s) :
    Eventually trans (Q a) s := by
  induction a using hwf.induction generalizing s with
  | h a ih =>
    refine eventually_trans _ _ _ _ (hbody a s hP) ?_
    rintro s' (hq | ⟨a', hp', hlt, himp⟩)
    · exact .done _ hq
    · exact eventually_weaken _ _ _ _ himp (ih a' hlt hp')

private theorem Eventually.of_stall {State : Type} {trans : State → Post → Prop} {post : Post}
    {x : State} (h : Eventually trans post x) (hx : ∀ U, trans x U → U x) : post x := by
  induction h with
  | done _ hp => exact hp
  | step x U ht _ ih => exact ih x (hx U ht) hx

theorem Eventually.and_of_stall {State : Type} {trans : State → Post → Prop} {S : Post}
    (hstall : ∀ x U, S x → trans x U → U x)
    (hand : ∀ x U V, trans x U → trans x V → trans x fun y => U y ∧ V y)
    {P Q : Post} (hP : ∀ x, P x → S x) (hQ : ∀ x, Q x → S x) {x : State}
    (h₁ : Eventually trans P x) (h₂ : Eventually trans Q x) :
    Eventually trans (fun y => P y ∧ Q y) x := by
  induction h₁ with
  | done x hp => exact .done _ ⟨hp, h₂.of_stall fun U hU => hstall x U (hP x hp) hU⟩
  | step x U hU _ ih =>
    cases h₂ with
    | done _ hq => exact ih x (hstall x U (hQ x hq) hU) (.done _ hq)
    | step _ V hV h₂ => exact .step _ _ (hand x U V hU hV) fun y ⟨hu, hv⟩ => ih y hu (h₂ y hv)
