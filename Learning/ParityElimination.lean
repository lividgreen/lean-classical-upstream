module

public import CslibFrontier.Foundations.Data.Code.Hadamard
public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi

/-!
# Gaussian elimination as an online learner of the parities

The parities on the cube `Fin n → Bool` are the codewords of the Hadamard code
(`Cslib.BitString.hadamardCode`): the parity of `y` labels the point `a` by the dot product
`y ⬝ᵥ a` in the Boolean ring. The elimination learner keeps `n` rows, each a point of the cube
with a bit, a row `(0, false)` being empty. It predicts at `a` the label of the first parity, in
the order of `binaryEquiv`, that satisfies every row, and `false` when none does. At a miss at
`a` with outcome `b` it writes `(a, b)` into the first empty row, when there is one, and at a hit
it stays. Its state after a history is the rows folded from the history by this rule
(`ParityElimination.state`), and it is an `OnlineLearner` of the realizable mistake-bound model
of `Cslib.MachineLearning.OnlineLearning.MistakeBound`.

## Main definitions

* `ParityElimination.learner` — the elimination learner.

## Main results

* `ParityElimination.mistakeBound_learner_le` — the elimination learner makes at most `n` mistakes
  on every sequence a parity of `n` bits realizes: a miss fills a row and halves the set of
  parities that satisfy the rows, and a set that has halved `n` times is the target alone. This is
  the mistake bound of the elimination algorithm for the parities of Blum (1998, "On-line
  algorithms in machine learning", §4).
-/

@[expose] public section

namespace ParityElimination

open Cslib.MachineLearning.OnlineLearning.MistakeBound

/-- The rows of the elimination learner: `n` equations, each a point of the cube with a bit. -/
abbrev Rows (n : ℕ) : Type := Fin n → (Fin n → Bool) × Bool

/-- The empty row: the equation `0 = 0`, which every parity satisfies. -/
def emptyRow (n : ℕ) : (Fin n → Bool) × Bool := (fun _ => false, false)

/-- **The order of the parities.** The `2 ^ n` points of the cube as the first `2 ^ n` numbers, a
point read as a number written in binary; the learner takes the first parity in this order that
satisfies the rows. -/
def binaryEquiv (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The parity `y` satisfies the rows when it gives every row its bit: `y ⬝ᵥ a = b` for the row
`(a, b)`. -/
def satisfies {n : ℕ} (s : Rows n) (y : Fin n → Bool) : Bool :=
  decide (∀ r, y ⬝ᵥ (s r).1 = (s r).2)

/-- **The prediction.** At the point `a`, the label of the first parity satisfying every row,
`false` when none does. -/
def pred {n : ℕ} (s : Rows n) (a : Fin n → Bool) : Bool :=
  match (List.finRange (2 ^ n)).find? (fun k => satisfies s ((binaryEquiv n).symm k)) with
  | some k => (binaryEquiv n).symm k ⬝ᵥ a
  | none => false

/-- **The transition.** At a miss at the point `a` with outcome `b`, the pair `(a, b)` goes into
the first empty row, nothing when none is empty; at a hit the rows stay. -/
def step {n : ℕ} (s : Rows n) (a : Fin n → Bool) (b : Bool) : Rows n :=
  if pred s a = b then s
  else
    match (List.finRange n).find? fun r => decide (s r = emptyRow n) with
    | some r => Function.update s r (a, b)
    | none => s

/-- **The rows after a history**: the rows folded from the history by `step`, from the empty
rows. -/
def state {n : ℕ} (h : List ((Fin n → Bool) × Bool)) : Rows n :=
  h.foldl (fun s p => step s p.1 p.2) fun _ => emptyRow n

/-- **The elimination learner.** After the history `h` it predicts at `a` with the rows
`state h`. -/
def learner (n : ℕ) : OnlineLearner (Fin n → Bool) :=
  fun h a => pred (state h) a

/-! ### Halving -/

/-- A map of a finite set to itself that is an involution and flips a bit splits the set in two
halves of one size, whichever the value of the bit. -/
private theorem two_mul_card_filter_eq {α : Type*} (S : Finset α) (φ : α → α)
    (f : α → Bool) (hmaps : ∀ x ∈ S, φ x ∈ S) (hinv : ∀ x ∈ S, φ (φ x) = x)
    (hf : ∀ x ∈ S, f (φ x) = !f x) (b : Bool) :
    2 * (S.filter fun x => f x = b).card = S.card := by
  have h : (S.filter fun x => f x = b).card = (S.filter fun x => ¬ f x = b).card := by
    refine Finset.card_nbij' φ φ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
      refine ⟨hmaps x hx.1, ?_⟩
      rw [hf x hx.1, hx.2]
      cases b <;> decide
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
      refine ⟨hmaps x hx.1, ?_⟩
      rw [hf x hx.1]
      revert hx
      cases b <;> cases hfx : f x <;> simp
    · intro x hx
      exact hinv x (Finset.mem_filter.mp hx).1
    · intro x hx
      exact hinv x (Finset.mem_filter.mp hx).1
  have h2 := Finset.card_filter_add_card_filter_not (s := S) (fun x => f x = b)
  omega

/-- The parities that satisfy the rows. -/
private def sol {n : ℕ} (s : Rows n) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun y => satisfies s y = true

/-- The rows that are not empty. -/
private def filled {n : ℕ} (s : Rows n) : Finset (Fin n) :=
  Finset.univ.filter fun r => s r ≠ emptyRow n

private theorem satisfies_eq_true {n : ℕ} {s : Rows n} {y : Fin n → Bool} :
    satisfies s y = true ↔ ∀ r, y ⬝ᵥ (s r).1 = (s r).2 := by
  simp [satisfies]

private theorem bool_add_add_self (x z : Bool) : x + z + z = x := by
  cases x <;> cases z <;> decide

private theorem bool_add_true (x : Bool) : x + true = !x := by
  cases x <;> decide

/-- At a point where two parities of the solution set disagree, the solutions with a given label
at the point are half of the solution set: adding the difference of the two parities is an
involution of the solution set that flips the label. -/
private theorem two_mul_card_sol_filter {n : ℕ} (s : Rows n) (a : Fin n → Bool)
    {y0 y1 : Fin n → Bool} (h0 : satisfies s y0 = true) (h1 : satisfies s y1 = true)
    (hne : y0 ⬝ᵥ a ≠ y1 ⬝ᵥ a) (b : Bool) :
    2 * ((sol s).filter fun y => y ⬝ᵥ a = b).card = (sol s).card := by
  rw [satisfies_eq_true] at h0 h1
  have hd : (y0 + y1) ⬝ᵥ a = true := by
    rw [add_dotProduct]
    revert hne
    generalize y0 ⬝ᵥ a = u
    generalize y1 ⬝ᵥ a = w
    revert u w
    decide
  refine two_mul_card_filter_eq (sol s) (fun y => y + (y0 + y1)) (fun y => y ⬝ᵥ a) ?_ ?_ ?_ b
  · intro y hy
    simp only [sol, Finset.mem_filter, Finset.mem_univ, true_and, satisfies_eq_true] at hy ⊢
    intro r
    rw [add_dotProduct, add_dotProduct, hy r, h0 r, h1 r]
    cases (s r).2 <;> rfl
  · intro y _
    funext i
    simp only [Pi.add_apply]
    exact bool_add_add_self (y i) (y0 i + y1 i)
  · intro y _
    show (y + (y0 + y1)) ⬝ᵥ a = _
    rw [add_dotProduct, hd, bool_add_true]

/-- When some parity satisfies the rows, the prediction is the label of a parity that satisfies
them. -/
private theorem exists_pred_witness {n : ℕ} (s : Rows n) (a : Fin n → Bool)
    {y : Fin n → Bool} (hy : satisfies s y = true) :
    ∃ y0, satisfies s y0 = true ∧ pred s a = y0 ⬝ᵥ a := by
  unfold pred
  cases h : (List.finRange (2 ^ n)).find? (fun k => satisfies s ((binaryEquiv n).symm k)) with
  | none =>
    exfalso
    exact absurd (by simpa using hy)
      (List.find?_eq_none.mp h (binaryEquiv n y) (List.mem_finRange _))
  | some k =>
    have hk := List.find?_some h
    exact ⟨(binaryEquiv n).symm k, hk, rfl⟩

private theorem card_filled_le {n : ℕ} (s : Rows n) : (filled s).card ≤ n :=
  (Finset.card_le_univ _).trans (by simp)

private theorem dot_false {n : ℕ} (y : Fin n → Bool) : y ⬝ᵥ (fun _ => false) = false :=
  dotProduct_zero y

/-- The rows after a miss, in the case an empty row is there to take the missed point: the
solution set loses the parities that are wrong at the point, one more row is filled, and the
target stays a solution. -/
private theorem step_miss {n : ℕ} (s : Rows n) (a y : Fin n → Bool)
    (hy : satisfies s y = true) (hK : (sol s).card * 2 ^ (filled s).card = 2 ^ n)
    (hmiss : pred s a ≠ y ⬝ᵥ a) :
    satisfies (step s a (y ⬝ᵥ a)) y = true ∧
      (sol (step s a (y ⬝ᵥ a))).card * 2 ^ (filled (step s a (y ⬝ᵥ a))).card = 2 ^ n ∧
      (filled (step s a (y ⬝ᵥ a))).card = (filled s).card + 1 := by
  obtain ⟨y0, hy0, hpred⟩ := exists_pred_witness s a hy
  have hmiss0 := hmiss
  rw [hpred] at hmiss
  have hy0y : y0 ≠ y := fun h => hmiss (by rw [h])
  -- the solution set has two members
  have hcard2 : 2 ≤ (sol s).card := by
    have : 1 < (sol s).card := Finset.one_lt_card.mpr
      ⟨y0, by simp [sol, hy0], y, by simp [sol, hy], hy0y⟩
    omega
  -- an empty row is there
  have hfilled_lt : (filled s).card < n := by
    by_contra hge
    have heq : (filled s).card = n := le_antisymm (card_filled_le s) (not_lt.mp hge)
    rw [heq] at hK
    have h1 : (sol s).card = 1 :=
      Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos n) (by rw [hK, one_mul])
    omega
  have hex : ∃ r, s r = emptyRow n := by
    by_contra hno
    push Not at hno
    have : filled s = Finset.univ := by
      ext r
      simp [filled, hno r]
    rw [this] at hfilled_lt
    simp at hfilled_lt
  obtain ⟨r1, hr1⟩ := hex
  have hfind : ∃ r0, (List.finRange n).find? (fun r => decide (s r = emptyRow n)) = some r0 ∧
      s r0 = emptyRow n := by
    cases h : (List.finRange n).find? (fun r => decide (s r = emptyRow n)) with
    | none =>
      exfalso
      have := List.find?_eq_none.mp h r1 (List.mem_finRange r1)
      simp [hr1] at this
    | some r0 =>
      exact ⟨r0, rfl, by simpa using List.find?_some h⟩
  obtain ⟨r0, hr0find, hr0⟩ := hfind
  have ha : a ≠ fun _ => false := by
    rintro rfl
    exact hmiss (by rw [dot_false, dot_false])
  have hstep : step s a (y ⬝ᵥ a) = Function.update s r0 (a, y ⬝ᵥ a) := by
    simp [step, hmiss0, hr0find]
  have hzero : ∀ y' : Fin n → Bool, y' ⬝ᵥ (s r0).1 = (s r0).2 := by
    intro y'
    rw [hr0]
    exact dot_false y'
  have hrows : ∀ y' : Fin n → Bool,
      satisfies (Function.update s r0 (a, y ⬝ᵥ a)) y' = true ↔
        satisfies s y' = true ∧ y' ⬝ᵥ a = y ⬝ᵥ a := by
    intro y'
    rw [satisfies_eq_true, satisfies_eq_true]
    constructor
    · intro h
      refine ⟨fun r => ?_, by simpa using h r0⟩
      by_cases hr : r = r0
      · subst hr
        exact hzero y'
      · simpa [Function.update_apply, hr] using h r
    · rintro ⟨h1, h2⟩ r
      by_cases hr : r = r0
      · subst hr
        simpa using h2
      · simpa [Function.update_apply, hr] using h1 r
  have hsol : sol (Function.update s r0 (a, y ⬝ᵥ a)) =
      (sol s).filter fun y' => y' ⬝ᵥ a = y ⬝ᵥ a := by
    ext y'
    simp only [sol, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hrows y'
  have hfilled : filled (Function.update s r0 (a, y ⬝ᵥ a)) = insert r0 (filled s) := by
    ext r
    by_cases hr : r = r0
    · subst hr
      have : (a, y ⬝ᵥ a) ≠ emptyRow n := by
        intro h
        exact ha (congrArg Prod.fst h)
      simp [filled, this]
    · simp [filled, Function.update_apply, hr]
  have hnot : r0 ∉ filled s := by simp [filled, hr0]
  have hhalf := two_mul_card_sol_filter s a hy0 hy hmiss (y ⬝ᵥ a)
  rw [hstep]
  refine ⟨(hrows y).mpr ⟨hy, rfl⟩, ?_, ?_⟩
  · rw [hsol, hfilled, Finset.card_insert_of_notMem hnot, pow_succ]
    calc ((sol s).filter fun y' => y' ⬝ᵥ a = y ⬝ᵥ a).card * (2 ^ (filled s).card * 2)
        = (2 * ((sol s).filter fun y' => y' ⬝ᵥ a = y ⬝ᵥ a).card) * 2 ^ (filled s).card := by
          ring
      _ = 2 ^ n := by rw [hhalf, hK]
  · rw [hfilled, Finset.card_insert_of_notMem hnot]

/-- The rows after a history extended by one example are the step of the rows after the
history. -/
private theorem state_append_singleton {n : ℕ} (h : List ((Fin n → Bool) × Bool)) (a : Fin n → Bool)
    (b : Bool) : state (h ++ [(a, b)]) = step (state h) a b := by
  simp [state, List.foldl_append]

/-- Along a history whose rows the target satisfies, with the solutions and the filled rows in
the halving relation, the mistakes still to come and the rows already filled number at most `n`:
each miss fills a row and halves the solutions. -/
private theorem mistakesFrom_add_filled_le {n : ℕ} (y : Fin n → Bool) :
    ∀ S : List ((Fin n → Bool) × Bool), (∀ p ∈ S, y ⬝ᵥ p.1 = p.2) →
      ∀ h : List ((Fin n → Bool) × Bool), satisfies (state h) y = true →
        (sol (state h)).card * 2 ^ (filled (state h)).card = 2 ^ n →
        mistakesFrom (learner n) h S + (filled (state h)).card ≤ n := by
  intro S
  induction S with
  | nil =>
    intro _ h _ _
    simpa using card_filled_le (state h)
  | cons p S ih =>
    intro hS h h1 h2
    obtain ⟨a, b⟩ := p
    have hb : y ⬝ᵥ a = b := hS (a, b) (by simp)
    subst hb
    have hS' : ∀ q ∈ S, y ⬝ᵥ q.1 = q.2 := fun q hq => hS q (List.mem_cons_of_mem _ hq)
    rw [mistakesFrom_cons]
    by_cases hhit : pred (state h) a = y ⬝ᵥ a
    · have hstay : step (state h) a (y ⬝ᵥ a) = state h := by simp [step, hhit]
      have := ih hS' (h ++ [(a, y ⬝ᵥ a)])
      rw [state_append_singleton, hstay] at this
      have hl : learner n h a = y ⬝ᵥ a := hhit
      simp only [hl, ite_true, zero_add]
      exact this h1 h2
    · obtain ⟨m1, m2, m3⟩ := step_miss (state h) a y h1 h2 hhit
      have := ih hS' (h ++ [(a, y ⬝ᵥ a)])
      rw [state_append_singleton] at this
      have hl : ¬ learner n h a = y ⬝ᵥ a := hhit
      simp only [hl, ite_false]
      have := this m1 m2
      omega

/-- **The elimination learner makes at most `n` mistakes on the parities**: on every sequence
that a parity of `n` bits realizes, in the realizable mistake-bound model, whatever its length.
Each miss fills a row and halves the set of parities that satisfy the rows, and a set that has
halved `n` times is the target alone. This is the mistake bound of Blum (1998, "On-line algorithms
in machine learning", §4) for the parities. -/
theorem mistakeBound_learner_le (n : ℕ) :
    mistakeBound (learner n) (Set.range (Cslib.BitString.hadamardCode (ι := Fin n))) ≤ n := by
  refine mistakeBound_le_iff.mpr fun S hS => ?_
  obtain ⟨c, ⟨y, rfl⟩, hc⟩ := realizable_iff.mp hS
  have h0 : state ([] : List ((Fin n → Bool) × Bool)) = fun _ => emptyRow n := rfl
  have hsol : sol (fun _ : Fin n => emptyRow n) = Finset.univ := by
    ext y'
    simp [sol, satisfies, emptyRow, dot_false]
  have hfill : filled (fun _ : Fin n => emptyRow n) = ∅ := by
    ext r
    simp [filled]
  have key := mistakesFrom_add_filled_le y S (fun p hp => hc p hp) []
    (by rw [h0]; simp [satisfies, emptyRow, dot_false])
    (by rw [h0, hsol, hfill]; simp)
  rw [h0, hfill] at key
  have : mistakes (learner n) S ≤ n := by
    unfold mistakes
    simpa using key
  exact_mod_cast this

end ParityElimination
