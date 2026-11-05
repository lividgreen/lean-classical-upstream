module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Algebra.Group.Basic

/-!
# Edge periods: the periods of a triangular system over the two-element field

In an edge cellular automaton (Gravner and Griffeath 2012, §2.3) the cells `0, 1, 2, …` evolve so
that the first `m` cells do not depend on the cells beyond them, and a cycle on an initial segment
is a state whose first `m` cells return after some time. Rowland (2006, §2) proves, for every
right bijective rule, that a column is periodic from the first step with a period dividing `l(k)`
times the least common multiple of the periods of the columns below it, and that a changed cell
changes its column at every step; Gravner and Griffeath state that **all periods of cycles on an
initial segment are powers of two**, a label extending to the next cell at the same period or at
the doubled one, and credit the proof to their paper on the Exactly 1 automaton (2010). Here is
the two-colour case: cell `j` is rewritten as itself plus `g j` of the state, where `g j` reads
the cells below `j` only, so that each configuration of the cells below a cell is, in their terms,
an E-inducer or a D-inducer according as `g j` is `0` or `1`. The statement is taken in the
generality the proofs have, any function of the cells below and not one rule of a fixed range. It
is, to our knowledge, first in Lean.

Write `triangularStep g` for the system and `prefixPeriod` for the least positive time at which the
cells below `m` all return to their states at time `0`. The system is injective on the cells below
`m`, so every state lies on a cycle of the first `m` cells. The argument is a pigeonhole on the
prefixes for the return, a division algorithm for the least period, and one computation on cell
`m`: over one period of the cells below it, cell `m` changes by one fixed amount `σ`, since `g m`
reads only the cells below `m`. In characteristic two, `σ = 0` keeps the period and `σ = 1`
doubles it.

## Main results

* `ReadsBelow` / `triangularStep` — a family `g` with `g j` depending on the cells below `j` only,
  and the system rewriting cell `j` as itself plus `g j` of the state.
* `iterate_eq_of_eq_below` — the cells below `m` of every iterate depend on the cells below `m`
  of the start only.
* `exists_prefix_return` / `prefixPeriod` / `prefixPeriod_pos` — the cells below `m` of every
  state return, at a least positive time.
* `iterate_eq_of_add_prefixPeriod` / `prefixPeriod_dvd_of_return` — the cells below `m` repeat
  with the period, and every time at which they return is a multiple of it.
* `prefixPeriod_zero` / `prefixPeriod_succ_eq_or_eq_two_mul` / `prefixPeriod_eq_two_pow` —
  **the dichotomy**: the period at width `m + 1` is the period at width `m` or twice it, so every
  period is a power of two.
* `apply_add_prefixPeriod_of_eq_two_mul` / `apply_add_prefixPeriod_of_eq` — **the complement**: at
  a doubling, the cell `m` after one period of the cells below it is the complement of the cell at
  the start, and when the period is kept it is the cell itself.
* `prefixPeriod_succ_eq_or_eq_two_mul_nonvacuous` — both cases of the dichotomy at one system.

## References

* Rowland, *Local nested structure in rule 30*, Complex Systems 16 (2006), §2 and §4.
* Gravner and Griffeath, *Robust periodic solutions and evolution from seeds in one-dimensional
  edge cellular automata*, Theoretical Computer Science (2012), §2.3.
-/

@[expose] public section

namespace EdgePeriods

/-- **Reads below**: `g j` depends on the cells below `j` only. -/
def ReadsBelow (g : ℕ → (ℕ → ZMod 2) → ZMod 2) : Prop :=
  ∀ (j : ℕ) (u v : ℕ → ZMod 2), (∀ i, i < j → u i = v i) → g j u = g j v

/-- **The triangular step**: cell `j` goes to itself plus `g j` of the state. -/
def triangularStep (g : ℕ → (ℕ → ZMod 2) → ZMod 2) (x : ℕ → ZMod 2) : ℕ → ZMod 2 :=
  fun j => x j + g j x

/-- **The cells below `m` of every iterate** depend on the cells below `m` of the start only. -/
theorem iterate_eq_of_eq_below {g : ℕ → (ℕ → ZMod 2) → ZMod 2} (hg : ReadsBelow g)
    {u v : ℕ → ZMod 2} {m : ℕ} (h : ∀ i, i < m → u i = v i) (t : ℕ) :
    ∀ i, i < m → (triangularStep g)^[t] u i = (triangularStep g)^[t] v i := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
      intro i hi
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [triangularStep]
      rw [ih i hi, hg i _ _ (fun k hk => ih k (lt_trans hk hi))]

/-- The system is injective on the cells below `m`: two states whose images agree below `m` agree
below `m`. -/
private theorem eq_below_of_step_eq_below {g : ℕ → (ℕ → ZMod 2) → ZMod 2} (hg : ReadsBelow g)
    {y y' : ℕ → ZMod 2} {m : ℕ}
    (h : ∀ i, i < m → triangularStep g y i = triangularStep g y' i) :
    ∀ i, i < m → y i = y' i := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      intro hj
      have hread : g j y = g j y' := hg j y y' (fun k hk => ih k hk (lt_trans hk hj))
      have hj' := h j hj
      simp only [triangularStep] at hj'
      rw [hread] at hj'
      exact add_right_cancel hj'

/-- The system is injective on the cells below `m` at every time. -/
private theorem eq_below_of_iterate_eq_below {g : ℕ → (ℕ → ZMod 2) → ZMod 2} (hg : ReadsBelow g)
    {m : ℕ} (t : ℕ) :
    ∀ {y y' : ℕ → ZMod 2},
      (∀ i, i < m → (triangularStep g)^[t] y i = (triangularStep g)^[t] y' i) →
        ∀ i, i < m → y i = y' i := by
  induction t with
  | zero => intro y y' h; simpa using h
  | succ t ih =>
      intro y y' h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
      exact eq_below_of_step_eq_below hg (ih h)

/-- **The cells below `m` of every state return**: at some positive time. -/
theorem exists_prefix_return {g : ℕ → (ℕ → ZMod 2) → ZMod 2} (hg : ReadsBelow g)
    (x : ℕ → ZMod 2) (m : ℕ) :
    ∃ Q, 0 < Q ∧ ∀ i, i < m → (triangularStep g)^[Q] x i = x i := by
  obtain ⟨a, b, hlt, heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun t : ℕ => fun i : Fin m => (triangularStep g)^[t] x i)
    (fun _ => Set.mem_univ _) Set.finite_univ
  refine ⟨b - a, by omega, ?_⟩
  have hba : b = a + (b - a) := by omega
  refine eq_below_of_iterate_eq_below hg a ?_
  intro i hi
  have := congrFun heq ⟨i, hi⟩
  simp only at this
  rw [← Function.iterate_add_apply, ← hba]
  exact this.symm

open scoped Classical in
/-- **The prefix period**: the least positive time at which the cells below `m` all return. -/
noncomputable def prefixPeriod {g : ℕ → (ℕ → ZMod 2) → ZMod 2} (hg : ReadsBelow g)
    (x : ℕ → ZMod 2) (m : ℕ) : ℕ :=
  Nat.find (exists_prefix_return hg x m)

/-- The cells below `m` return at the prefix period. -/
private theorem prefixPeriod_spec {g : ℕ → (ℕ → ZMod 2) → ZMod 2} (hg : ReadsBelow g)
    (x : ℕ → ZMod 2) (m : ℕ) :
    0 < prefixPeriod hg x m ∧
      ∀ i, i < m → (triangularStep g)^[prefixPeriod hg x m] x i = x i :=
  Nat.find_spec (exists_prefix_return hg x m)

/-- No smaller positive time is a return of the cells below `m`. -/
private theorem prefixPeriod_min {g : ℕ → (ℕ → ZMod 2) → ZMod 2} (hg : ReadsBelow g)
    (x : ℕ → ZMod 2) (m : ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hret : ∀ i, i < m → (triangularStep g)^[Q] x i = x i) : prefixPeriod hg x m ≤ Q :=
  Nat.find_min' (exists_prefix_return hg x m) ⟨hQ, hret⟩

/-- **The prefix period is positive.** -/
theorem prefixPeriod_pos {g : ℕ → (ℕ → ZMod 2) → ZMod 2} (hg : ReadsBelow g)
    (x : ℕ → ZMod 2) (m : ℕ) : 0 < prefixPeriod hg x m :=
  (prefixPeriod_spec hg x m).1

/-- **The cells below `m` repeat with the prefix period**: after any time `t`, a further prefix
period leaves the cells below `m` as they were. -/
theorem iterate_eq_of_add_prefixPeriod {g : ℕ → (ℕ → ZMod 2) → ZMod 2} (hg : ReadsBelow g)
    (x : ℕ → ZMod 2) (m t : ℕ) :
    ∀ i, i < m → (triangularStep g)^[t + prefixPeriod hg x m] x i =
      (triangularStep g)^[t] x i := by
  intro i hi
  rw [Function.iterate_add_apply]
  exact iterate_eq_of_eq_below hg (fun k hk => (prefixPeriod_spec hg x m).2 k hk) t i hi

/-- `k` prefix periods, then any further time. -/
private theorem iterate_eq_of_add_mul_prefixPeriod {g : ℕ → (ℕ → ZMod 2) → ZMod 2}
    (hg : ReadsBelow g) (x : ℕ → ZMod 2) (m t k : ℕ) :
    ∀ i, i < m → (triangularStep g)^[t + k * prefixPeriod hg x m] x i =
      (triangularStep g)^[t] x i := by
  induction k with
  | zero => intro i _; simp
  | succ k ih =>
      intro i hi
      rw [show t + (k + 1) * prefixPeriod hg x m =
        (t + k * prefixPeriod hg x m) + prefixPeriod hg x m by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]]
      rw [iterate_eq_of_add_prefixPeriod hg x m _ i hi]
      exact ih i hi

/-- **Every return time of the cells below `m` is a multiple of the prefix period.** -/
theorem prefixPeriod_dvd_of_return {g : ℕ → (ℕ → ZMod 2) → ZMod 2} (hg : ReadsBelow g)
    (x : ℕ → ZMod 2) (m : ℕ) {Q : ℕ}
    (hret : ∀ i, i < m → (triangularStep g)^[Q] x i = x i) : prefixPeriod hg x m ∣ Q := by
  have hP := prefixPeriod_pos hg x m
  have hQ : Q = Q % prefixPeriod hg x m + (Q / prefixPeriod hg x m) * prefixPeriod hg x m := by
    rw [Nat.mul_comm]; exact (Nat.mod_add_div Q _).symm
  have hr : ∀ i, i < m → (triangularStep g)^[Q % prefixPeriod hg x m] x i = x i := by
    intro i hi
    rw [← iterate_eq_of_add_mul_prefixPeriod hg x m (Q % prefixPeriod hg x m)
      (Q / prefixPeriod hg x m) i hi, ← hQ]
    exact hret i hi
  by_contra hndvd
  have hpos : 0 < Q % prefixPeriod hg x m := by
    rcases Nat.eq_zero_or_pos (Q % prefixPeriod hg x m) with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hndvd
    · exact h
  have hle := prefixPeriod_min hg x m hpos hr
  have := Nat.mod_lt Q hP
  omega

/-- **The empty prefix returns at once**: the cells below `0` are none, so the period is `1`. -/
theorem prefixPeriod_zero {g : ℕ → (ℕ → ZMod 2) → ZMod 2} (hg : ReadsBelow g)
    (x : ℕ → ZMod 2) : prefixPeriod hg x 0 = 1 :=
  Nat.dvd_one.mp (prefixPeriod_dvd_of_return hg x 0 (Q := 1)
    (fun i hi => absurd hi (Nat.not_lt_zero i)))

private theorem triangularStep_apply (g : ℕ → (ℕ → ZMod 2) → ZMod 2) (x : ℕ → ZMod 2) (j : ℕ) :
    triangularStep g x j = x j + g j x :=
  rfl

private theorem zmod_two_eq_one_of_ne_zero : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

private theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

/-- **One period of the cells below `m` moves the cell `m` by a fixed amount**: the cell `m` gains
the same difference over every stretch of one prefix period, since `g m` reads the cells below
`m` only. -/
private theorem iterate_apply_add_prefixPeriod {g : ℕ → (ℕ → ZMod 2) → ZMod 2}
    (hg : ReadsBelow g) (x : ℕ → ZMod 2) (m t : ℕ) :
    (triangularStep g)^[t + prefixPeriod hg x m] x m =
      (triangularStep g)^[t] x m +
        ((triangularStep g)^[prefixPeriod hg x m] x m - x m) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [show t + 1 + prefixPeriod hg x m = (t + prefixPeriod hg x m) + 1 by omega,
        Function.iterate_succ_apply', Function.iterate_succ_apply', triangularStep_apply,
        triangularStep_apply, ih, hg m ((triangularStep g)^[t + prefixPeriod hg x m] x)
          ((triangularStep g)^[t] x) (fun i hi => iterate_eq_of_add_prefixPeriod hg x m t i hi)]
      exact add_right_comm _ _ _

/-- **A cell that returns with the cells below it keeps the period.** -/
private theorem prefixPeriod_succ_of_cell_eq {g : ℕ → (ℕ → ZMod 2) → ZMod 2}
    (hg : ReadsBelow g) (x : ℕ → ZMod 2) (m : ℕ)
    (h : (triangularStep g)^[prefixPeriod hg x m] x m = x m) :
    prefixPeriod hg x (m + 1) = prefixPeriod hg x m := by
  apply Nat.dvd_antisymm
  · refine prefixPeriod_dvd_of_return hg x (m + 1) ?_
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · exact (prefixPeriod_spec hg x m).2 i hlt
    · exact h
  · refine prefixPeriod_dvd_of_return hg x m ?_
    intro i hi
    exact (prefixPeriod_spec hg x (m + 1)).2 i (Nat.lt_succ_of_lt hi)

/-- **A cell that does not return with the cells below it doubles the period.** -/
private theorem prefixPeriod_succ_of_cell_ne {g : ℕ → (ℕ → ZMod 2) → ZMod 2}
    (hg : ReadsBelow g) (x : ℕ → ZMod 2) (m : ℕ)
    (h : (triangularStep g)^[prefixPeriod hg x m] x m ≠ x m) :
    prefixPeriod hg x (m + 1) = 2 * prefixPeriod hg x m := by
  have hP := prefixPeriod_pos hg x m
  have hσ : (triangularStep g)^[prefixPeriod hg x m] x m - x m = 1 :=
    zmod_two_eq_one_of_ne_zero _ (sub_ne_zero.mpr h)
  have hdvd : prefixPeriod hg x (m + 1) ∣ 2 * prefixPeriod hg x m := by
    refine prefixPeriod_dvd_of_return hg x (m + 1) ?_
    intro i hi
    rw [Nat.two_mul]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | him
    · rw [iterate_eq_of_add_prefixPeriod hg x m _ i hlt]
      exact (prefixPeriod_spec hg x m).2 i hlt
    · rw [him, iterate_apply_add_prefixPeriod hg x m, hσ]
      have := iterate_apply_add_prefixPeriod hg x m 0
      rw [Nat.zero_add, hσ] at this
      rw [this, Function.iterate_zero_apply, add_assoc, zmod_two_one_add_one, add_zero]
  have hmul : prefixPeriod hg x m ∣ prefixPeriod hg x (m + 1) := by
    refine prefixPeriod_dvd_of_return hg x m ?_
    intro i hi
    exact (prefixPeriod_spec hg x (m + 1)).2 i (Nat.lt_succ_of_lt hi)
  obtain ⟨d, hd⟩ := hmul
  have hd2 : d ∣ 2 := by
    rw [hd, Nat.mul_comm 2] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hP hdvd
  have hd0 : d ≠ 0 := by
    rintro rfl
    have := prefixPeriod_pos hg x (m + 1)
    omega
  have hd3 : d ≤ 2 := Nat.le_of_dvd Nat.zero_lt_two hd2
  rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl
  · exfalso
    apply h
    have hret := (prefixPeriod_spec hg x (m + 1)).2 m (Nat.lt_succ_self m)
    rw [hd, Nat.mul_one] at hret
    exact hret
  · rw [hd, Nat.mul_comm]

/-- **The dichotomy**: the prefix period at width `m + 1` is the period at width `m` or twice it. -/
theorem prefixPeriod_succ_eq_or_eq_two_mul {g : ℕ → (ℕ → ZMod 2) → ZMod 2}
    (hg : ReadsBelow g) (x : ℕ → ZMod 2) (m : ℕ) :
    prefixPeriod hg x (m + 1) = prefixPeriod hg x m ∨
      prefixPeriod hg x (m + 1) = 2 * prefixPeriod hg x m := by
  by_cases h : (triangularStep g)^[prefixPeriod hg x m] x m = x m
  · exact Or.inl (prefixPeriod_succ_of_cell_eq hg x m h)
  · exact Or.inr (prefixPeriod_succ_of_cell_ne hg x m h)

/-- **Every prefix period is a power of two.** -/
theorem prefixPeriod_eq_two_pow {g : ℕ → (ℕ → ZMod 2) → ZMod 2} (hg : ReadsBelow g)
    (x : ℕ → ZMod 2) (m : ℕ) : ∃ k : ℕ, prefixPeriod hg x m = 2 ^ k := by
  induction m with
  | zero => exact ⟨0, by rw [prefixPeriod_zero]; rfl⟩
  | succ m ih =>
      obtain ⟨k, hk⟩ := ih
      rcases prefixPeriod_succ_eq_or_eq_two_mul hg x m with h | h
      · exact ⟨k, by rw [h, hk]⟩
      · exact ⟨k + 1, by rw [h, hk, pow_succ']⟩

/-- **The complement**: at a doubling, the cell `m` after one prefix period of the cells below it
is the complement of the cell before, at every time. -/
theorem apply_add_prefixPeriod_of_eq_two_mul {g : ℕ → (ℕ → ZMod 2) → ZMod 2}
    (hg : ReadsBelow g) (x : ℕ → ZMod 2) (m : ℕ)
    (h : prefixPeriod hg x (m + 1) = 2 * prefixPeriod hg x m) (t : ℕ) :
    (triangularStep g)^[t + prefixPeriod hg x m] x m = (triangularStep g)^[t] x m + 1 := by
  have hP := prefixPeriod_pos hg x m
  by_cases hc : (triangularStep g)^[prefixPeriod hg x m] x m = x m
  · have := prefixPeriod_succ_of_cell_eq hg x m hc
    omega
  · rw [iterate_apply_add_prefixPeriod hg x m t,
      zmod_two_eq_one_of_ne_zero _ (sub_ne_zero.mpr hc)]

/-- **The kept period**: when the period does not grow, the cell `m` after one prefix period of
the cells below it is the cell before, at every time. -/
theorem apply_add_prefixPeriod_of_eq {g : ℕ → (ℕ → ZMod 2) → ZMod 2}
    (hg : ReadsBelow g) (x : ℕ → ZMod 2) (m : ℕ)
    (h : prefixPeriod hg x (m + 1) = prefixPeriod hg x m) (t : ℕ) :
    (triangularStep g)^[t + prefixPeriod hg x m] x m = (triangularStep g)^[t] x m := by
  have hP := prefixPeriod_pos hg x m
  by_cases hc : (triangularStep g)^[prefixPeriod hg x m] x m = x m
  · rw [iterate_apply_add_prefixPeriod hg x m t, hc, sub_self, add_zero]
  · have := prefixPeriod_succ_of_cell_ne hg x m hc
    omega

/-- **Both cases of the dichotomy at one system**: with `g j u = u 0` at `j = 1` and `0` elsewhere,
which reads below, and the state with cell `0` set and every other cell clear, cell `1` flips at
every step and cell `2` never moves, so the period doubles from width `1` to width `2` and stays at
width `3`. -/
theorem prefixPeriod_succ_eq_or_eq_two_mul_nonvacuous :
    ∃ hg : ReadsBelow (fun (j : ℕ) (u : ℕ → ZMod 2) => if j = 1 then u 0 else 0),
      prefixPeriod hg (fun j => if j = 0 then 1 else 0) 2 =
          2 * prefixPeriod hg (fun j => if j = 0 then 1 else 0) 1 ∧
        prefixPeriod hg (fun j => if j = 0 then 1 else 0) 3 =
          prefixPeriod hg (fun j => if j = 0 then 1 else 0) 2 := by
  have hg : ReadsBelow (fun (j : ℕ) (u : ℕ → ZMod 2) => if j = 1 then u 0 else 0) := by
    intro j u v h
    by_cases hj : j = 1
    · simp only [hj, ↓reduceIte]
      exact h 0 (by omega)
    · simp [hj]
  refine ⟨hg, ?_⟩
  have hiter : ∀ t : ℕ,
      (triangularStep (fun (j : ℕ) (u : ℕ → ZMod 2) => if j = 1 then u 0 else 0))^[t]
          (fun j => if j = 0 then 1 else 0) =
        fun j => if j = 0 then 1 else if j = 1 then (t : ZMod 2) else 0 := by
    intro t
    induction t with
    | zero =>
        funext j
        by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> simp [h0, h1]
    | succ t ih =>
        rw [Function.iterate_succ_apply', ih]
        funext j
        rw [triangularStep_apply]
        by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> simp [h0, h1]
  have hone : (1 : ZMod 2) ≠ 0 := by decide
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hret : ∀ i, i < 2 →
      (triangularStep (fun (j : ℕ) (u : ℕ → ZMod 2) => if j = 1 then u 0 else 0))^[2]
        (fun j => if j = 0 then 1 else 0) i = (fun j => if j = 0 then (1 : ZMod 2) else 0) i := by
    intro i hi
    rw [hiter 2]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simp
    · simp [htwo]
  have hno1 : ¬ ∀ i, i < 2 →
      (triangularStep (fun (j : ℕ) (u : ℕ → ZMod 2) => if j = 1 then u 0 else 0))^[1]
        (fun j => if j = 0 then 1 else 0) i = (fun j => if j = 0 then (1 : ZMod 2) else 0) i := by
    intro h
    have := h 1 (by omega)
    rw [hiter 1] at this
    simp only [one_ne_zero, ↓reduceIte, Nat.cast_one] at this
    exact hone this
  have hP1 : prefixPeriod hg (fun j => if j = 0 then 1 else 0) 1 = 1 := by
    have hpos := prefixPeriod_pos hg (fun j => if j = 0 then 1 else 0) 1
    have hle := prefixPeriod_min hg (fun j => if j = 0 then 1 else 0) 1 (Q := 1) Nat.one_pos
      (fun i hi => by
        rw [hiter 1]
        obtain rfl : i = 0 := by omega
        simp)
    omega
  have hP2 : prefixPeriod hg (fun j => if j = 0 then 1 else 0) 2 = 2 := by
    have hpos := prefixPeriod_pos hg (fun j => if j = 0 then 1 else 0) 2
    have hle := prefixPeriod_min hg (fun j => if j = 0 then 1 else 0) 2 (Q := 2)
      Nat.two_pos hret
    have hne : prefixPeriod hg (fun j => if j = 0 then 1 else 0) 2 ≠ 1 := by
      intro h
      apply hno1
      have := (prefixPeriod_spec hg (fun j => if j = 0 then 1 else 0) 2).2
      rw [h] at this
      exact this
    omega
  have hP3 : prefixPeriod hg (fun j => if j = 0 then 1 else 0) 3 = 2 := by
    have hpos := prefixPeriod_pos hg (fun j => if j = 0 then 1 else 0) 3
    have hle := prefixPeriod_min hg (fun j => if j = 0 then 1 else 0) 3 (Q := 2)
      Nat.two_pos (fun i hi => by
        rw [hiter 2]
        obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        · simp
        · simp [htwo]
        · simp)
    have hne : prefixPeriod hg (fun j => if j = 0 then 1 else 0) 3 ≠ 1 := by
      intro h
      apply hno1
      have := (prefixPeriod_spec hg (fun j => if j = 0 then 1 else 0) 3).2
      rw [h] at this
      intro i hi
      exact this i (by omega)
    omega
  rw [hP1, hP2, hP3]
  exact ⟨rfl, rfl⟩

end EdgePeriods
