module

public import ErgodicTheory.Rule18Annihilation
import all ErgodicTheory.Rule18Kinks
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Jen's kink annihilation for rule `18`, from four statements about a lift to rule `90`

A *kink* of a configuration over `ZMod 2` is a word `1 0^(2n) 1` (`Rule18Kinks.kinkSet`). Sabrié and
Törmä (2023, §4) state, crediting Jen (1990), that a configuration with finitely many `1`s has,
after some number of steps of Wolfram's rule `18`, at most one kink (`Rule18Kinks.JenAnnihilation`).
No published proof of that statement is known, and the proof here is not theirs.

The *lift* of a configuration inserts one clear cell into the gap of each kink, so that the lifted
configuration has only gaps of even length; Jen (1990) calls this map `G`. This module defines the
lift, the leftmost and the rightmost kink of a configuration, and states and proves four statements
about them:

* `LiftConjugacy` — while one step of rule `18` keeps the kink count, the lift turns it into a
  step of rule `90`;
* `LeftmostKinkStep` and `RightmostKinkStep` — how the outermost kinks move in one step;
* `LiftKinkCells` — where the lift puts the outermost kinks and the whole configuration.

## Main results

* `kinksBelow`, `lift`, `IsLeftmostKink`, `IsRightmostKink` — the objects.
* `liftKinkCells` — **where the lift puts the outermost kinks and the support**: the lifted cells
  of the leftmost and of the rightmost kink, with nothing of the lift between each pair, and the
  support of the lift of a configuration supported in `[l, r]`, in `[l, r + c]` for `c` its kink
  count.
* `liftConjugacy` — **the lift turns a count-keeping step of rule `18` into a step of rule `90`**:
  each set cell of the image has a parent, the one neighbouring set cell of the configuration,
  parents do not decrease, and the kinks of the image below a set cell are as many as the kinks of
  the configuration below its parent.
* `jenAnnihilation` — **Jen's kink annihilation for rule `18`**: a finitely supported configuration
  has, after some number of steps, at most one kink; it is `jenAnnihilation_of_lift` at the four
  statements proved here.
* `jenAnnihilation_of_lift` — **Jen's kink annihilation follows from the four statements**. Suppose
  the kink count stays `c ≥ 2` for `2 ^ K` steps, where `2 ^ K ≥ D (D + 1)` and `D` is the width of
  the configuration plus `c`, the width of its lift. The lift of the iterate is the iterate of the
  lift, by `LiftConjugacy`, which rule `90` carries to two disjoint intervals, by the doubling
  identity (`LocalRuleColumns.iterate_two_pow_step90`). Measured from the support's left end, the
  right end of the leftmost kink never falls back and gains at least two at each collision, which
  comes at least every `D` steps while it stays below `2 D`; the same holds for the rightmost kink
  from the support's right end. The two kinks' cells in the lift then cannot lie in the two
  intervals in their order.
-/

@[expose] public section

namespace Rule18Kinks

open LocalRuleColumns

open private exists_kink_between from ErgodicTheory.Rule18Kinks

/-- The kinks of `x` whose left end lies below `i`. -/
noncomputable def kinksBelow (x : ℤ → ZMod 2) (i : ℤ) : ℕ := (kinkSet x ∩ Set.Iio i).ncard

open scoped Classical in
/-- The lift of `x`: each set cell `i` moved to `i + kinksBelow x i`, one clear cell inserted into
each kink's gap (the map Jen (1990) calls `G`). -/
noncomputable def lift (x : ℤ → ZMod 2) : ℤ → ZMod 2 :=
  fun j => if ∃ i, x i ≠ 0 ∧ i + kinksBelow x i = j then 1 else 0

/-- `(p, q)` is the leftmost kink of `x`: `p` the least kink and `q` the next set cell. -/
def IsLeftmostKink (x : ℤ → ZMod 2) (p q : ℤ) : Prop :=
  p ∈ kinkSet x ∧ (∀ k ∈ kinkSet x, p ≤ k) ∧ p < q ∧ x q ≠ 0 ∧ ∀ m, p < m → m < q → x m = 0

/-- `(p, q)` is the rightmost kink of `x`: `p` the greatest kink and `q` the next set cell. -/
def IsRightmostKink (x : ℤ → ZMod 2) (p q : ℤ) : Prop :=
  p ∈ kinkSet x ∧ (∀ k ∈ kinkSet x, k ≤ p) ∧ p < q ∧ x q ≠ 0 ∧ ∀ m, p < m → m < q → x m = 0

/-- While one step of rule `18` keeps the kink count, the lift turns it into a step of rule `90`. -/
def LiftConjugacy : Prop :=
  ∀ x : ℤ → ZMod 2, (Function.support x).Finite → kinks (step rule18 x) = kinks x →
    lift (step rule18 x) = step rule90 (lift x)

/-- One step of the leftmost kink: a gap of three or more closes by two about its middle, and a
collision sends the kink's right end past its old one. -/
def LeftmostKinkStep : Prop :=
  ∀ x : ℤ → ZMod 2, (Function.support x).Finite → ∀ p q p' q' : ℤ,
    IsLeftmostKink x p q → IsLeftmostKink (step rule18 x) p' q' →
      (3 ≤ q - p → p' = p + 1 ∧ q' = q - 1) ∧ (q = p + 1 → q + 1 ≤ q')

/-- The mirror for the rightmost kink. -/
def RightmostKinkStep : Prop :=
  ∀ x : ℤ → ZMod 2, (Function.support x).Finite → ∀ p q p' q' : ℤ,
    IsRightmostKink x p q → IsRightmostKink (step rule18 x) p' q' →
      (3 ≤ q - p → p' = p + 1 ∧ q' = q - 1) ∧ (q = p + 1 → p' + 1 ≤ p)

/-- Where the lift puts the outermost kinks and the whole configuration. -/
def LiftKinkCells : Prop :=
  ∀ x : ℤ → ZMod 2, (Function.support x).Finite →
    (∀ p q, IsLeftmostKink x p q →
      lift x p ≠ 0 ∧ lift x (q + 1) ≠ 0 ∧ ∀ m, p < m → m < q + 1 → lift x m = 0) ∧
    (∀ p q, IsRightmostKink x p q →
      lift x (p + kinks x - 1) ≠ 0 ∧ lift x (q + kinks x) ≠ 0 ∧
        ∀ m, p + kinks x - 1 < m → m < q + kinks x → lift x m = 0) ∧
    (∀ l r : ℤ, (∀ i, x i ≠ 0 → l ≤ i ∧ i ≤ r) →
      ∀ j, lift x j ≠ 0 → l ≤ j ∧ j ≤ r + kinks x)

/-! ## The growth of a right end that collides at least every `D` steps -/

private theorem growth_mono (A g : ℕ → ℤ) (hpos : ∀ t, 0 < g t) (hodd : ∀ t, Odd (g t))
    (hstep : ∀ t, (3 ≤ g t → A (t + 1) = A t ∧ g (t + 1) = g t - 2) ∧
      (g t = 1 → A t + 2 ≤ A (t + 1))) : Monotone A := by
  refine monotone_nat_of_le_succ fun t => ?_
  have h1 := hpos t
  have h2 := Int.odd_iff.mp (hodd t)
  obtain ⟨h3, h4⟩ := hstep t
  by_cases h : 3 ≤ g t
  · exact (h3 h).1.ge
  · have : g t = 1 := by omega
    have := h4 this
    omega

private theorem growth_window (A g : ℕ → ℤ) (hpos : ∀ t, 0 < g t) (hodd : ∀ t, Odd (g t))
    (hstep : ∀ t, (3 ≤ g t → A (t + 1) = A t ∧ g (t + 1) = g t - 2) ∧
      (g t = 1 → A t + 2 ≤ A (t + 1))) (D : ℕ) (t₀ : ℕ) (hg : g t₀ < 2 * (D : ℤ)) :
    A t₀ + 2 ≤ A (t₀ + D) := by
  have hmono := growth_mono A g hpos hodd hstep
  have key : ∀ m : ℕ, A t₀ + 2 ≤ A (t₀ + m) ∨ g (t₀ + m) + 2 * (m : ℤ) = g t₀ := by
    intro m
    induction m with
    | zero => exact Or.inr (by simp)
    | succ m ih =>
      rcases ih with h | h
      · exact Or.inl (h.trans (hmono (by omega)))
      · obtain ⟨h3, h4⟩ := hstep (t₀ + m)
        have h1 := hpos (t₀ + m)
        have h2 := Int.odd_iff.mp (hodd (t₀ + m))
        by_cases h5 : 3 ≤ g (t₀ + m)
        · right
          have := (h3 h5).2
          rw [← add_assoc, this]
          push_cast
          omega
        · left
          have h6 : g (t₀ + m) = 1 := by omega
          have h7 := h4 h6
          have h8 := hmono (show t₀ ≤ t₀ + m by omega)
          rw [← add_assoc]
          omega
  rcases key D with h | h
  · exact h
  · have := hpos (t₀ + D)
    omega

private theorem growth (A g : ℕ → ℤ) (hA0 : 0 ≤ A 0) (hpos : ∀ t, 0 < g t)
    (hodd : ∀ t, Odd (g t)) (hle : ∀ t, g t ≤ A t)
    (hstep : ∀ t, (3 ≤ g t → A (t + 1) = A t ∧ g (t + 1) = g t - 2) ∧
      (g t = 1 → A t + 2 ≤ A (t + 1))) (D T : ℕ) (hT : D * (D + 1) ≤ T) :
    2 * (D : ℤ) ≤ A T := by
  by_contra hlt
  push Not at hlt
  have hmono := growth_mono A g hpos hodd hstep
  have hall : ∀ k : ℕ, k * D ≤ T → 2 * (k : ℤ) ≤ A (k * D) := by
    intro k
    induction k with
    | zero => intro _; simpa using hA0
    | succ k ih =>
      intro hk
      have hk' : k * D ≤ T := by nlinarith [Nat.zero_le D]
      have h1 := ih hk'
      have h2 : g (k * D) < 2 * (D : ℤ) :=
        (hle _).trans_lt ((hmono hk').trans_lt hlt)
      have h3 := growth_window A g hpos hodd hstep D (k * D) h2
      rw [show (k + 1) * D = k * D + D by ring]
      push_cast
      omega
  have h := hall (D + 1) (by nlinarith)
  have h2 := hmono (show (D + 1) * D ≤ T by nlinarith)
  push_cast at h
  omega

/-! ## Outermost kinks and the support of the iterates -/

private theorem odd_of_kink {x : ℤ → ZMod 2} {p q : ℤ} (hp : p ∈ kinkSet x) (hpq : p < q)
    (hq : x q ≠ 0) (hm : ∀ m, p < m → m < q → x m = 0) : Odd (q - p) := by
  obtain ⟨_, j, hpj, hj, hodd, hjm⟩ := hp
  have : j = q := by
    rcases lt_trichotomy j q with h | h | h
    · exact absurd (hm j hpj h) hj
    · exact h
    · exact absurd (hjm q hpq h) hq
  subst this
  exact hodd

private theorem exists_leftmost {x : ℤ → ZMod 2} (hx : (Function.support x).Finite)
    (hne : (kinkSet x).Nonempty) : ∃ p q, IsLeftmostKink x p q := by
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image (kinkSet x) id (kinkSet_finite hx) hne
  obtain ⟨j, hpj, hj, _, hjm⟩ := hp.2
  exact ⟨p, j, hp, fun k hk => hmin k hk, hpj, hj, hjm⟩

private theorem exists_rightmost {x : ℤ → ZMod 2} (hx : (Function.support x).Finite)
    (hne : (kinkSet x).Nonempty) : ∃ p q, IsRightmostKink x p q := by
  obtain ⟨p, hp, hmax⟩ := Set.exists_max_image (kinkSet x) id (kinkSet_finite hx) hne
  obtain ⟨j, hpj, hj, _, hjm⟩ := hp.2
  exact ⟨p, j, hp, fun k hk => hmax k hk, hpj, hj, hjm⟩

private theorem step_support_bounds {x : ℤ → ZMod 2} {l r : ℤ}
    (h : ∀ i, x i ≠ 0 → l ≤ i ∧ i ≤ r) :
    ∀ i, step rule18 x i ≠ 0 → l - 1 ≤ i ∧ i ≤ r + 1 := by
  intro i hi
  by_contra hc
  apply hi
  have e1 : x (i - 1) = 0 := by
    by_contra h1
    have := h _ h1
    omega
  have e2 : x i = 0 := by
    by_contra h1
    have := h _ h1
    omega
  have e3 : x (i + 1) = 0 := by
    by_contra h1
    have := h _ h1
    omega
  change rule18 (x (i - 1)) (x i) (x (i + 1)) = 0
  rw [e1, e2, e3]
  decide

private theorem iterate_support_bounds {x : ℤ → ZMod 2} {l r : ℤ}
    (h : ∀ i, x i ≠ 0 → l ≤ i ∧ i ≤ r) :
    ∀ (t : ℕ) (i : ℤ), ((step rule18)^[t] x) i ≠ 0 → l - t ≤ i ∧ i ≤ r + t := by
  intro t
  induction t with
  | zero => simpa using h
  | succ t ih =>
    intro i hi
    rw [Function.iterate_succ_apply'] at hi
    have := step_support_bounds ih i hi
    push_cast
    omega

private theorem step_support_finite {x : ℤ → ZMod 2} (hx : (Function.support x).Finite) :
    (Function.support (step rule18 x)).Finite := by
  obtain ⟨l, hl⟩ := Set.Finite.bddBelow hx
  obtain ⟨r, hr⟩ := Set.Finite.bddAbove hx
  have := step_support_bounds (x := x) (l := l) (r := r)
    fun i hi => ⟨hl hi, hr hi⟩
  exact (Set.finite_Icc (l - 1) (r + 1)).subset fun i hi => this i hi

private theorem iterate_support_finite {x : ℤ → ZMod 2} (hx : (Function.support x).Finite)
    (t : ℕ) : (Function.support ((step rule18)^[t] x)).Finite := by
  induction t with
  | zero => simpa using hx
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact step_support_finite ih

/-! ## How the outermost kinks move in one step -/

private theorem zmod_two_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z
  decide

private theorem step18_apply (x : ℤ → ZMod 2) (i : ℤ) :
    step rule18 x i = (x (i - 1) + x (i + 1)) * (1 + x i) := rfl

private theorem step18_ne {x : ℤ → ZMod 2} {i : ℤ} (h : step rule18 x i ≠ 0) :
    x i = 0 ∧ (x (i - 1) ≠ 0 ∨ x (i + 1) ≠ 0) := by
  rw [step18_apply] at h
  have key : ∀ a b c : ZMod 2, (a + c) * (1 + b) ≠ 0 → b = 0 ∧ (a ≠ 0 ∨ c ≠ 0) := by decide
  exact key _ _ _ h

private theorem step18_ne_of_left {x : ℤ → ZMod 2} {i : ℤ} (h0 : x i = 0) (h1 : x (i - 1) ≠ 0)
    (h2 : x (i + 1) = 0) : step rule18 x i ≠ 0 := by
  rw [step18_apply]
  have key : ∀ a b c : ZMod 2, b = 0 → a ≠ 0 → c = 0 → (a + c) * (1 + b) ≠ 0 := by decide
  exact key _ _ _ h0 h1 h2

private theorem step18_ne_of_right {x : ℤ → ZMod 2} {i : ℤ} (h0 : x i = 0) (h1 : x (i - 1) = 0)
    (h2 : x (i + 1) ≠ 0) : step rule18 x i ≠ 0 := by
  rw [step18_apply]
  have key : ∀ a b c : ZMod 2, b = 0 → a = 0 → c ≠ 0 → (a + c) * (1 + b) ≠ 0 := by decide
  exact key _ _ _ h0 h1 h2

private theorem step18_eq_zero_of_clear {x : ℤ → ZMod 2} {i : ℤ} (h0 : x i = 0)
    (h1 : x (i - 1) = 0) (h2 : x (i + 1) = 0) : step rule18 x i = 0 := by
  rw [step18_apply, h0, h1, h2]
  decide

private theorem step18_eq_zero_of_ne {x : ℤ → ZMod 2} {i : ℤ} (h : x i ≠ 0) :
    step rule18 x i = 0 := by
  rw [step18_apply]
  have key : ∀ a b c : ZMod 2, b ≠ 0 → (a + c) * (1 + b) = 0 := by decide
  exact key _ _ _ h

/-- Every set cell at or below the least kink is at even distance from it. -/
private theorem even_of_leftmost {x : ℤ → ZMod 2} {p q : ℤ} (h : IsLeftmostKink x p q) :
    ∀ i, i ≤ p → x i ≠ 0 → Even (p - i) := by
  intro i hip hi
  by_contra hev
  have hlt : i < p := lt_of_le_of_ne hip (by rintro rfl; exact hev (by simp))
  have hodd : Odd (p - i) := Int.not_even_iff_odd.mp hev
  obtain ⟨c, hc, hc1, hc2⟩ := exists_kink_between x (p - i).toNat i p rfl hlt hi h.1.1 hodd
  have := h.2.1 c hc
  omega

/-- Every set cell at or above the right end of the greatest kink is at even distance from it. -/
private theorem even_of_rightmost {x : ℤ → ZMod 2} {p q : ℤ} (h : IsRightmostKink x p q) :
    ∀ i, q ≤ i → x i ≠ 0 → Even (i - q) := by
  intro i hqi hi
  by_contra hev
  have hlt : q < i := lt_of_le_of_ne hqi (by rintro rfl; exact hev (by simp))
  have hodd : Odd (i - q) := Int.not_even_iff_odd.mp hev
  obtain ⟨c, hc, hc1, hc2⟩ := exists_kink_between x (i - q).toNat q i rfl hlt h.2.2.2.1 hi hodd
  have := h.2.1 c hc
  have := h.2.2.1
  omega

/-- A set cell of the image at or below `p` is at odd distance from `p`, when the set cells of
the configuration at or below `p` are at even distance from it. -/
private theorem odd_of_step_left {x : ℤ → ZMod 2} {p : ℤ} (hp : x p ≠ 0)
    (hev : ∀ i, i ≤ p → x i ≠ 0 → Even (p - i)) :
    ∀ k, k ≤ p → step rule18 x k ≠ 0 → Odd (p - k) := by
  intro k hk hy
  obtain ⟨h0, h1 | h1⟩ := step18_ne hy
  · have := hev (k - 1) (by omega) h1
    rw [Int.even_iff] at this
    rw [Int.odd_iff]
    omega
  · have hk' : k + 1 ≤ p := by
      by_contra hc
      have : k = p := by omega
      subst this
      exact hp h0
    have := hev (k + 1) hk' h1
    rw [Int.even_iff] at this
    rw [Int.odd_iff]
    omega

/-- A set cell of the image at or above `q` is at odd distance from `q`, when the set cells of the
configuration at or above `q` are at even distance from it. -/
private theorem odd_of_step_right {x : ℤ → ZMod 2} {q : ℤ} (hq : x q ≠ 0)
    (hev : ∀ i, q ≤ i → x i ≠ 0 → Even (i - q)) :
    ∀ k, q ≤ k → step rule18 x k ≠ 0 → Odd (k - q) := by
  intro k hk hy
  obtain ⟨h0, h1 | h1⟩ := step18_ne hy
  · have hk' : q ≤ k - 1 := by
      by_contra hc
      have : k = q := by omega
      subst this
      exact hq h0
    have := hev (k - 1) hk' h1
    rw [Int.even_iff] at this
    rw [Int.odd_iff]
    omega
  · have := hev (k + 1) (by omega) h1
    rw [Int.even_iff] at this
    rw [Int.odd_iff]
    omega

/-- A gap of three or more between consecutive set cells closes by one at each end: the cells
`p + 1` and `q - 1` are set in the image, and the cells between them are clear. -/
private theorem step_gap {x : ℤ → ZMod 2} {p q : ℤ} (hpq : p + 3 ≤ q) (hp : x p ≠ 0)
    (hq : x q ≠ 0) (hm : ∀ m, p < m → m < q → x m = 0) :
    step rule18 x (p + 1) ≠ 0 ∧ step rule18 x (q - 1) ≠ 0 ∧
      ∀ m, p + 1 < m → m < q - 1 → step rule18 x m = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · refine step18_ne_of_left (hm _ (by omega) (by omega)) ?_ (hm _ (by omega) (by omega))
    have : p + 1 - 1 = p := by omega
    rw [this]
    exact hp
  · refine step18_ne_of_right (hm _ (by omega) (by omega)) (hm _ (by omega) (by omega)) ?_
    have : q - 1 + 1 = q := by omega
    rw [this]
    exact hq
  · intro m h1 h2
    exact step18_eq_zero_of_clear (hm _ (by omega) (by omega)) (hm _ (by omega) (by omega))
      (hm _ (by omega) (by omega))

/-- The cell `p + 1` is a kink of the image of a gap of three or more. -/
private theorem step_gap_kink {x : ℤ → ZMod 2} {p q : ℤ} (hpq : p + 3 ≤ q) (hodd : Odd (q - p))
    (hp : x p ≠ 0) (hq : x q ≠ 0) (hm : ∀ m, p < m → m < q → x m = 0) :
    p + 1 ∈ kinkSet (step rule18 x) := by
  obtain ⟨a1, a2, a3⟩ := step_gap hpq hp hq hm
  rw [Int.odd_iff] at hodd
  exact ⟨a1, q - 1, by omega, a2, Int.odd_iff.mpr (by omega), a3⟩

/-- **The leftmost kink under one step of rule `18`**: if the leftmost kink `(p, q)` of a finitely
supported configuration spans a gap of three or more, the leftmost kink of the image is
`(p + 1, q - 1)`, and if `q = p + 1` the right end of the image's leftmost kink lies past `q`. -/
theorem leftmostKinkStep : LeftmostKinkStep := by
  intro x _ p q p' q' hL hL'
  have hyp := odd_of_step_left hL.1.1 (even_of_leftmost hL)
  have hodd : Odd (q - p) := odd_of_kink hL.1 hL.2.2.1 hL.2.2.2.1 hL.2.2.2.2
  have hoddy : Odd (q' - p') := odd_of_kink hL'.1 hL'.2.2.1 hL'.2.2.2.1 hL'.2.2.2.2
  have hpq' : p' < q' := hL'.2.2.1
  refine ⟨fun h3 => ?_, fun hq1 => ?_⟩
  · have hpq : p + 3 ≤ q := by omega
    obtain ⟨a1, a2, a3⟩ := step_gap hpq hL.1.1 hL.2.2.2.1 hL.2.2.2.2
    have hple : p' ≤ p + 1 :=
      hL'.2.1 _ (step_gap_kink hpq hodd hL.1.1 hL.2.2.2.1 hL.2.2.2.2)
    rw [Int.odd_iff] at hoddy
    have hp'eq : p' = p + 1 := by
      by_contra hne
      have o1 := hyp p' (by omega) hL'.1.1
      rw [Int.odd_iff] at o1
      rcases lt_trichotomy q' (p + 1) with hlt | heq | hgt
      · have o2 := hyp q' (by omega) hL'.2.2.2.1
        rw [Int.odd_iff] at o2
        omega
      · omega
      · exact a1 (hL'.2.2.2.2 (p + 1) (by omega) hgt)
    subst hp'eq
    refine ⟨rfl, ?_⟩
    rcases lt_trichotomy q' (q - 1) with hlt | heq | hgt
    · exact absurd (a3 q' hL'.2.2.1 hlt) hL'.2.2.2.1
    · exact heq
    · exact absurd (hL'.2.2.2.2 (q - 1) (by omega) hgt) a2
  · have yp : step rule18 x p = 0 := step18_eq_zero_of_ne hL.1.1
    have yq : step rule18 x q = 0 := step18_eq_zero_of_ne hL.2.2.2.1
    by_contra hlt
    push Not at hlt
    have e1 : p' ≠ p := fun h => hL'.1.1 (by rw [h]; exact yp)
    have e2 : q' ≠ p := fun h => hL'.2.2.2.1 (by rw [h]; exact yp)
    have e3 : q' ≠ q := fun h => hL'.2.2.2.1 (by rw [h]; exact yq)
    have o1 := hyp p' (by omega) hL'.1.1
    have o2 := hyp q' (by omega) hL'.2.2.2.1
    rw [Int.odd_iff] at o1 o2 hoddy
    omega

/-- **The rightmost kink under one step of rule `18`**: if the rightmost kink `(p, q)` of a finitely
supported configuration spans a gap of three or more, the rightmost kink of the image is
`(p + 1, q - 1)`, and if `q = p + 1` the left end of the image's rightmost kink lies below `p`. -/
theorem rightmostKinkStep : RightmostKinkStep := by
  intro x _ p q p' q' hR hR'
  have hyp := odd_of_step_right hR.2.2.2.1 (even_of_rightmost hR)
  have hodd : Odd (q - p) := odd_of_kink hR.1 hR.2.2.1 hR.2.2.2.1 hR.2.2.2.2
  have hoddy : Odd (q' - p') := odd_of_kink hR'.1 hR'.2.2.1 hR'.2.2.2.1 hR'.2.2.2.2
  have hpq' : p' < q' := hR'.2.2.1
  refine ⟨fun h3 => ?_, fun hq1 => ?_⟩
  · have hpq : p + 3 ≤ q := by omega
    obtain ⟨a1, a2, a3⟩ := step_gap hpq hR.1.1 hR.2.2.2.1 hR.2.2.2.2
    have hple : p + 1 ≤ p' :=
      hR'.2.1 _ (step_gap_kink hpq hodd hR.1.1 hR.2.2.2.1 hR.2.2.2.2)
    rw [Int.odd_iff] at hoddy
    have hp'eq : p' = p + 1 := by
      by_contra hne
      have hp2 : p + 2 ≤ p' := by omega
      have hge : q - 1 ≤ p' := by
        by_contra hc
        exact hR'.1.1 (a3 p' (by omega) (by omega))
      have o2 := hyp q' (by omega) hR'.2.2.2.1
      rw [Int.odd_iff] at o2
      by_cases hqp : q ≤ p'
      · have o1 := hyp p' hqp hR'.1.1
        rw [Int.odd_iff] at o1
        omega
      · omega
    subst hp'eq
    refine ⟨rfl, ?_⟩
    rcases lt_trichotomy q' (q - 1) with hlt | heq | hgt
    · exact absurd (a3 q' hR'.2.2.1 hlt) hR'.2.2.2.1
    · exact heq
    · exact absurd (hR'.2.2.2.2 (q - 1) (by omega) hgt) a2
  · have yp : step rule18 x p = 0 := step18_eq_zero_of_ne hR.1.1
    have yq : step rule18 x q = 0 := step18_eq_zero_of_ne hR.2.2.2.1
    by_contra hlt
    push Not at hlt
    have e1 : p' ≠ p := fun h => hR'.1.1 (by rw [h]; exact yp)
    have e2 : p' ≠ q := fun h => hR'.1.1 (by rw [h]; exact yq)
    have o1 := hyp p' (by omega) hR'.1.1
    have o2 := hyp q' (by omega) hR'.2.2.2.1
    rw [Int.odd_iff] at o1 o2 hoddy
    omega

/-! ## Where the lift puts the outermost kinks -/

private theorem lift_ne_iff {x : ℤ → ZMod 2} {j : ℤ} :
    lift x j ≠ 0 ↔ ∃ i, x i ≠ 0 ∧ i + (kinksBelow x i : ℤ) = j := by
  unfold lift
  split_ifs with h
  · exact iff_of_true (by decide) h
  · exact iff_of_false (fun h' => h' rfl) h

private theorem kinksBelow_mono {x : ℤ → ZMod 2} (hx : (Function.support x).Finite) {i j : ℤ}
    (h : i ≤ j) : kinksBelow x i ≤ kinksBelow x j :=
  Set.ncard_le_ncard (Set.inter_subset_inter_right _ (Set.Iio_subset_Iio h))
    ((kinkSet_finite hx).subset Set.inter_subset_left)

private theorem kinksBelow_le {x : ℤ → ZMod 2} (hx : (Function.support x).Finite) (i : ℤ) :
    kinksBelow x i ≤ kinks x :=
  Set.ncard_le_ncard Set.inter_subset_left (kinkSet_finite hx)

/-- Between the lifted cells of two consecutive set cells the lift is clear. -/
private theorem lift_eq_zero_between {x : ℤ → ZMod 2} (hx : (Function.support x).Finite) {p q : ℤ}
    (hm : ∀ m, p < m → m < q → x m = 0) {m : ℤ}
    (h1 : p + (kinksBelow x p : ℤ) < m) (h2 : m < q + (kinksBelow x q : ℤ)) : lift x m = 0 := by
  by_contra hne
  obtain ⟨i, hi, rfl⟩ := lift_ne_iff.mp hne
  rcases le_or_gt i p with hip | hip
  · have := kinksBelow_mono hx hip
    omega
  · have hqi : q ≤ i := by
      by_contra hc
      exact hi (hm i hip (by omega))
    have := kinksBelow_mono hx hqi
    omega

/-- **Where the lift puts the outermost kinks and the whole configuration**: for a finitely
supported configuration, the lifted cells of the leftmost kink `(p, q)` are `p` and `q + 1` with
nothing of the lift between them; those of the rightmost kink `(p, q)` are `p + c - 1` and `q + c`,
for `c` the kink count, with nothing of the lift between them; and the lift of a configuration
supported in `[l, r]` is supported in `[l, r + c]`. -/
theorem liftKinkCells : LiftKinkCells := by
  intro x hx
  refine ⟨?_, ?_, ?_⟩
  · intro p q hL
    have hkp : kinksBelow x p = 0 := by
      have : kinkSet x ∩ Set.Iio p = ∅ :=
        Set.eq_empty_of_forall_notMem fun k hk => absurd (hL.2.1 k hk.1) (not_le.mpr hk.2)
      simp [kinksBelow, this]
    have hkq : kinksBelow x q = 1 := by
      have : kinkSet x ∩ Set.Iio q = {p} := by
        ext k
        refine ⟨fun hk => ?_, fun hk => ?_⟩
        · have h1 := hL.2.1 k hk.1
          have h2 : k = p := by
            by_contra hne
            exact hk.1.1 (hL.2.2.2.2 k (lt_of_le_of_ne h1 (Ne.symm hne)) hk.2)
          exact h2
        · have hk' : k = p := hk
          subst hk'
          exact ⟨hL.1, hL.2.2.1⟩
      simp [kinksBelow, this]
    have e1 : lift x p ≠ 0 := lift_ne_iff.mpr ⟨p, hL.1.1, by simp [hkp]⟩
    have e2 : lift x (q + 1) ≠ 0 := lift_ne_iff.mpr ⟨q, hL.2.2.2.1, by simp [hkq]⟩
    refine ⟨e1, e2, fun m h1 h2 => lift_eq_zero_between hx hL.2.2.2.2 ?_ ?_⟩
    · simp [hkp]; omega
    · simp [hkq]; omega
  · intro p q hR
    have hpos : 0 < kinks x := Set.ncard_pos (kinkSet_finite hx) |>.mpr ⟨p, hR.1⟩
    have hkp : kinksBelow x p = kinks x - 1 := by
      have : kinkSet x ∩ Set.Iio p = kinkSet x \ {p} := by
        ext k
        refine ⟨fun hk => ⟨hk.1, ?_⟩, fun hk => ⟨hk.1, ?_⟩⟩
        · exact (ne_of_lt hk.2)
        · exact lt_of_le_of_ne (hR.2.1 k hk.1) hk.2
      rw [kinksBelow, this, Set.ncard_sdiff_singleton_of_mem hR.1]
      rfl
    have hkq : kinksBelow x q = kinks x := by
      have : kinkSet x ∩ Set.Iio q = kinkSet x :=
        Set.inter_eq_left.mpr fun k hk => lt_of_le_of_lt (hR.2.1 k hk) hR.2.2.1
      simp [kinksBelow, this]; rfl
    have hc : ((kinks x - 1 : ℕ) : ℤ) = (kinks x : ℤ) - 1 := by omega
    have e1 : lift x (p + kinks x - 1) ≠ 0 :=
      lift_ne_iff.mpr ⟨p, hR.1.1, by rw [hkp, hc]; ring⟩
    have e2 : lift x (q + kinks x) ≠ 0 := lift_ne_iff.mpr ⟨q, hR.2.2.2.1, by rw [hkq]⟩
    refine ⟨e1, e2, fun m h1 h2 => lift_eq_zero_between hx hR.2.2.2.2 ?_ ?_⟩
    · rw [hkp, hc]; omega
    · rw [hkq]; omega
  · intro l r hb j hj
    obtain ⟨i, hi, rfl⟩ := lift_ne_iff.mp hj
    have := hb i hi
    have := kinksBelow_le hx i
    omega

/-! ## The lift of a count-keeping step -/

/-- The parent of a cell: its left neighbour when that is set, its right neighbour otherwise. -/
private def parentCell (x : ℤ → ZMod 2) (i : ℤ) : ℤ :=
  if x (i - 1) ≠ 0 then i - 1 else i + 1

/-- A set cell of the image is clear in the configuration, and exactly one of its two neighbours
there is set, namely its parent. -/
private theorem parentCell_spec {x : ℤ → ZMod 2} {i : ℤ} (hi : step rule18 x i ≠ 0) :
    x i = 0 ∧ x (parentCell x i) ≠ 0 ∧ (parentCell x i = i - 1 ∨ parentCell x i = i + 1) ∧
      (x (i - 1) ≠ 0 → x (i + 1) = 0) ∧ (x (i + 1) ≠ 0 → x (i - 1) = 0) := by
  obtain ⟨h0, h1⟩ := step18_ne hi
  rw [step18_apply] at hi
  have key : ∀ a c : ZMod 2, (a + c) * (1 + 0) ≠ 0 → (a ≠ 0 → c = 0) ∧ (c ≠ 0 → a = 0) := by
    decide
  rw [h0] at hi
  obtain ⟨k1, k2⟩ := key _ _ hi
  unfold parentCell
  refine ⟨h0, ?_, ?_, k1, k2⟩
  · split_ifs with h
    · exact h
    · rcases h1 with h1 | h1
      · exact absurd h1 h
      · exact h1
  · split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- The parent is non-decreasing on the set cells of the image. -/
private theorem parentCell_mono {x : ℤ → ZMod 2} {u v : ℤ} (hu : step rule18 x u ≠ 0)
    (hv : step rule18 x v ≠ 0) (huv : u ≤ v) : parentCell x u ≤ parentCell x v := by
  obtain ⟨u0, un, u2, u3, u4⟩ := parentCell_spec hu
  obtain ⟨v0, vn, v2, v3, v4⟩ := parentCell_spec hv
  rcases huv.eq_or_lt with rfl | hlt
  · exact le_rfl
  by_cases hv2 : u + 2 ≤ v
  · omega
  · have hv1 : v = u + 1 := by omega
    subst hv1
    have : parentCell x u ≠ u + 1 := fun h => by rw [h] at un; exact un v0
    omega

/-- An anchor map as in the count's non-increase respects a split at a set cell `s` of the
image: the kinks of the image below `s` are at most those of the configuration below the anchor
of `s`, and likewise at and above it. -/
private theorem kinks_split_le {x y : ℤ → ZMod 2} (hx : (Function.support x).Finite)
    (a : ℤ → ℤ) (ha₁ : ∀ i, y i ≠ 0 → x (a i) ≠ 0)
    (ha₂ : ∀ i, y i ≠ 0 → a i = i - 1 ∨ a i = i + 1)
    (hmono : ∀ u v, y u ≠ 0 → y v ≠ 0 → u ≤ v → a u ≤ a v) {s : ℤ} (hs : y s ≠ 0) :
    (kinkSet y ∩ Set.Iio s).ncard ≤ (kinkSet x ∩ Set.Iio (a s)).ncard ∧
    (kinkSet y ∩ Set.Ici s).ncard ≤ (kinkSet x ∩ Set.Ici (a s)).ncard := by
  have key : ∀ i ∈ kinkSet y, ∃ c ∈ kinkSet x, ∃ j, i < j ∧ y j ≠ 0 ∧
      (∀ m, i < m → m < j → y m = 0) ∧ a i ≤ c ∧ c < a j := by
    rintro i ⟨hi, j, hij, hj, hodd, hbet⟩
    have h1 := ha₁ i hi
    have h2 := ha₁ j hj
    have hm := hmono i j hi hj hij.le
    have hodd2 : (a j - a i) % 2 = 1 := by
      rw [Int.odd_iff] at hodd
      rcases ha₂ i hi with e | e <;> rcases ha₂ j hj with e' | e' <;> omega
    have hlt : a i < a j := by omega
    obtain ⟨c, hc, hc1, hc2⟩ :=
      exists_kink_between x _ (a i) (a j) rfl hlt h1 h2 (Int.odd_iff.mpr hodd2)
    exact ⟨c, hc, j, hij, hj, hbet, hc1, hc2⟩
  choose! g hg using key
  have hinj : Set.InjOn g (kinkSet y) := by
    intro i hi k hk hik
    by_contra hne
    obtain ⟨_, j, hij, hj, hbet, hc1, hc2⟩ := hg i hi
    obtain ⟨_, j', hkj, hj', hbet', hd1, hd2⟩ := hg k hk
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hjk : j ≤ k := by
        by_contra h
        exact hk.1 (hbet k hlt (not_le.mp h))
      have := hmono j k hj hk.1 hjk
      omega
    · have hjk : j' ≤ i := by
        by_contra h
        exact hi.1 (hbet' i hgt (not_le.mp h))
      have := hmono j' i hj' hi.1 hjk
      omega
  have hfin := kinkSet_finite hx
  refine ⟨Set.ncard_le_ncard_of_injOn g (fun i hi => ⟨(hg i hi.1).1, ?_⟩)
    (hinj.mono Set.inter_subset_left) (hfin.subset Set.inter_subset_left),
    Set.ncard_le_ncard_of_injOn g (fun i hi => ⟨(hg i hi.1).1, ?_⟩)
    (hinj.mono Set.inter_subset_left) (hfin.subset Set.inter_subset_left)⟩
  · obtain ⟨_, j, hij, hj, hbet, hc1, hc2⟩ := hg i hi.1
    have hjs : j ≤ s := by
      by_contra h
      exact hs (hbet s hi.2 (not_le.mp h))
    have := hmono j s hj hs hjs
    have h3 : g i < a s := by omega
    exact h3
  · obtain ⟨_, j, hij, hj, hbet, hc1, hc2⟩ := hg i hi.1
    have := hmono s i hs hi.1.1 hi.2
    have h3 : a s ≤ g i := by omega
    exact h3

/-- When one step keeps the kink count, the kinks of the image below a set cell are as many as the
kinks of the configuration below its parent. -/
private theorem kinksBelow_parentCell {x : ℤ → ZMod 2} (hx : (Function.support x).Finite)
    (hk : kinks (step rule18 x) = kinks x) {i : ℤ} (hi : step rule18 x i ≠ 0) :
    kinksBelow (step rule18 x) i = kinksBelow x (parentCell x i) := by
  have hy : (Function.support (step rule18 x)).Finite := step_support_finite hx
  obtain ⟨h1, h2⟩ := kinks_split_le (y := step rule18 x) hx (parentCell x)
    (fun _ hj => (parentCell_spec hj).2.1)
    (fun _ hj => (parentCell_spec hj).2.2.1) (fun _ _ hu hv huv => parentCell_mono hu hv huv) hi
  have tot : ∀ z : ℤ → ZMod 2, (kinkSet z).Finite → ∀ s : ℤ,
      (kinkSet z ∩ Set.Iio s).ncard + (kinkSet z ∩ Set.Ici s).ncard = kinks z := by
    intro z hz s
    have := Set.ncard_inter_add_ncard_sdiff_eq_ncard (kinkSet z) (Set.Iio s) hz
    have e : kinkSet z \ Set.Iio s = kinkSet z ∩ Set.Ici s := by
      ext k
      simp [not_lt]
    rw [e] at this
    exact this
  have t1 := tot _ (kinkSet_finite hy) i
  have t2 := tot _ (kinkSet_finite hx) (parentCell x i)
  unfold kinksBelow
  omega

/-- Between consecutive set cells at odd distance the kink count below grows by one. -/
private theorem kinksBelow_next_odd {z : ℤ → ZMod 2} (hz : (Function.support z).Finite) {n n' : ℤ}
    (hn : z n ≠ 0) (hn' : z n' ≠ 0) (hlt : n < n') (hm : ∀ m, n < m → m < n' → z m = 0)
    (hodd : Odd (n' - n)) : kinksBelow z n' = kinksBelow z n + 1 := by
  have h : kinkSet z ∩ Set.Iio n' = insert n (kinkSet z ∩ Set.Iio n) := by
    ext k
    constructor
    · rintro ⟨hk, hk'⟩
      rcases lt_trichotomy k n with h | h | h
      · exact Or.inr ⟨hk, h⟩
      · exact Or.inl h
      · exact absurd (hm k h hk') hk.1
    · rintro (rfl | ⟨hk, hk'⟩)
      · exact ⟨⟨hn, n', hlt, hn', hodd, hm⟩, hlt⟩
      · exact ⟨hk, hk'.trans hlt⟩
  unfold kinksBelow
  rw [h, Set.ncard_insert_of_notMem (by simp)
    ((kinkSet_finite hz).subset Set.inter_subset_left)]

/-- Between consecutive set cells at even distance the kink count below stays. -/
private theorem kinksBelow_next_even {z : ℤ → ZMod 2} {n n' : ℤ}
    (hn' : z n' ≠ 0) (hlt : n < n') (hm : ∀ m, n < m → m < n' → z m = 0)
    (heven : ¬ Odd (n' - n)) : kinksBelow z n' = kinksBelow z n := by
  have h : kinkSet z ∩ Set.Iio n' = kinkSet z ∩ Set.Iio n := by
    ext k
    constructor
    · rintro ⟨hk, hk'⟩
      rcases lt_trichotomy k n with h | h | h
      · exact ⟨hk, h⟩
      · subst h
        exact absurd (odd_of_kink hk hlt hn' hm) heven
      · exact absurd (hm k h hk') hk.1
    · rintro ⟨hk, hk'⟩
      exact ⟨hk, hk'.trans hlt⟩
  unfold kinksBelow
  rw [h]

/-- **The lift turns a count-keeping step of rule `18` into a step of rule `90`**: on a finitely
supported configuration whose image under one step of rule `18` has as many kinks, the lift of the
image is the image of the lift under one step of rule `90`.

Each set cell of the image has a parent, the one neighbouring set cell of the configuration, and
parents do not decrease. Splitting the injection that shows the kink count does not grow at the
set cell, the kinks of the image below it are as many as the kinks of the configuration below
its parent, since the totals agree. So the lifted cell of a set cell of the image sits next to
the lifted cell of its parent, and comparing the lifted cells around a cell of the lift gives the
identity of rule `90` there. -/
theorem liftConjugacy : LiftConjugacy := by
  intro x hx hk
  have hpar : ∀ i, step rule18 x i ≠ 0 →
      kinksBelow (step rule18 x) i = kinksBelow x (parentCell x i) :=
    fun i hi => kinksBelow_parentCell hx hk hi
  funext j
  have hsum : ∀ a b c : ZMod 2, (c ≠ 0 ↔ ((a ≠ 0 ∧ b = 0) ∨ (a = 0 ∧ b ≠ 0))) → c = a + b := by
    decide
  change lift (step rule18 x) j = lift x (j - 1) + lift x (j + 1)
  apply hsum
  constructor
  · intro hj
    obtain ⟨i, hi, hij⟩ := lift_ne_iff.mp hj
    rw [hpar i hi] at hij
    obtain ⟨i0, pn, p2, p3, p4⟩ := parentCell_spec hi
    rcases p2 with hp | hp
    · rw [hp] at hij
      have hl : lift x (j - 1) ≠ 0 :=
        lift_ne_iff.mpr ⟨i - 1, by rw [hp] at pn; exact pn, by omega⟩
      have hxi : x (i + 1) = 0 := p3 (by rw [hp] at pn; exact pn)
      refine Or.inl ⟨hl, ?_⟩
      by_contra hr
      obtain ⟨n, hn, hcell⟩ := lift_ne_iff.mp hr
      have h1 : i ≤ n := by
        by_contra hc
        have := kinksBelow_mono hx (show n ≤ i - 1 by omega)
        omega
      have h2 : n ≠ i := fun h => hn (h ▸ i0)
      have h3 : n ≠ i + 1 := fun h => hn (h ▸ hxi)
      have := kinksBelow_mono hx (show i - 1 ≤ n by omega)
      omega
    · rw [hp] at hij
      have hr : lift x (j + 1) ≠ 0 :=
        lift_ne_iff.mpr ⟨i + 1, by rw [hp] at pn; exact pn, by omega⟩
      have hxi : x (i - 1) = 0 := p4 (by rw [hp] at pn; exact pn)
      refine Or.inr ⟨?_, hr⟩
      by_contra hl
      obtain ⟨n, hn, hcell⟩ := lift_ne_iff.mp hl
      have h1 : n ≤ i := by
        by_contra hc
        have := kinksBelow_mono hx (show i + 1 ≤ n by omega)
        omega
      have h2 : n ≠ i := fun h => hn (h ▸ i0)
      have h3 : n ≠ i - 1 := fun h => hn (h ▸ hxi)
      have := kinksBelow_mono hx (show n ≤ i + 1 by omega)
      omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2'⟩)
    · obtain ⟨n, hn, hcell⟩ := lift_ne_iff.mp h1
      have e1 : x (n + 1) = 0 := by
        by_contra h
        have hb := kinksBelow_next_odd hx hn h (by omega) (fun m a b => by omega)
          (by rw [show n + 1 - n = 1 by omega]; exact odd_one)
        exact (lift_ne_iff.mpr ⟨n + 1, h, by omega⟩ : lift x (j + 1) ≠ 0) h2
      have e2 : x (n + 2) = 0 := by
        by_contra h
        have hb := kinksBelow_next_even (z := x) (n := n) h (by omega)
          (fun m a b => by
            have : m = n + 1 := by omega
            rw [this]; exact e1)
          (by rw [show n + 2 - n = 2 by omega]; decide)
        exact (lift_ne_iff.mpr ⟨n + 2, h, by omega⟩ : lift x (j + 1) ≠ 0) h2
      have hyn : step rule18 x (n + 1) ≠ 0 :=
        step18_ne_of_left e1 (by rw [show n + 1 - 1 = n by omega]; exact hn)
          (by rw [show n + 1 + 1 = n + 2 by omega]; exact e2)
      have hp : parentCell x (n + 1) = n := by
        have hc : x (n + 1 - 1) ≠ 0 := by rw [show n + 1 - 1 = n by omega]; exact hn
        unfold parentCell
        split_ifs
        omega
      refine lift_ne_iff.mpr ⟨n + 1, hyn, ?_⟩
      rw [hpar _ hyn, hp]
      omega
    · obtain ⟨n, hn, hcell⟩ := lift_ne_iff.mp h2'
      have e1 : x (n - 1) = 0 := by
        by_contra h
        have hb := kinksBelow_next_odd hx h hn (by omega) (fun m a b => by omega)
          (by rw [show n - (n - 1) = 1 by omega]; exact odd_one)
        exact (lift_ne_iff.mpr ⟨n - 1, h, by omega⟩ : lift x (j - 1) ≠ 0) h1
      have e2 : x (n - 2) = 0 := by
        by_contra h
        have hb := kinksBelow_next_even (z := x) (n := n - 2) hn (by omega)
          (fun m a b => by
            have : m = n - 1 := by omega
            rw [this]; exact e1)
          (by rw [show n - (n - 2) = 2 by omega]; decide)
        exact (lift_ne_iff.mpr ⟨n - 2, h, by omega⟩ : lift x (j - 1) ≠ 0) h1
      have hyn : step rule18 x (n - 1) ≠ 0 :=
        step18_ne_of_right e1 (by rw [show n - 1 - 1 = n - 2 by omega]; exact e2)
          (by rw [show n - 1 + 1 = n by omega]; exact hn)
      have hp : parentCell x (n - 1) = n := by
        have hc : ¬ x (n - 1 - 1) ≠ 0 := by
          rw [show n - 1 - 1 = n - 2 by omega]; exact not_not.mpr e2
        unfold parentCell
        split_ifs
        omega
      refine lift_ne_iff.mpr ⟨n - 1, hyn, ?_⟩
      rw [hpar _ hyn, hp]
      omega

/-! ## The count must drop -/

private theorem exists_drop (hC : LiftConjugacy) (hL : LeftmostKinkStep) (hR : RightmostKinkStep)
    (hG : LiftKinkCells) (x : ℤ → ZMod 2) (hx : (Function.support x).Finite)
    (hc2 : 2 ≤ kinks x) : ∃ n, kinks ((step rule18)^[n] x) < kinks x := by
  by_contra hno
  push Not at hno
  set c := kinks x with hcdef
  -- bounds of the support of the iterates
  obtain ⟨l, hl⟩ := Set.Finite.bddBelow hx
  obtain ⟨r, hr⟩ := Set.Finite.bddAbove hx
  have hbd : ∀ i, x i ≠ 0 → l ≤ i ∧ i ≤ r := fun i hi => ⟨hl hi, hr hi⟩
  set X : ℕ → ℤ → ZMod 2 := fun t => (step rule18)^[t] x with hX
  have hXs : ∀ t, X (t + 1) = step rule18 (X t) := fun t =>
    Function.iterate_succ_apply' _ _ _
  have hb : ∀ t i, X t i ≠ 0 → l - t ≤ i ∧ i ≤ r + t := iterate_support_bounds hbd
  have hfin : ∀ t, (Function.support (X t)).Finite := iterate_support_finite hx
  have hkin : ∀ t, kinks (X t) = c := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      have h1 : kinks (X (t + 1)) ≤ kinks (X t) := by
        rw [hXs]
        exact kinks_step_rule18_le (X t) (hfin t)
      have h2 : c ≤ kinks (X (t + 1)) := hno (t + 1)
      omega
  -- the lift of the iterate is the iterate of the lift
  have hlift : ∀ t, lift (X t) = (step rule90)^[t] (lift x) := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', ← ih, hXs]
      refine hC (X t) (hfin t) ?_
      rw [← hXs, hkin, hkin]
  have hne : ∀ t, (kinkSet (X t)).Nonempty := fun t =>
    Set.nonempty_of_ncard_ne_zero (by
      change kinks (X t) ≠ 0
      rw [hkin]
      omega)
  choose p q hLk using fun t => exists_leftmost (hfin t) (hne t)
  choose P Q hRk using fun t => exists_rightmost (hfin t) (hne t)
  -- a kink is a set cell
  have hker : ∀ t k, k ∈ kinkSet (X t) → X t k ≠ 0 := fun t k hk => hk.1
  -- the quantities
  have hlr : l ≤ r := by
    obtain ⟨k, hk⟩ := hne 0
    have := hbd k (hker 0 k hk)
    omega
  set D : ℕ := (r - l).toNat + c with hD
  have hDz : (D : ℤ) = r - l + c := by omega
  set K : ℕ := D * (D + 1) with hK
  set T : ℕ := 2 ^ K with hT
  have hTD : D * (D + 1) ≤ T := Nat.lt_two_pow_self.le
  have hD2 : 2 ≤ D := by omega
  have hDT : (D : ℤ) < 2 * (T : ℤ) := by
    have : D ≤ D * (D + 1) := Nat.le_mul_of_pos_right D (by omega)
    omega
  -- the leftmost kinks
  have hLs := fun t => hL (X t) (hfin t) (p t) (q t) (p (t + 1)) (q (t + 1)) (hLk t)
    (by rw [← hXs]; exact hLk (t + 1))
  have hRs := fun t => hR (X t) (hfin t) (P t) (Q t) (P (t + 1)) (Q (t + 1)) (hRk t)
    (by rw [← hXs]; exact hRk (t + 1))
  have hAT : 2 * (D : ℤ) ≤ q T + T - l := by
    refine growth (fun t : ℕ => q t + (t : ℤ) - l) (fun t => q t - p t) ?_ ?_ ?_ ?_ ?_ D T hTD
    · have := (hb 0 (q 0) (hLk 0).2.2.2.1).1
      simp only [Nat.cast_zero] at this ⊢
      omega
    · intro t
      have := (hLk t).2.2.1
      omega
    · intro t
      exact odd_of_kink (hLk t).1 (hLk t).2.2.1 (hLk t).2.2.2.1 (hLk t).2.2.2.2
    · intro t
      have h1 := (hb t (p t) (hker t _ (hLk t).1)).1
      omega
    · intro t
      obtain ⟨h1, h2⟩ := hLs t
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨e1, e2⟩ := h1 (by omega)
        push_cast
        omega
      · have := h2 (by omega)
        push_cast
        omega
  have hBT : 2 * (D : ℤ) ≤ r + T - P T := by
    refine growth (fun t : ℕ => r + (t : ℤ) - P t) (fun t => Q t - P t) ?_ ?_ ?_ ?_ ?_ D T hTD
    · have := (hb 0 (P 0) (hker 0 _ (hRk 0).1)).2
      simp only [Nat.cast_zero] at this ⊢
      omega
    · intro t
      have := (hRk t).2.2.1
      omega
    · intro t
      exact odd_of_kink (hRk t).1 (hRk t).2.2.1 (hRk t).2.2.2.1 (hRk t).2.2.2.2
    · intro t
      have h1 := (hb t (Q t) (hRk t).2.2.2.1).2
      omega
    · intro t
      obtain ⟨h1, h2⟩ := hRs t
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨e1, e2⟩ := h1 (by omega)
        push_cast
        omega
      · have := h2 (by omega)
        push_cast
        omega
  -- the two kinks are ordered
  have hqP : q T ≤ P T := by
    have h1 : 1 < (kinkSet (X T)).ncard := by
      change 1 < kinks (X T)
      rw [hkin]
      omega
    obtain ⟨a, b, ha, hb', hab⟩ := (Set.one_lt_ncard_iff (kinkSet_finite (hfin T))).mp h1
    have h2 := (hLk T).2.1 a ha
    have h3 := (hLk T).2.1 b hb'
    have h4 := (hRk T).2.1 a ha
    have h5 := (hRk T).2.1 b hb'
    have hpP : p T < P T := by omega
    by_contra hlt
    push Not at hlt
    exact hker T _ (hRk T).1 ((hLk T).2.2.2.2 (P T) hpP hlt)
  -- the lift at stage `T`
  have hz : ∀ j, lift (X T) j ≠ 0 →
      (l + T ≤ j ∧ j ≤ l + T + D) ∨ (l - T ≤ j ∧ j ≤ l - T + D) := by
    intro j hj
    rw [hlift T, hT, iterate_two_pow_step90] at hj
    have hTz : ((2 ^ K : ℕ) : ℤ) = (2 : ℤ) ^ K := by push_cast; rfl
    have hsum : lift x (j - 2 ^ K) ≠ 0 ∨ lift x (j + 2 ^ K) ≠ 0 := by
      by_contra hh
      push Not at hh
      rw [hh.1, hh.2] at hj
      exact hj (by simp)
    rcases hsum with h | h
    · have := (hG x hx).2.2 l r hbd _ h
      left
      have hT' : (T : ℤ) = 2 ^ K := hTz
      omega
    · have := (hG x hx).2.2 l r hbd _ h
      right
      have hT' : (T : ℤ) = 2 ^ K := hTz
      omega
  have hGL := (hG (X T) (hfin T)).1 (p T) (q T) (hLk T)
  have hGR := (hG (X T) (hfin T)).2.1 (P T) (Q T) (hRk T)
  rw [hkin T] at hGR
  have hpb := (hb T (p T) (hker T _ (hLk T).1)).1
  have hQb := (hb T (Q T) (hRk T).2.2.2.1).2
  have hcz : (2 : ℤ) ≤ c := by exact_mod_cast hc2
  have z1 := hz _ hGL.1
  have z2 := hz _ hGL.2.1
  have z3 := hz _ hGR.1
  have z4 := hz _ hGR.2.1
  omega

/-- **Jen's kink annihilation for rule `18`, from four statements about the lift**: if the lift
turns a count-keeping step of rule `18` into a step of rule `90` (`LiftConjugacy`), the outermost
kinks move as stated (`LeftmostKinkStep`, `RightmostKinkStep`) and the lift puts them and the whole
configuration where stated (`LiftKinkCells`), then a finitely supported configuration has, after
some number of steps of rule `18`, at most one kink. The statement is Sabrié and Törmä's (2023, §4),
who credit Jen (1990); the proof is not theirs.

By strong induction on the kink count it suffices to show that a configuration with `c ≥ 2` kinks
reaches a count below `c`. Were the count `c` throughout the first `2 ^ K` steps, with
`2 ^ K ≥ D (D + 1)` and `D` the width of the configuration plus `c`, the lift of the iterate would
be the iterate of the lift, supported in two disjoint intervals by the doubling identity of rule
`90`. The right end of the leftmost kink then sits at least `2 D` past the support's left end, and
the left end of the rightmost kink at least `2 D` before the support's right end, so that the
lifted cells of the two kinks cannot lie in the two intervals in their order. -/
theorem jenAnnihilation_of_lift (hC : LiftConjugacy) (hL : LeftmostKinkStep)
    (hR : RightmostKinkStep) (hG : LiftKinkCells) : JenAnnihilation := by
  intro x hx
  induction hk : kinks x using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    by_cases h : kinks x ≤ 1
    · exact ⟨0, by simpa using h⟩
    · push Not at h
      obtain ⟨n, hn⟩ := exists_drop hC hL hR hG x hx (by omega)
      obtain ⟨m, hm⟩ := ih (kinks ((step rule18)^[n] x)) (by omega) ((step rule18)^[n] x)
        (iterate_support_finite hx n) rfl
      exact ⟨m + n, by rwa [Function.iterate_add_apply]⟩

/-- **Jen's kink annihilation for rule `18`**: a finitely supported configuration has, after some
number of steps of rule `18`, at most one kink. The statement is Sabrié and Törmä's (2023, §4), who
credit Jen (1990); the proof is not theirs. It is `jenAnnihilation_of_lift` at the four statements
proved in this module. -/
theorem jenAnnihilation : JenAnnihilation :=
  jenAnnihilation_of_lift liftConjugacy leftmostKinkStep rightmostKinkStep liftKinkCells

end Rule18Kinks
