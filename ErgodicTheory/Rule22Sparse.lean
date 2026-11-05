module

public import ErgodicTheory.LocalRuleColumns
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Rule `22` on configurations supported in one coset of `4ℤ`

On a configuration over `ZMod 2` whose set cells all lie in one coset of `4ℤ`, every radius-one
window meets at most one set cell, so one step of Wolfram's rule `22` (one exactly when exactly one
of the three inputs is one) reads the sum of the three cells, as the additive rule does. Two steps
of rule `22` are then two steps of rule `90`, and the image is again supported in one coset of `4ℤ`:
the orbits of the two rules agree at every even time. From the single cell this is the closed form
of Chan-López and Martín-Ruiz (2026, §3), `Q_{2j}(x) = (x² + x⁻²)^j`, the row of rule `90`
(Wolfram 1983) at time `2j`, which is its row `j` with every distance doubled.

## Main results

* `rule22`, `SupportInCoset` — Wolfram's rule `22` over `ZMod 2`, and the condition that the
  support of a configuration lies in one coset of `mℤ`.
* `step_rule22_eq_of_supportInCoset` — on such a configuration one step of rule `22` reads
  `x (i - 1) + x i + x (i + 1)`.
* `iterate_step_rule22_two_eq_rule90`, `supportInCoset_iterate_step_rule90_two` — two steps of
  rule `22` are two steps of rule `90` on a configuration supported in one coset of `4ℤ`, and the
  image is supported in one coset of `4ℤ`.
* `iterate_step_rule22_two_mul_eq_rule90`, `supportInCoset_iterate_step_rule22_two_mul` — **the
  orbits agree at every even time**, and stay supported in one coset of `4ℤ`.
* `iterate_step_rule22_two_mul_single` — from the single cell, rule `22` at time `2j` is rule `90`
  at time `2j`; `iterate_step_rule90_two_mul_single_even` and
  `iterate_step_rule90_two_mul_single_odd` read that row as the row at time `j` with every
  distance doubled.
* `iterate_step_rule22_odd_single` — the row at time `2j + 1` is the row at time `2j` times
  `x⁻¹ + 1 + x`: at each cell, the sum of the three cells of the even row's window.
* `not_iterate_step_rule22_two_eq_rule90_off_coset` — the coset hypothesis is load-bearing: at the
  two cells `0` and `2` the two rules differ after two steps.
* `rule146`, `reduction` — Jen's rule `146` over `ZMod 2`, and the reduction of a configuration,
  its state read at the even cells (Gravner and Griffeath 2010, §3).
* `iterate_step_rule22_two_reduction`, `iterate_step_rule22_two_mul_reduction` — two steps of
  rule `22` on a configuration clear at the odd cells are rule `146` on its reduction, at every
  even time (Gravner and Griffeath 2010, Lemma 3.1).
* `not_iterate_step_rule22_two_reduction_off_even` — clearness at the odd cells is load-bearing: at
  the two cells `0` and `1` the reduction of the second iterate is not rule `146`'s image.
-/

@[expose] public section

namespace Rule22Sparse

open LocalRuleColumns

/-- Wolfram's rule `22` over `ZMod 2`: the new value is one exactly when exactly one of the three
cells is one. -/
abbrev rule22 : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 := fun a b c => a + b + c + a * b * c

/-- The support of `x` lies in one coset of `mℤ`: any two set cells differ by a multiple of `m`. -/
def SupportInCoset {Q : Type*} [Zero Q] (m : ℤ) (x : ℤ → Q) : Prop :=
  ∀ i j, x i ≠ 0 → x j ≠ 0 → m ∣ i - j

private theorem rule22_eq_sum_of_atMostOne (a b c : ZMod 2) (hab : a ≠ 0 → b = 0)
    (hac : a ≠ 0 → c = 0) (hbc : b ≠ 0 → c = 0) : rule22 a b c = a + b + c := by
  revert a b c; decide

set_option synthInstance.maxSize 1000 in
private theorem rule22_two_step_of_coset (u v w p q : ZMod 2) (huv : u ≠ 0 → v = 0)
    (huw : u ≠ 0 → w = 0) (hup : u ≠ 0 → p = 0) (hvw : v ≠ 0 → w = 0) (hvp : v ≠ 0 → p = 0)
    (hvq : v ≠ 0 → q = 0) (hwp : w ≠ 0 → p = 0) (hwq : w ≠ 0 → q = 0) (hpq : p ≠ 0 → q = 0) :
    rule22 (u + v + w) (v + w + p) (w + p + q) = u + q := by
  revert u v w p q; decide

/-- On a configuration supported in one coset of `4ℤ`, one step of rule `22` reads the sum of the
three cells of the window. -/
theorem step_rule22_eq_of_supportInCoset {x : ℤ → ZMod 2} (hx : SupportInCoset 4 x) (i : ℤ) :
    step rule22 x i = x (i - 1) + x i + x (i + 1) := by
  refine rule22_eq_sum_of_atMostOne _ _ _ ?_ ?_ ?_ <;> intro h1
  all_goals by_contra h2
  · have := hx _ _ h1 h2; omega
  · have := hx _ _ h1 h2; omega
  · have := hx _ _ h1 h2; omega

/-- Two steps of rule `22` are two steps of rule `90` on a configuration supported in one coset of
`4ℤ`. -/
theorem iterate_step_rule22_two_eq_rule90 {x : ℤ → ZMod 2} (hx : SupportInCoset 4 x) :
    (step rule22)^[2] x = (step rule90)^[2] x := by
  funext i
  have h90 := iterate_two_pow_step90 1 x i
  simp only [pow_one] at h90
  rw [h90]
  change step rule22 (step rule22 x) i = _
  have e : ∀ j, step rule22 x j = x (j - 1) + x j + x (j + 1) :=
    step_rule22_eq_of_supportInCoset hx
  change rule22 (step rule22 x (i - 1)) (step rule22 x i) (step rule22 x (i + 1)) = _
  rw [e (i - 1), e i, e (i + 1)]
  have h := rule22_two_step_of_coset (x (i - 2)) (x (i - 1)) (x i) (x (i + 1)) (x (i + 2))
  have key : ∀ a b : ℤ, ¬ 4 ∣ a - b → x a ≠ 0 → x b = 0 := by
    intro a b hn ha; by_contra hb; exact hn (hx a b ha hb)
  have r1 : i - 1 - 1 = i - 2 := by ring
  have r2 : i + 1 + 1 = i + 2 := by ring
  rw [show i - 1 + 1 = i by ring, show i + 1 - 1 = i by ring, r1, r2]
  have := h (key _ _ (by omega)) (key _ _ (by omega)) (key _ _ (by omega))
    (key _ _ (by omega)) (key _ _ (by omega)) (key _ _ (by omega)) (key _ _ (by omega))
    (key _ _ (by omega)) (key _ _ (by omega))
  rw [this]

/-- Two steps of rule `90` carry a configuration supported in one coset of `4ℤ` to one supported in
one coset of `4ℤ`. -/
theorem supportInCoset_iterate_step_rule90_two {x : ℤ → ZMod 2} (hx : SupportInCoset 4 x) :
    SupportInCoset 4 ((step rule90)^[2] x) := by
  have h90 : ∀ i, (step rule90)^[2] x i = x (i - 2) + x (i + 2) := by
    intro i
    have := iterate_two_pow_step90 1 x i
    simp only [pow_one] at this
    exact this
  intro i j hi hj
  rw [h90] at hi hj
  have hi' : x (i - 2) ≠ 0 ∨ x (i + 2) ≠ 0 := by
    by_contra h; rw [not_or, not_not, not_not] at h; rw [h.1, h.2] at hi; simp at hi
  have hj' : x (j - 2) ≠ 0 ∨ x (j + 2) ≠ 0 := by
    by_contra h; rw [not_or, not_not, not_not] at h; rw [h.1, h.2] at hj; simp at hj
  rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj'
  · have := hx _ _ hi' hj'; omega
  · have := hx _ _ hi' hj'; omega
  · have := hx _ _ hi' hj'; omega
  · have := hx _ _ hi' hj'; omega

/-- At every even time, rule `22` from a configuration supported in one coset of `4ℤ` is rule
`90`. -/
theorem iterate_step_rule22_two_mul_eq_rule90 {x : ℤ → ZMod 2} (hx : SupportInCoset 4 x)
    (j : ℕ) : (step rule22)^[2 * j] x = (step rule90)^[2 * j] x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, Function.iterate_add_apply,
      Function.iterate_add_apply, iterate_step_rule22_two_eq_rule90 hx]
    exact ih (supportInCoset_iterate_step_rule90_two hx)

/-- The orbit of rule `22` at every even time stays supported in one coset of `4ℤ`. -/
theorem supportInCoset_iterate_step_rule22_two_mul {x : ℤ → ZMod 2} (hx : SupportInCoset 4 x)
    (j : ℕ) : SupportInCoset 4 ((step rule22)^[2 * j] x) := by
  induction j generalizing x with
  | zero => exact hx
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, Function.iterate_add_apply,
      iterate_step_rule22_two_eq_rule90 hx]
    exact ih (supportInCoset_iterate_step_rule90_two hx)

private theorem supportInCoset_single : SupportInCoset 4 (Pi.single (0 : ℤ) (1 : ZMod 2)) := by
  intro i j hi hj
  have hi' : i = 0 := by
    by_contra h; exact hi (by simp [h])
  have hj' : j = 0 := by
    by_contra h; exact hj (by simp [h])
  subst hi' hj'; simp

/-- **The closed form** of the orbit of rule `22` from a single cell: at time `2j` it is rule `90`'s
row at time `2j`. -/
theorem iterate_step_rule22_two_mul_single (j : ℕ) :
    (step rule22)^[2 * j] (Pi.single 0 1) = (step rule90)^[2 * j] (Pi.single 0 1) :=
  iterate_step_rule22_two_mul_eq_rule90 supportInCoset_single j

/-- **The odd row** of the orbit of rule `22` from a single cell (Chan-López and Martín-Ruiz 2026,
§3): the row at time `2j + 1` is the row at time `2j` times `x⁻¹ + 1 + x`, that is, at each cell the
sum of the three cells of the even row's window. -/
theorem iterate_step_rule22_odd_single (j : ℕ) (i : ℤ) :
    (step rule22)^[2 * j + 1] (Pi.single 0 1) i =
      (step rule22)^[2 * j] (Pi.single 0 1) (i - 1) + (step rule22)^[2 * j] (Pi.single 0 1) i +
        (step rule22)^[2 * j] (Pi.single 0 1) (i + 1) := by
  rw [Function.iterate_succ_apply']
  exact step_rule22_eq_of_supportInCoset
    (supportInCoset_iterate_step_rule22_two_mul supportInCoset_single j) i

/-- The dilation of a configuration by two: the value at `2 * i` is the value of `x` at `i`, and
odd cells read zero. -/
private def dil (x : ℤ → ZMod 2) : ℤ → ZMod 2 := fun k => if 2 ∣ k then x (k / 2) else 0

private theorem dil_even (x : ℤ → ZMod 2) (m : ℤ) : dil x (2 * m) = x m := by
  simp [dil]

private theorem dil_odd (x : ℤ → ZMod 2) (m : ℤ) : dil x (2 * m + 1) = 0 := by
  have : ¬ (2 : ℤ) ∣ 2 * m + 1 := by omega
  simp [dil, this]

private theorem iterate_two_dil (x : ℤ → ZMod 2) :
    (step rule90)^[2] (dil x) = dil (step rule90 x) := by
  funext k
  have h90 := iterate_two_pow_step90 1 (dil x) k
  simp only [pow_one] at h90
  rw [h90]
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [show 2 * m - 2 = 2 * (m - 1) by ring, show 2 * m + 2 = 2 * (m + 1) by ring,
      dil_even, dil_even, dil_even]
    rfl
  · rw [show 2 * m + 1 - 2 = 2 * (m - 1) + 1 by ring, show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by ring,
      dil_odd, dil_odd, dil_odd]
    simp

private theorem iterate_two_mul_dil (j : ℕ) :
    ∀ x : ℤ → ZMod 2, (step rule90)^[2 * j] (dil x) = dil ((step rule90)^[j] x) := by
  induction j with
  | zero => intro x; rfl
  | succ j ih =>
    intro x
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, Function.iterate_add_apply, iterate_two_dil, ih,
      Function.iterate_succ_apply]

private theorem single_eq_dil : (Pi.single (0 : ℤ) (1 : ZMod 2)) = dil (Pi.single 0 1) := by
  funext k
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [dil_even]
    by_cases h : m = 0
    · subst h; simp
    · have : (2 * m : ℤ) ≠ 0 := by omega
      simp [h, this]
  · rw [dil_odd]
    have : (2 * m + 1 : ℤ) ≠ 0 := by omega
    simp [this]

/-- Rule `90`'s row at time `2j` from the single cell, read at an even cell, is its row at time `j`
with every distance doubled. -/
theorem iterate_step_rule90_two_mul_single_even (j : ℕ) (i : ℤ) :
    (step rule90)^[2 * j] (Pi.single 0 1) (2 * i) = (step rule90)^[j] (Pi.single 0 1) i := by
  rw [single_eq_dil, iterate_two_mul_dil, dil_even]
  rw [← single_eq_dil]

/-- Rule `90`'s row at time `2j` from the single cell vanishes at odd cells. -/
theorem iterate_step_rule90_two_mul_single_odd (j : ℕ) (i : ℤ) :
    (step rule90)^[2 * j] (Pi.single 0 1) (2 * i + 1) = 0 := by
  rw [single_eq_dil, iterate_two_mul_dil, dil_odd]

/-- The guard: the two cells `0` and `2` are of one parity and not in one coset of `4ℤ`, and
two steps of rule `22` clear cell `0` where two steps of rule `90` set it. -/
theorem not_iterate_step_rule22_two_eq_rule90_off_coset :
    (step rule22)^[2] (Pi.single 0 1 + Pi.single 2 1 : ℤ → ZMod 2) ≠
      (step rule90)^[2] (Pi.single 0 1 + Pi.single 2 1 : ℤ → ZMod 2) := by
  intro h
  have h0 := congrFun h 0
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
    Function.iterate_succ_apply', Function.iterate_succ_apply'] at h0
  revert h0
  decide +kernel

/-! ## Rule `22` on the configurations of one parity: the reduction to rule `146` -/

/-- Jen's rule `146` over `ZMod 2`: the new value is one exactly at the inputs `001`, `100` and
`111`. -/
abbrev rule146 : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 :=
  fun a b c => c + b * c + a + a * b + a * b * c

/-- The reduction of a configuration: its state read at the even cells, `x (2 * y)` at the cell
`y` (Gravner and Griffeath 2010, §3). -/
def reduction (x : ℤ → ZMod 2) : ℤ → ZMod 2 := fun y => x (2 * y)

/-- **Two steps of rule `22` on a configuration clear at the odd cells are rule `146` on its
reduction** (Gravner and Griffeath 2010, Lemma 3.1): the image is again clear at the odd cells.
One step writes `x (2y)` at `2y` and `x (2y) + x (2y + 2)` at `2y + 1`, and a second step reads, at
`2y` and at `2y + 1`, windows on which the two rules agree. -/
theorem iterate_step_rule22_two_reduction {x : ℤ → ZMod 2} (hx : ∀ j, Odd j → x j = 0) :
    (∀ j, Odd j → (step rule22)^[2] x j = 0) ∧
      reduction ((step rule22)^[2] x) = step rule146 (reduction x) := by
  have hx1 : ∀ k : ℤ, x (2 * k + 1) = 0 := fun k => hx _ ⟨k, rfl⟩
  have hy0 : ∀ k : ℤ, step rule22 x (2 * k) = x (2 * k) := by
    intro k
    change rule22 (x (2 * k - 1)) (x (2 * k)) (x (2 * k + 1)) = _
    rw [show 2 * k - 1 = 2 * (k - 1) + 1 by ring, hx1, hx1]
    simp [rule22]
  have hy1 : ∀ k : ℤ, step rule22 x (2 * k + 1) = x (2 * k) + x (2 * (k + 1)) := by
    intro k
    change rule22 (x (2 * k + 1 - 1)) (x (2 * k + 1)) (x (2 * k + 1 + 1)) = _
    rw [show 2 * k + 1 - 1 = 2 * k by ring, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, hx1]
    simp [rule22]
  constructor
  · rintro j ⟨k, rfl⟩
    change rule22 (step rule22 x (2 * k + 1 - 1)) (step rule22 x (2 * k + 1))
      (step rule22 x (2 * k + 1 + 1)) = 0
    rw [show 2 * k + 1 - 1 = 2 * k by ring, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, hy0, hy1,
      hy0]
    generalize x (2 * k) = a
    generalize x (2 * (k + 1)) = c
    revert a c
    decide
  · funext y
    change rule22 (step rule22 x (2 * y - 1)) (step rule22 x (2 * y)) (step rule22 x (2 * y + 1))
      = rule146 (x (2 * (y - 1))) (x (2 * y)) (x (2 * (y + 1)))
    rw [show 2 * y - 1 = 2 * (y - 1) + 1 by ring, hy1, hy0, hy1,
      show y - 1 + 1 = y by ring]
    generalize x (2 * (y - 1)) = a
    generalize x (2 * y) = b
    generalize x (2 * (y + 1)) = c
    revert a b c
    decide

/-- **Gravner and Griffeath's Lemma 3.1 at every even time**: from a configuration clear at the odd
cells, the orbit of rule `22` at time `2t` is clear at the odd cells and its reduction is the
orbit of rule `146` at time `t` of the reduction. -/
theorem iterate_step_rule22_two_mul_reduction {x : ℤ → ZMod 2} (hx : ∀ j, Odd j → x j = 0)
    (t : ℕ) :
    (∀ j, Odd j → (step rule22)^[2 * t] x j = 0) ∧
      reduction ((step rule22)^[2 * t] x) = (step rule146)^[t] (reduction x) := by
  induction t generalizing x with
  | zero => exact ⟨hx, rfl⟩
  | succ t ih =>
    obtain ⟨h1, h2⟩ := iterate_step_rule22_two_reduction hx
    obtain ⟨h3, h4⟩ := ih h1
    rw [show 2 * (t + 1) = 2 * t + 2 by ring, Function.iterate_add_apply,
      Function.iterate_succ_apply (step rule146)]
    exact ⟨h3, by rw [h4, h2]⟩

/-- The guard: the clearness at the odd cells is load-bearing. At the two cells `0` and `1`, two
steps of rule `22` set the cells `-2` to `3`, whose reduction is the three cells `-1`, `0` and `1`,
while rule `146` carries the reduction, the cell `0`, to the two cells `-1` and `1`. -/
theorem not_iterate_step_rule22_two_reduction_off_even :
    reduction ((step rule22)^[2] (Pi.single 0 1 + Pi.single 1 1 : ℤ → ZMod 2)) ≠
      step rule146 (reduction (Pi.single 0 1 + Pi.single 1 1 : ℤ → ZMod 2)) := by
  intro h
  have h0 := congrFun h 0
  simp only [reduction] at h0
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h0
  revert h0
  decide +kernel

end Rule22Sparse
