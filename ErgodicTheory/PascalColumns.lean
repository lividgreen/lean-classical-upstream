module

public import ErgodicTheory.LocalRuleColumns
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Bitwise

/-!
# Rule `90` from the single seed is Pascal's triangle modulo two

Rule `90` from the single seed `Pi.single 0 1` is Pascal's triangle modulo two (Wolfram 1983):
at step `a + b` and cell `a - b` the orbit reads the binomial coefficient `(a + b).choose a`
reduced modulo two, and every other cell reads `0`. Lucas's theorem at the prime two turns the
coefficient into a digit criterion: it is odd exactly when `a` and `b` share no binary digit.

## Main results

* `step_rule90_single_pascal` — **Pascal's triangle modulo two**: the orbit of the single seed
  under rule `90` reads `(a + b).choose a` in `ZMod 2` at cell `a - b` and step `a + b`, by the
  Pascal recurrence.
* `step_rule90_single_eq_zero_of_odd`, `step_rule90_single_eq_zero_of_lt_abs` — every other cell
  reads `0`: where step plus cell is odd, and outside the light cone.
* `choose_add_mod_two_eq_one_iff` — **Lucas's theorem at the prime two**: `(a + b).choose a` is
  odd iff `a &&& b = 0`, by Lucas's congruence on the lowest binary digit and induction on the
  remaining digits.
* `choose_three_mul_mod_two_eq_one_iff` — the same criterion at `a = m`, `b = 2 m`: `C(3 m, m)` is
  odd iff `m &&& (2 * m) = 0`.
* `and_two_mul_eq_zero_iff` — `m` and `2 m` share no binary digit iff `m` has no two adjacent binary
  ones. Together with the previous statement this is the comment of the OEIS's entry A003714: the
  numbers with no two adjacent binary ones are exactly the `m` with `C(3 m, m)` odd, a consequence
  of Lucas's theorem at the prime two.
* `step_rule90_single_eq_one_iff` — the two combined: at step `a + b` and cell `a - b` the orbit
  of the single seed reads `1` iff `a &&& b = 0`.
-/

@[expose] public section

namespace PascalColumns

open LocalRuleColumns

/-! ## Lucas's theorem at the prime two -/

private theorem and_eq_zero_iff_div_two (a b : ℕ) :
    a &&& b = 0 ↔ (a % 2 = 0 ∨ b % 2 = 0) ∧ (a / 2) &&& (b / 2) = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 : (a &&& b).testBit 0 = (0 : ℕ).testBit 0 := by rw [h]
      simp [Nat.testBit_zero] at h0
      omega
    · apply Nat.eq_of_testBit_eq
      intro i
      have h1 : (a &&& b).testBit (i + 1) = (0 : ℕ).testBit (i + 1) := by rw [h]
      rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, Nat.zero_testBit] at h1
      rw [Nat.testBit_and, Nat.zero_testBit]
      exact h1
  · rintro ⟨h0, h1⟩
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases i with
    | zero =>
        simp only [Nat.testBit_zero]
        simp
        omega
    | succ i =>
        have h2 : ((a / 2) &&& (b / 2)).testBit i = (0 : ℕ).testBit i := by rw [h1]
        rw [Nat.testBit_and, Nat.zero_testBit] at h2
        rw [Nat.testBit_succ, Nat.testBit_succ]
        exact h2

/-- **Lucas's theorem at the prime two** (Lucas 1878): the binomial coefficient
`(a + b).choose a` is odd exactly when `a` and `b` share no binary digit. Lucas's congruence
`Choose.choose_modEq_choose_mod_mul_choose_div_nat` at `p = 2` splits off the lowest binary digit
of `a` and of `b`, and the remaining digits are the same statement at `a / 2` and `b / 2`. -/
theorem choose_add_mod_two_eq_one_iff :
    ∀ a b : ℕ, Nat.choose (a + b) a % 2 = 1 ↔ a &&& b = 0 := by
  suffices h : ∀ n a b : ℕ, a + b = n → (Nat.choose (a + b) a % 2 = 1 ↔ a &&& b = 0) from
    fun a b => h _ a b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn
  subst hn
  by_cases h00 : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h00
    simp
  have hlt : a / 2 + b / 2 < a + b := by omega
  have ih' := ih _ hlt (a / 2) (b / 2) rfl
  have key : Nat.choose (a + b) a % 2 =
      (Nat.choose ((a + b) % 2) (a % 2) * Nat.choose ((a + b) / 2) (a / 2)) % 2 :=
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  rw [and_eq_zero_iff_div_two, key]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · have h1 : (a + b) % 2 = 0 := by omega
    have h2 : (a + b) / 2 = a / 2 + b / 2 := by omega
    rw [h1, h2, ha]
    simp only [Nat.choose_self, one_mul]
    rw [ih']
    simp
  · have h1 : (a + b) % 2 = 1 := by omega
    have h2 : (a + b) / 2 = a / 2 + b / 2 := by omega
    rw [h1, h2, ha]
    simp only [Nat.choose_zero_right, one_mul]
    rw [ih']
    simp
  · have h1 : (a + b) % 2 = 1 := by omega
    have h2 : (a + b) / 2 = a / 2 + b / 2 := by omega
    rw [h1, h2, ha]
    simp only [Nat.choose_self, one_mul]
    rw [ih']
    simp [hb]
  · have h1 : (a + b) % 2 = 0 := by omega
    rw [h1, ha]
    simp only [Nat.choose_zero_succ, zero_mul, Nat.zero_mod, zero_ne_one, false_iff]
    omega

/-- The binomial coefficient `C(3 m, m)` is odd exactly when `m` and `2 m` share no binary digit. -/
theorem choose_three_mul_mod_two_eq_one_iff (m : ℕ) :
    Nat.choose (3 * m) m % 2 = 1 ↔ m &&& (2 * m) = 0 := by
  have h := choose_add_mod_two_eq_one_iff m (2 * m)
  rwa [show m + 2 * m = 3 * m by omega] at h

/-- `m` and `2 m` share no binary digit exactly when `m` has no two adjacent binary ones. -/
theorem and_two_mul_eq_zero_iff (m : ℕ) :
    m &&& (2 * m) = 0 ↔ ∀ i : ℕ, ¬ (m.testBit i = true ∧ m.testBit (i + 1) = true) := by
  have hshift : ∀ i : ℕ, (2 * m).testBit (i + 1) = m.testBit i := by
    intro i
    rw [Nat.testBit_succ, show 2 * m / 2 = m by omega]
  constructor
  · intro h i hi
    have h1 : (m &&& (2 * m)).testBit (i + 1) = (0 : ℕ).testBit (i + 1) := by rw [h]
    rw [Nat.testBit_and, hshift, Nat.zero_testBit, hi.1, hi.2] at h1
    simp at h1
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases j with
    | zero => simp [Nat.testBit_zero]
    | succ i =>
        rw [hshift]
        have hi := h i
        cases hmi : m.testBit i <;> cases hmj : m.testBit (i + 1) <;> simp_all

/-! ## The cells of the orbit -/

/-- **Parity**: the orbit of the single seed under rule `90` reads `0` where step plus cell is
odd. -/
theorem step_rule90_single_eq_zero_of_odd (t : ℕ) (x : ℤ) (h : ¬ 2 ∣ ((t : ℤ) + x)) :
    ((step rule90)^[t] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2)) x = 0 := by
  induction t generalizing x with
  | zero =>
    have hx : x ≠ 0 := by
      intro h0
      subst h0
      simp at h
    simp [Pi.single_eq_of_ne hx]
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    change ((step rule90)^[t] _ (x - 1)) + ((step rule90)^[t] _ (x + 1)) = 0
    rw [ih (x - 1) (by push_cast at h ⊢; omega), ih (x + 1) (by push_cast at h ⊢; omega)]
    decide

/-- **The light cone**: the orbit of the single seed under rule `90` reads `0` outside it. -/
theorem step_rule90_single_eq_zero_of_lt_abs (t : ℕ) (i : ℤ) (h : (t : ℤ) < |i|) :
    ((step rule90)^[t] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2)) i = 0 := by
  have hq : rule90 0 0 0 = 0 := by decide
  have hM : ∀ k : ℤ, k ≠ 0 → (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2) k = 0 :=
    fun k hk => Pi.single_eq_of_ne hk _
  rcases lt_abs.mp h with h1 | h1
  · exact iterate_step_eq_zero_of_gt rule90 hq _ (M := 0) (fun k hk => hM k (by omega)) t i
      (by omega)
  · exact iterate_step_eq_zero_of_lt rule90 hq _ (M := 0) (fun k hk => hM k (by omega)) t i
      (by omega)

/-! ## Pascal's triangle modulo two -/

/-- **Pascal's triangle modulo two** (Wolfram 1983): rule `90`
from the single seed reads `(a + b).choose a`, reduced modulo two, at cell `a - b` and step
`a + b`. The Pascal recurrence `(n + 1).choose (k + 1) = n.choose k + n.choose (k + 1)` is rule
`90`'s own step; the two edges `b = 0` and `a = 0` read the light cone's live boundary. -/
theorem step_rule90_single_pascal :
    ∀ a b : ℕ,
      ((step rule90)^[a + b] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2)) ((a : ℤ) - b)
        = ((Nat.choose (a + b) a : ℕ) : ZMod 2) := by
  suffices h : ∀ n a b : ℕ, a + b = n →
      ((step rule90)^[a + b] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2)) ((a : ℤ) - b)
        = ((Nat.choose (a + b) a : ℕ) : ZMod 2) from
    fun a b => h _ a b rfl
  intro n
  induction n with
  | zero =>
    intro a b hn
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    simp
  | succ n ih =>
    intro a b hn
    have ih' : ∀ a b : ℕ, a + b = n →
        ((step rule90)^[n] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2)) ((a : ℤ) - b)
          = ((Nat.choose n a : ℕ) : ZMod 2) := fun a b h => by
      have := ih a b h
      rwa [h] at this
    rw [hn, Function.iterate_succ_apply']
    change ((step rule90)^[n] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2) ((a : ℤ) - b - 1))
      + ((step rule90)^[n] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2) ((a : ℤ) - b + 1)) = _
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · omega
      · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        have h1 := ih' 0 b' (by omega)
        have h2 := step_rule90_single_eq_zero_of_lt_abs n (((0 : ℕ) : ℤ) - ((b' + 1 : ℕ) : ℤ) - 1)
          (by push_cast; rw [abs_of_neg (by omega)]; omega)
        rw [h2, zero_add, show ((0 : ℕ) : ℤ) - ((b' + 1 : ℕ) : ℤ) + 1 = ((0 : ℕ) : ℤ) - b' by
          push_cast; ring, h1]
        simp
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · have h1 := ih' a' 0 (by omega)
        have h2 := step_rule90_single_eq_zero_of_lt_abs n (((a' + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) + 1)
          (by push_cast; rw [abs_of_pos (by omega)]; omega)
        rw [h2, add_zero, show ((a' + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - 1 = (a' : ℤ) - ((0 : ℕ) : ℤ) by
          push_cast; ring, h1]
        obtain rfl : n = a' := by omega
        simp
      · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        have h1 := ih' a' (b' + 1) (by omega)
        have h2 := ih' (a' + 1) b' (by omega)
        rw [show ((a' + 1 : ℕ) : ℤ) - ((b' + 1 : ℕ) : ℤ) - 1 = (a' : ℤ) - ((b' + 1 : ℕ) : ℤ) by
            push_cast; ring,
          show ((a' + 1 : ℕ) : ℤ) - ((b' + 1 : ℕ) : ℤ) + 1 = ((a' + 1 : ℕ) : ℤ) - (b' : ℤ) by
            push_cast; ring, h1, h2]
        rw [Nat.choose_succ_succ, Nat.cast_add]

/-- **The digit criterion for the single seed**: at step `a + b` and cell `a - b` the orbit of
the single seed under rule `90` reads `1` exactly when `a` and `b` share no binary digit.
Pascal's triangle modulo two (`step_rule90_single_pascal`) with Lucas's theorem at the prime two
(`choose_add_mod_two_eq_one_iff`). -/
theorem step_rule90_single_eq_one_iff (a b : ℕ) :
    ((step rule90)^[a + b] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2)) ((a : ℤ) - b) = 1
      ↔ a &&& b = 0 := by
  rw [step_rule90_single_pascal, ← choose_add_mod_two_eq_one_iff]
  have e := ZMod.natCast_mod (Nat.choose (a + b) a) 2
  rcases Nat.mod_two_eq_zero_or_one (Nat.choose (a + b) a) with h | h
  · rw [h] at e
    simp [← e, h]
  · rw [h] at e
    simp [← e, h]

end PascalColumns
