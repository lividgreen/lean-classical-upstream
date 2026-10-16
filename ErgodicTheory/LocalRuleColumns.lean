module

public import Batteries.Tactic.OpenPrivate
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
public import ErgodicTheory.DrivenColumns
import all ErgodicTheory.DrivenColumns

/-!
# Columns of a local rule on the line

A local rule `f : Q → Q → Q → Q` acts on every configuration `ℤ → Q` of the line by
`step f x i = f (x (i - 1)) (x i) (x (i + 1))`. The column at a cell `i` along the orbit of `x` is
`t ↦ (step f)^[t] x i`. Nothing here asks for quiescence or finite support unless a statement says
so; the carrier is a type `Q` and all configurations.

## Main results

* `step`, `column`, `window` — the rule on all configurations, the column at a cell along an
  orbit, and the width-`n` window of cells `a, …, a + n - 1` read all at once.
* `eventuallyPeriodic_window_iff` — for finite `Q`, a width-`(m + 1)` window is eventually periodic
  iff its two boundary columns are, by `DrivenColumns.eventuallyPeriodic_of_driven` on the window.
* `eventuallyPeriodic_column_between` — **the driven interior**: for finite `Q`, any rule and any
  configuration, columns at `a` and `b` eventually periodic force the column at every `i` with
  `a ≤ i ≤ b` eventually periodic (Jen 1990, §3);
  `eventuallyPeriodic_column_between_nonvacuous` meets its four hypotheses at once.
* `rule90`, `iterate_two_pow_step90` — **`2 ^ j` steps of rule `90` in one identity**
  (Wolfram 1983): over `ZMod 2` the iterate is
  `x (i - 2 ^ j) + x (i + 2 ^ j)`, by repeated doubling-cancellation, with no binomial coefficient.
* `iterate_step_eq_zero_of_gt` / `iterate_step_eq_zero_of_lt` — a quiescent rule keeps a
  configuration that vanishes past a bound vanishing past that bound moved by the elapsed time.
* `column_step90_single_one_live` / `column_step90_single_one_dead_between` — from the single seed
  `Pi.single 0 1`, the column of rule `90` at cell `1` reads `1` at every stage `2 ^ (j + 1) - 1`
  and `0` at every stage `2 ^ j + r` with `r < 2 ^ j - 1`.
* `not_eventuallyPeriodic_column_step90_single_one` — **that column is not eventually periodic**:
  the gaps between its live stages grow without bound (Jen 1990, Proposition 2).
-/

@[expose] public section

namespace LocalRuleColumns

open private eventuallyPeriodic_shift from ErgodicTheory.DrivenColumns

variable {Q : Type*}

/-- **A local rule on every configuration of the line**: the new value at `i` is
`f` applied to the values at `i - 1`, `i` and `i + 1`. -/
def step (f : Q → Q → Q → Q) (x : ℤ → Q) : ℤ → Q :=
  fun i => f (x (i - 1)) (x i) (x (i + 1))

/-- **The column** at cell `i`: the value read at `i` at stage `t` along the orbit of `x`. -/
def column (f : Q → Q → Q → Q) (x : ℤ → Q) (i : ℤ) : ℕ → Q :=
  fun t => (step f)^[t] x i

/-- **The width-`n` window**: cells `a, a + 1, …, a + n - 1`, read all at once along the orbit. -/
def window (f : Q → Q → Q → Q) (x : ℤ → Q) (a : ℤ) (n : ℕ) : ℕ → (Fin n → Q) :=
  fun t j => (step f)^[t] x (a + ((j : ℕ) : ℤ))

/-- The window's own driven step: the two boundary cells (`j = 0`, `j = m`) are read off directly
from the pair of external inputs, and every interior cell follows the rule from its two
window-internal neighbours. -/
private def windowStep (f : Q → Q → Q → Q) (m : ℕ) :
    (Fin (m + 1) → Q) → (Q × Q) → (Fin (m + 1) → Q) :=
  fun w p j =>
    if hj0 : (j : ℕ) = 0 then p.1
    else if hjm : (j : ℕ) = m then p.2
    else f (w ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩) (w j)
           (w ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩)

/-- **The window form**: over a finite carrier, the whole
width-`(m + 1)` window is eventually periodic iff its two boundary columns are. Forward, two
projections. Backward, `DrivenColumns.eventuallyPeriodic_of_driven` on the window itself: the pair
of boundary columns, shifted one step ahead, is the driving input, and the window's own recursion
matches `windowStep` exactly. -/
theorem eventuallyPeriodic_window_iff [Finite Q] (f : Q → Q → Q → Q) (x : ℤ → Q) (a : ℤ) (m : ℕ) :
    DrivenColumns.EventuallyPeriodic (window f x a (m + 1)) ↔
      DrivenColumns.EventuallyPeriodic (column f x a) ∧
      DrivenColumns.EventuallyPeriodic (column f x (a + (m : ℤ))) := by
  constructor
  · intro hW
    refine ⟨?_, ?_⟩
    · have h := DrivenColumns.eventuallyPeriodic_comp hW (fun w : Fin (m + 1) → Q => w 0)
      have heq : (fun w : Fin (m + 1) → Q => w 0) ∘ window f x a (m + 1) = column f x a := by
        funext t
        simp [window, column]
      rwa [heq] at h
    · have h := DrivenColumns.eventuallyPeriodic_comp hW
        (fun w : Fin (m + 1) → Q => w (Fin.last m))
      have heq : (fun w : Fin (m + 1) → Q => w (Fin.last m)) ∘ window f x a (m + 1)
          = column f x (a + (m : ℤ)) := by
        funext t
        simp [window, column, Fin.last]
      rwa [heq] at h
  · rintro ⟨ha, hb⟩
    have hu : DrivenColumns.EventuallyPeriodic
        (fun t => (column f x a (t + 1), column f x (a + (m : ℤ)) (t + 1))) :=
      DrivenColumns.eventuallyPeriodic_pair (eventuallyPeriodic_shift ha 1)
        (eventuallyPeriodic_shift hb 1)
    have hstep : ∃ N, ∀ t, N ≤ t →
        window f x a (m + 1) (t + 1)
          = windowStep f m (window f x a (m + 1) t)
              (column f x a (t + 1), column f x (a + (m : ℤ)) (t + 1)) := by
      refine ⟨0, fun t _ => ?_⟩
      funext j
      simp only [window, windowStep]
      split_ifs with hj0 hjm
      · rw [hj0]
        simp [column]
      · rw [hjm]
        simp [column]
      · have hjge : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
        have e1 : a + ((j : ℕ) : ℤ) - 1 = a + (((j : ℕ) - 1 : ℕ) : ℤ) := by
          push_cast [hjge]; ring
        have e2 : a + ((j : ℕ) : ℤ) + 1 = a + (((j : ℕ) + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [← e1, ← e2, Function.iterate_succ_apply']
        rfl
    exact DrivenColumns.eventuallyPeriodic_of_driven (windowStep f m) hu hstep

/-- **The driven interior, between two settled columns**:
over a finite carrier, for any rule and any configuration, if the columns at `a` and `b` are each
eventually periodic, so is the column at every `i` with `a ≤ i ≤ b`. `i` sits inside the
width-`(b - a + 1)` window based at `a`, whose two boundary columns are exactly the hypotheses, and
`i`'s column is one coordinate projection of that window. -/
theorem eventuallyPeriodic_column_between [Finite Q] (f : Q → Q → Q → Q) (x : ℤ → Q) {a b i : ℤ}
    (ha : DrivenColumns.EventuallyPeriodic (column f x a))
    (hb : DrivenColumns.EventuallyPeriodic (column f x b))
    (hai : a ≤ i) (hib : i ≤ b) :
    DrivenColumns.EventuallyPeriodic (column f x i) := by
  set m : ℕ := (b - a).toNat with hm_def
  have hab : a + (m : ℤ) = b := by omega
  have hb' : DrivenColumns.EventuallyPeriodic (column f x (a + (m : ℤ))) := by
    rw [hab]; exact hb
  have hW : DrivenColumns.EventuallyPeriodic (window f x a (m + 1)) :=
    (eventuallyPeriodic_window_iff f x a m).mpr ⟨ha, hb'⟩
  set k : ℕ := (i - a).toNat with hk_def
  have hklt : k < m + 1 := by omega
  have hik : a + (k : ℤ) = i := by omega
  have h := DrivenColumns.eventuallyPeriodic_comp hW (fun w : Fin (m + 1) → Q => w ⟨k, hklt⟩)
  have heq : (fun w : Fin (m + 1) → Q => w ⟨k, hklt⟩) ∘ window f x a (m + 1) = column f x i := by
    funext t
    change window f x a (m + 1) t ⟨k, hklt⟩ = column f x i t
    simp only [window, column]
    rw [hik]
  rwa [heq] at h

/-- The joint-satisfiability witness for `eventuallyPeriodic_column_between`'s four hypotheses: the
carrier `Bool`, the rule that keeps the middle value, the constant configuration, and the cells
`a = -1`, `i = 0`, `b = 1`. -/
theorem eventuallyPeriodic_column_between_nonvacuous :
    DrivenColumns.EventuallyPeriodic
        (column (fun (_ b _ : Bool) => b) (fun _ : ℤ => true) (-1)) ∧
      DrivenColumns.EventuallyPeriodic
        (column (fun (_ b _ : Bool) => b) (fun _ : ℤ => true) 1) ∧
      (-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 1 := by
  have hfix : step (fun (_ b _ : Bool) => b) (fun _ : ℤ => true) = fun _ : ℤ => true := rfl
  have hcol : ∀ i : ℤ, DrivenColumns.EventuallyPeriodic
      (column (fun (_ b _ : Bool) => b) (fun _ : ℤ => true) i) := fun i =>
    ⟨1, 0, one_pos, fun u _ => by
      simp only [column, Function.iterate_fixed hfix]⟩
  exact ⟨hcol _, hcol _, by norm_num, by norm_num⟩

/-! ## Rule `90`: the doubling identity -/

/-- **Rule `90`** over `ZMod 2`: the new value is the sum of the two outer neighbours. -/
abbrev rule90 : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 := fun a _ c => a + c

/-- **`2 ^ j` steps of rule `90`, in one identity**: pure
`ZMod 2` cancellation of the doubled middle term, no binomial coefficient and no Lucas' theorem,
and no finiteness of support. -/
theorem iterate_two_pow_step90 :
    ∀ (j : ℕ) (x : ℤ → ZMod 2) (i : ℤ),
      ((step rule90) ^[2 ^ j] x) i = x (i - 2 ^ j) + x (i + 2 ^ j) := by
  intro j
  induction j with
  | zero =>
      intro x i
      change step rule90 x i = x (i - (2 : ℤ) ^ (0 : ℕ)) + x (i + (2 : ℤ) ^ (0 : ℕ))
      norm_num [step]
  | succ j ih =>
      intro x i
      have hiter : (2 : ℕ) ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; ring
      rw [hiter, Function.iterate_add_apply, ih ((step rule90) ^[2 ^ j] x) i,
        ih x (i - (2 : ℤ) ^ j), ih x (i + (2 : ℤ) ^ j)]
      have hpow : (2 : ℤ) ^ (j + 1) = (2 : ℤ) ^ j + (2 : ℤ) ^ j := by rw [pow_succ]; ring
      have e1 : i - (2 : ℤ) ^ j - (2 : ℤ) ^ j = i - (2 : ℤ) ^ (j + 1) := by rw [hpow]; ring
      have e2 : i - (2 : ℤ) ^ j + (2 : ℤ) ^ j = i := by ring
      have e3 : i + (2 : ℤ) ^ j - (2 : ℤ) ^ j = i := by ring
      have e4 : i + (2 : ℤ) ^ j + (2 : ℤ) ^ j = i + (2 : ℤ) ^ (j + 1) := by rw [hpow]; ring
      rw [e1, e2, e3, e4]
      have hcollapse : ∀ a b c : ZMod 2, a + b + (b + c) = a + c := by decide
      exact hcollapse (x (i - (2 : ℤ) ^ (j + 1))) (x i) (x (i + (2 : ℤ) ^ (j + 1)))

/-! ## Quiescent rules: the light cone -/

/-- **The support bound propagates forward, above**: under a quiescent rule, if `x` vanishes past
`M`, every iterate at stage `t` vanishes past `M + t`. -/
theorem iterate_step_eq_zero_of_gt [Zero Q] (f : Q → Q → Q → Q) (hq : f 0 0 0 = 0) (x : ℤ → Q)
    {M : ℤ} (hM : ∀ k : ℤ, M < k → x k = 0) :
    ∀ (t : ℕ) (j : ℤ), M + (t : ℤ) < j → ((step f)^[t] x) j = 0 := by
  intro t
  induction t with
  | zero => intro j hj; exact hM j (by simpa using hj)
  | succ t ih =>
      intro j hj
      rw [Function.iterate_succ_apply']
      change f (((step f)^[t] x) (j - 1)) (((step f)^[t] x) j) (((step f)^[t] x) (j + 1)) = 0
      rw [ih (j - 1) (by push_cast at hj; omega), ih j (by push_cast at hj; omega),
        ih (j + 1) (by push_cast at hj; omega)]
      exact hq

/-- **The support bound propagates forward, below**, the mirror. -/
theorem iterate_step_eq_zero_of_lt [Zero Q] (f : Q → Q → Q → Q) (hq : f 0 0 0 = 0) (x : ℤ → Q)
    {M : ℤ} (hM : ∀ k : ℤ, k < M → x k = 0) :
    ∀ (t : ℕ) (j : ℤ), j < M - (t : ℤ) → ((step f)^[t] x) j = 0 := by
  intro t
  induction t with
  | zero => intro j hj; exact hM j (by simpa using hj)
  | succ t ih =>
      intro j hj
      rw [Function.iterate_succ_apply']
      change f (((step f)^[t] x) (j - 1)) (((step f)^[t] x) j) (((step f)^[t] x) (j + 1)) = 0
      rw [ih (j - 1) (by push_cast at hj; omega), ih j (by push_cast at hj; omega),
        ih (j + 1) (by push_cast at hj; omega)]
      exact hq

/-! ## Rule `90`: the column at cell `1` from the single seed -/

/-- **The light cone's edge is live**: the leftmost reachable cell at stage `r`, from the single
seed `Pi.single 0 1` under rule `90`, always carries a `1`. -/
private theorem step90_single_edge :
    ∀ r : ℕ,
      ((step rule90) ^[r] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2)) (-(r : ℤ)) = 1 := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
      have hM : ∀ k : ℤ, k < 0 → (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2) k = 0 := by
        intro k hk
        exact Pi.single_eq_of_ne (by omega) _
      have hq : rule90 0 0 0 = 0 := by decide
      have hleft2 := iterate_step_eq_zero_of_lt rule90 hq
        (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2) hM r (-(r : ℤ) - 2) (by omega)
      change ((step rule90) ^[r + 1] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2))
        (-((r : ℤ) + 1)) = 1
      have e1 : -((r : ℤ) + 1) - 1 = -(r : ℤ) - 2 := by ring
      have e2 : -((r : ℤ) + 1) + 1 = -(r : ℤ) := by ring
      rw [Function.iterate_succ_apply']
      simp only [step, rule90]
      rw [e1, e2, hleft2, ih]
      decide

/-- The doubling identity read at cell `1` from the single seed. -/
private theorem step90_single_step (j r : ℕ) :
    ((step rule90) ^[2 ^ j + r] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2)) 1
      = ((step rule90) ^[r] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2)) (1 - 2 ^ j)
        + ((step rule90) ^[r] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2)) (1 + 2 ^ j) := by
  rw [Function.iterate_add_apply, iterate_two_pow_step90]

/-- **Live at `2 ^ (j + 1) - 1`**: from the single seed, the
column of rule `90` at cell `1` reads `1` at every stage `2 ^ j' - 1` with `j' ≥ 1`. Route:
`2 ^ (j + 1) - 1 = 2 ^ j + (2 ^ j - 1)`, and the doubling identity at `r = 2 ^ j - 1` gives the
live edge cell plus a cell beyond the `r`-step support. -/
theorem column_step90_single_one_live (j : ℕ) :
    ((step rule90) ^[2 ^ (j + 1) - 1] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2)) 1 = 1 := by
  have h1 : (1 : ℕ) ≤ 2 ^ j := Nat.one_le_two_pow
  have hidx : 2 ^ j + (2 ^ j - 1) = 2 ^ (j + 1) - 1 := by rw [pow_succ]; omega
  have hstep := step90_single_step j (2 ^ j - 1)
  rw [hidx] at hstep
  have hcast : ((2 ^ j - 1 : ℕ) : ℤ) = (2 : ℤ) ^ j - 1 := by
    rw [Nat.cast_sub h1]; push_cast; ring
  have hEdge := step90_single_edge (2 ^ j - 1)
  have heq : -((2 ^ j - 1 : ℕ) : ℤ) = 1 - (2 : ℤ) ^ j := by rw [hcast]; ring
  rw [heq] at hEdge
  have hM0 : ∀ k : ℤ, 0 < k → (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2) k = 0 := by
    intro k hk; exact Pi.single_eq_of_ne (by omega) _
  have hq : rule90 0 0 0 = 0 := by decide
  have hZero := iterate_step_eq_zero_of_gt rule90 hq
    (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2) hM0 (2 ^ j - 1) (1 + (2 : ℤ) ^ j) (by omega)
  rw [hstep, hEdge, hZero]
  decide

/-- **Dead strictly between two live stages**: at `2 ^ j + r`
with `r < 2 ^ j - 1`, the column of rule `90` at cell `1` from the single seed reads `0`. Both
summands of the doubling identity land beyond the `r`-step support, above (`1 + 2 ^ j`) and below
(`1 - 2 ^ j`, exactly where `r < 2 ^ j - 1` bites). -/
theorem column_step90_single_one_dead_between (j r : ℕ) (hr : r < 2 ^ j - 1) :
    ((step rule90) ^[2 ^ j + r] (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2)) 1 = 0 := by
  have hcastp : ((2 ^ j : ℕ) : ℤ) = (2 : ℤ) ^ j := by push_cast; ring
  have hstep := step90_single_step j r
  have hM0 : ∀ k : ℤ, 0 < k → (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2) k = 0 := by
    intro k hk; exact Pi.single_eq_of_ne (by omega) _
  have hMlt : ∀ k : ℤ, k < 0 → (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2) k = 0 := by
    intro k hk; exact Pi.single_eq_of_ne (by omega) _
  have hq : rule90 0 0 0 = 0 := by decide
  have hZ1 := iterate_step_eq_zero_of_lt rule90 hq
    (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2) hMlt r (1 - (2 : ℤ) ^ j) (by omega)
  have hZ2 := iterate_step_eq_zero_of_gt rule90 hq
    (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2) hM0 r (1 + (2 : ℤ) ^ j) (by omega)
  rw [hstep, hZ1, hZ2]
  decide

/-- **The column of rule `90` at cell `1` is not eventually periodic**, from the single seed
`Pi.single 0 1`. Given a period `P` from `N`, pick `j` past `N + P + 1`; stage `2 ^ j - 1` is live
and stage `2 ^ j - 1 + P` is dead, contradicting the period. -/
theorem not_eventuallyPeriodic_column_step90_single_one :
    ¬ DrivenColumns.EventuallyPeriodic
      (column rule90 (Pi.single (0 : ℤ) (1 : ZMod 2) : ℤ → ZMod 2) 1) := by
  rintro ⟨P, N, hP, hper⟩
  set j : ℕ := N + P + 2 with hj_def
  have hjbig : N + P + 1 < 2 ^ j := by
    have hlt := Nat.lt_two_pow_self (n := j)
    omega
  have hj1 : 1 ≤ j := by omega
  have hlive := column_step90_single_one_live (j - 1)
  rw [show j - 1 + 1 = j from by omega] at hlive
  have ht1N : N ≤ 2 ^ j - 1 := by omega
  have hr : P - 1 < 2 ^ j - 1 := by omega
  have hdb := column_step90_single_one_dead_between j (P - 1) hr
  have hidx : 2 ^ j + (P - 1) = 2 ^ j - 1 + P := by omega
  rw [hidx] at hdb
  have hthis := hper (2 ^ j - 1) ht1N
  simp only [column] at hthis
  rw [hdb, hlive] at hthis
  exact absurd hthis (by decide)

end LocalRuleColumns
