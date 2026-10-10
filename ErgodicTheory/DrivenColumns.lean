/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false


/-!
# Driven columns: finite systems fed by an eventually periodic input

This module holds the engine alone; `EventuallyPeriodic` is defined here. The driven interior, the
window form and table `90`'s column, stated for a local rule on all configurations of the line, are
in `ErgodicTheory/LocalRuleColumns.lean`; their table-rule forms and the rays described below live
in `CellularAutomata/ObservedRays.lean` (in the companion package
`elementary_cellular_automata`).

([RuleSpace] §4 Proposition 4.2, [RuleSpace] §4 Remark 4.1)

`CellularAutomata/ObservedColumn.lean` (in the companion package `elementary_cellular_automata`)
proves a table's own column eventually periodic when the diameter along its orbit never grows,
and exhibits an accreting table (`f90`) whose single-seed CENTER column is nonetheless eventually
periodic — the converse fails. This file extends that machinery two ways.

First, a finite-valued sequence driven by an eventually periodic input is itself eventually
periodic (`eventuallyPeriodic_of_driven`), by a pigeonhole-and-propagate argument independent of
table rules entirely. Applied to a table's own recursion, this gives: the columns strictly between
two settled columns are eventually periodic too (`eventuallyPeriodic_observedColumn_between`, via
the window form `eventuallyPeriodic_observedWindow_iff`), and the diagonal RAYS moving at the
rule's own light-cone speed are always eventually periodic, at every quiescent table and every
finitely-supported seed (`eventuallyPeriodic_observedRay_one`/`_neg_one`), with speed zero
recovering the column (`observedRay_zero`) and every other integer speed beyond `±1` running
outside the light cone entirely (not treated here).

Second, `f90`'s single-seed column at cell `1` — one cell over from the center column
`CellularAutomata/ObservedColumn.lean` already settles — is NOT eventually periodic
(`not_eventuallyPeriodic_observedColumn_f90_single_one`): it reads `1` at every stage `2 ^ j - 1`
(`j ≥ 1`) and `0` strictly between consecutive such stages, a gap that grows without bound. The
identity behind this (`iterate_two_pow_f90`) is pure `ZMod 2` cancellation over `2 ^ j` steps, no
binomial coefficient and no Lucas' theorem.

## Main results

* `eventuallyPeriodic_of_driven` — **the engine**: `[Finite α]`, a driving input eventually
  periodic in `ι`, and a step relation `a (t + 1) = g (a t) (u t)` give `a` eventually periodic.
  `eventuallyPeriodic_comp`/`eventuallyPeriodic_pair` — post-composition and pairing, its two
  standing closure facts. `eventuallyPeriodic_of_driven_nonvacuous` — a period-two `Bool` input and
  its running `xor`, meeting both hypotheses at once with the driven sequence itself not constant.
* `observedWindow`, `eventuallyPeriodic_observedWindow_iff` — a width-`(m + 1)` window is
  eventually periodic iff its two boundary columns are.
* `eventuallyPeriodic_observedColumn_between` — **the driven interior**: at `a ≤ i ≤ b`, columns
  eventually periodic at both `a` and `b` force the column at `i` eventually periodic too — a
  corollary of the window form. `eventuallyPeriodic_observedColumn_between_nonvacuous` meets its
  four hypotheses at once, at the shift `f170` from the single seed.
* `observedRay`, `observedRay_zero` — the ray at integer speed `v` from cell `e`, agreeing with the
  observed column at `v = 0`.
* `eventuallyPeriodic_observedRay_one` / `eventuallyPeriodic_observedRay_neg_one` — **the rays at
  the rule's own speed** are eventually periodic, at every quiescent table (`f 0 0 0 = 0`) and
  every finitely-supported seed, with no further hypothesis on either.
* `iterate_two_pow_f90` — `2 ^ j` steps of rule `90`, folded into one identity by repeated
  `ZMod 2` doubling-cancellation.
* `observedColumn_f90_single_one_live` / `observedColumn_f90_single_one_dead_between` — the
  single-seed column at cell `1`, under `f90`, reads `1` at every stage `2 ^ (j + 1) - 1` and `0`
  at every stage strictly between two such stages. `observedColumn_f90_single_one` assembles the
  two halves into one equality, the dyadic block a step falls in named by `Nat.log 2`.
* `not_eventuallyPeriodic_observedColumn_f90_single_one` — **the first column proved not
  eventually periodic**: the gap between consecutive live stages grows without bound, past any
  claimed period.
* `eventuallyPeriodic_observedColumn_between_guard` — the guard: one settled end does not settle
  the cells beside it, at `f90`, cells `0` and `1`.
* `not_eventuallyPeriodic_observedRay_zero_f90` — the guard: the ray theorems' speed is
  load-bearing, since speed `0` on this same witness is exactly the column just proved not
  eventually periodic.

## Scope

Registered as [RuleSpace] §4 Proposition 4.2, rows RS-5 and RS-6: the engine is its clause (i),
the window form and the driven interior its clause (ii), the rays its clause (iii), and the
doubling identity with the column at cell `1` its clause (iv). [RuleSpace] §4 Remark 4.1 is the
statement it extends.

The column at cell `1` is stated first as its two halves, `observedColumn_f90_single_one_live` and
`observedColumn_f90_single_one_dead_between`, and
`not_eventuallyPeriodic_observedColumn_f90_single_one` consumes the two halves alone rather than
the assembled equality. `observedColumn_f90_single_one` assembles them, over `Classical`
decidability of the existential condition, into the one equality covering every step.

Every theorem is stated at `tableRule f hq`, never at an arbitrary radius-one `U`, and the ray
theorems are stated for every table meeting quiescence alone and every finitely-supported seed —
no result here is specialized to `f90` beyond the column-`1` witness (which is precisely about
`f90`) and the guard pair built on it.
-/


@[expose] public section

namespace GrowingComposite

/-- **Eventual periodicity** of a `ℕ`-indexed sequence: a period `P` that holds from some point `N`
on. Absent from Mathlib (`Function.Periodic` is the exact-periodicity form) and minted here. -/
def EventuallyPeriodic {α : Type*} (f : ℕ → α) : Prop :=
  ∃ P N, 0 < P ∧ ∀ u, N ≤ u → f (u + P) = f u

end GrowingComposite

namespace DrivenColumns

/-! ## Piece 1: the engine -/

/-- **Iterating an eventual period**: `k` copies of a period `P` still return `f` to its own value,
past the same threshold. -/
private theorem eventuallyPeriodic_apply_add_mul {α : Type*} {f : ℕ → α} {P N : ℕ}
    (hper : ∀ t, N ≤ t → f (t + P) = f t) (t : ℕ) (ht : N ≤ t) (k : ℕ) :
    f (t + k * P) = f t := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show t + (k + 1) * P = (t + k * P) + P from by ring, hper (t + k * P) (by omega), ih]

/-- **The engine** ([RuleSpace] §4 Proposition 4.2(i), row RS-5): a finite-valued sequence driven
by an eventually periodic input is itself eventually periodic. The values `a (N₁ + j * P)`, `N₁`
past both `hstep`'s own threshold and the input's, range over the finite type `α`, so two of them
coincide at some `j < j'`; propagating that coincidence forward one step at a time through `hstep`
and the input's own periodicity extends it to every later stage, at period `(j' - j) * P`. -/
theorem eventuallyPeriodic_of_driven {α ι : Type*} [Finite α] (g : α → ι → α)
    {u : ℕ → ι} {a : ℕ → α} (hu : GrowingComposite.EventuallyPeriodic u)
    (hstep : ∃ N, ∀ t, N ≤ t → a (t + 1) = g (a t) (u t)) :
    GrowingComposite.EventuallyPeriodic a := by
  classical
  obtain ⟨P, N₀, hP, hperu⟩ := hu
  obtain ⟨N, hstepN⟩ := hstep
  set N₁ : ℕ := max N N₀ with hN₁_def
  obtain ⟨j, j', hjj', heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun j : ℕ => a (N₁ + j * P)) (fun j => Set.mem_univ _) Set.finite_univ
  set Δ : ℕ := j' - j with hΔ_def
  have hΔpos : 0 < Δ := by omega
  have hjΔ : j' = j + Δ := by omega
  set M : ℕ := N₁ + j * P with hM_def
  have hMN : N ≤ M := by rw [hM_def, hN₁_def]; omega
  have hMN₀ : N₀ ≤ M := by rw [hM_def, hN₁_def]; omega
  have hbase : a (M + Δ * P) = a M := by
    have hidx : M + Δ * P = N₁ + j' * P := by rw [hM_def, hjΔ]; ring
    rw [hidx]; exact heq.symm
  have hind : ∀ r : ℕ, a (M + r + Δ * P) = a (M + r) := by
    intro r
    induction r with
    | zero => simpa using hbase
    | succ r ih =>
        have hrM : N ≤ M + r := le_trans hMN (Nat.le_add_right _ _)
        have hrM' : N ≤ M + r + Δ * P := le_trans hrM (Nat.le_add_right _ _)
        have hrM0 : N₀ ≤ M + r := le_trans hMN₀ (Nat.le_add_right _ _)
        have h1 : a (M + r + 1) = g (a (M + r)) (u (M + r)) := hstepN (M + r) hrM
        have h2 : a (M + r + Δ * P + 1) = g (a (M + r + Δ * P)) (u (M + r + Δ * P)) :=
          hstepN (M + r + Δ * P) hrM'
        have hu_eq : u (M + r + Δ * P) = u (M + r) :=
          eventuallyPeriodic_apply_add_mul hperu (M + r) hrM0 Δ
        calc a (M + (r + 1) + Δ * P)
            = a (M + r + Δ * P + 1) := by congr 1; ring
          _ = g (a (M + r + Δ * P)) (u (M + r + Δ * P)) := h2
          _ = g (a (M + r)) (u (M + r + Δ * P)) := by rw [ih]
          _ = g (a (M + r)) (u (M + r)) := by rw [hu_eq]
          _ = a (M + r + 1) := h1.symm
          _ = a (M + (r + 1)) := rfl
  refine ⟨Δ * P, M, Nat.mul_pos hΔpos hP, fun t ht => ?_⟩
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact hind r

/-- **Post-composition** ([RuleSpace] §4 Proposition 4.2(i), row RS-5): an eventually periodic
sequence stays eventually periodic under any further map. -/
theorem eventuallyPeriodic_comp {α β : Type*} {f : ℕ → α}
    (hf : GrowingComposite.EventuallyPeriodic f) (φ : α → β) :
    GrowingComposite.EventuallyPeriodic (φ ∘ f) := by
  obtain ⟨P, N, hP, hper⟩ := hf
  exact ⟨P, N, hP, fun t ht => by simp only [Function.comp_apply, hper t ht]⟩

/-- **Pairing** ([RuleSpace] §4 Proposition 4.2(i), row RS-5): two eventually periodic sequences
pair into one, at the product of their periods and the later of their thresholds. -/
theorem eventuallyPeriodic_pair {α β : Type*} {f : ℕ → α} {g : ℕ → β}
    (hf : GrowingComposite.EventuallyPeriodic f) (hg : GrowingComposite.EventuallyPeriodic g) :
    GrowingComposite.EventuallyPeriodic (fun t => (f t, g t)) := by
  obtain ⟨P₁, N₁, hP₁, hper₁⟩ := hf
  obtain ⟨P₂, N₂, hP₂, hper₂⟩ := hg
  refine ⟨P₁ * P₂, max N₁ N₂, Nat.mul_pos hP₁ hP₂, fun t ht => ?_⟩
  change (f (t + P₁ * P₂), g (t + P₁ * P₂)) = (f t, g t)
  have h1 : f (t + P₁ * P₂) = f t := by
    have h := eventuallyPeriodic_apply_add_mul hper₁ t (le_trans (le_max_left N₁ N₂) ht) P₂
    rwa [show P₂ * P₁ = P₁ * P₂ from by ring] at h
  have h2 : g (t + P₁ * P₂) = g t :=
    eventuallyPeriodic_apply_add_mul hper₂ t (le_trans (le_max_right N₁ N₂) ht) P₁
  rw [h1, h2]

/-- **A shift of an eventually periodic sequence stays eventually periodic**, at the same period and
threshold: internal plumbing for reading a driven state's value one step ahead. -/
private theorem eventuallyPeriodic_shift {α : Type*} {f : ℕ → α}
    (hf : GrowingComposite.EventuallyPeriodic f) (k : ℕ) :
    GrowingComposite.EventuallyPeriodic (fun t => f (t + k)) := by
  obtain ⟨P, N, hP, hper⟩ := hf
  refine ⟨P, N, hP, fun t ht => ?_⟩
  change f (t + P + k) = f (t + k)
  rw [show t + P + k = t + k + P from by ring]
  exact hper (t + k) (by omega)

/-- The smallest instance meeting `eventuallyPeriodic_of_driven`'s two hypotheses, with the driven
sequence itself not constant: a period-two input and its running XOR. -/
def nonvacDriven_u : ℕ → Bool := fun t => decide (t % 2 = 0)

def nonvacDriven_a : ℕ → Bool
  | 0 => false
  | t + 1 => xor (nonvacDriven_a t) (nonvacDriven_u t)

theorem eventuallyPeriodic_of_driven_nonvacuous :
    GrowingComposite.EventuallyPeriodic nonvacDriven_u ∧
      (∃ N, ∀ t, N ≤ t →
        nonvacDriven_a (t + 1) = xor (nonvacDriven_a t) (nonvacDriven_u t)) ∧
      nonvacDriven_a 0 ≠ nonvacDriven_a 1 := by
  refine ⟨⟨2, 0, by norm_num, fun t _ => ?_⟩, ⟨0, fun _ _ => rfl⟩, by decide⟩
  show nonvacDriven_u (t + 2) = nonvacDriven_u t
  have ht2 : (t + 2) % 2 = t % 2 := by omega
  simp only [nonvacDriven_u, ht2]

end DrivenColumns

/-! ## Axiom audit

Every public theorem above is `#print axioms`-clean on the standard triple, and the guards below
make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'DrivenColumns.eventuallyPeriodic_of_driven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_of_driven

/-- info: 'DrivenColumns.eventuallyPeriodic_comp' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_comp

/-- info: 'DrivenColumns.eventuallyPeriodic_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_pair

/-- info: 'DrivenColumns.eventuallyPeriodic_of_driven_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_of_driven_nonvacuous
