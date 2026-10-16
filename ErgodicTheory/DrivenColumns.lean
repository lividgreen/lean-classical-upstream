module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring


/-!
# Driven columns: finite systems fed by an eventually periodic input

A finite-valued sequence driven by an eventually periodic input is itself eventually periodic
(Endrullis, Hendriks and Klop 2011), by a pigeonhole-and-propagate argument independent of any
particular system. `EventuallyPeriodic` is defined here. The driven interior, the window form and
the column of rule `90`, stated for a local rule on all configurations of the line, are in
`ErgodicTheory/LocalRuleColumns.lean`.

## Main results

* `eventuallyPeriodic_of_driven` — **the engine**: `[Finite α]`, a driving input eventually
  periodic in `ι`, and a step relation `a (t + 1) = g (a t) (u t)` give `a` eventually periodic.
  `eventuallyPeriodic_comp`/`eventuallyPeriodic_pair` — post-composition and pairing, its two
  standing closure facts. `eventuallyPeriodic_of_driven_nonvacuous` — a period-two `Bool` input and
  its running `xor`, meeting both hypotheses at once with the driven sequence itself not constant.
-/


@[expose] public section

namespace DrivenColumns

/-- **Eventual periodicity** of a `ℕ`-indexed sequence: a period `P` that holds from some point `N`
on. Absent from Mathlib (`Function.Periodic` is the exact-periodicity form) and minted here. -/
def EventuallyPeriodic {α : Type*} (f : ℕ → α) : Prop :=
  ∃ P N, 0 < P ∧ ∀ u, N ≤ u → f (u + P) = f u

/-! ## The engine -/

/-- **Iterating an eventual period**: `k` copies of a period `P` still return `f` to its own value,
past the same threshold. -/
private theorem eventuallyPeriodic_apply_add_mul {α : Type*} {f : ℕ → α} {P N : ℕ}
    (hper : ∀ t, N ≤ t → f (t + P) = f t) (t : ℕ) (ht : N ≤ t) (k : ℕ) :
    f (t + k * P) = f t := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show t + (k + 1) * P = (t + k * P) + P from by ring, hper (t + k * P) (by omega), ih]

/-- **The engine**: a finite-valued sequence driven
by an eventually periodic input is itself eventually periodic. The values `a (N₁ + j * P)`, `N₁`
past both `hstep`'s own threshold and the input's, range over the finite type `α`, so two of them
coincide at some `j < j'`; propagating that coincidence forward one step at a time through `hstep`
and the input's own periodicity extends it to every later stage, at period `(j' - j) * P`. -/
theorem eventuallyPeriodic_of_driven {α ι : Type*} [Finite α] (g : α → ι → α)
    {u : ℕ → ι} {a : ℕ → α} (hu : DrivenColumns.EventuallyPeriodic u)
    (hstep : ∃ N, ∀ t, N ≤ t → a (t + 1) = g (a t) (u t)) :
    DrivenColumns.EventuallyPeriodic a := by
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

/-- **Post-composition**: an eventually periodic
sequence stays eventually periodic under any further map. -/
theorem eventuallyPeriodic_comp {α β : Type*} {f : ℕ → α}
    (hf : DrivenColumns.EventuallyPeriodic f) (φ : α → β) :
    DrivenColumns.EventuallyPeriodic (φ ∘ f) := by
  obtain ⟨P, N, hP, hper⟩ := hf
  exact ⟨P, N, hP, fun t ht => by simp only [Function.comp_apply, hper t ht]⟩

/-- **Pairing**: two eventually periodic sequences
pair into one, at the product of their periods and the later of their thresholds. -/
theorem eventuallyPeriodic_pair {α β : Type*} {f : ℕ → α} {g : ℕ → β}
    (hf : DrivenColumns.EventuallyPeriodic f) (hg : DrivenColumns.EventuallyPeriodic g) :
    DrivenColumns.EventuallyPeriodic (fun t => (f t, g t)) := by
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
    (hf : DrivenColumns.EventuallyPeriodic f) (k : ℕ) :
    DrivenColumns.EventuallyPeriodic (fun t => f (t + k)) := by
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
    DrivenColumns.EventuallyPeriodic nonvacDriven_u ∧
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


set_option linter.style.longLine false in
/-- info: 'DrivenColumns.eventuallyPeriodic_of_driven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_of_driven

/-- info: 'DrivenColumns.eventuallyPeriodic_comp' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_comp

/-- info: 'DrivenColumns.eventuallyPeriodic_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_pair

set_option linter.style.longLine false in
/-- info: 'DrivenColumns.eventuallyPeriodic_of_driven_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_of_driven_nonvacuous
