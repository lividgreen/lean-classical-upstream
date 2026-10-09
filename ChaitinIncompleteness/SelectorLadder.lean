/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Foundation.FirstOrder.Incompleteness.Halting

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The rung-chain builder: appending an unprovable truth at every stage ([Inevitability] §6)

Provenance: [Inevitability] §6 Proposition 6.16 — the chain builder underlying the corpus's
reflection ladders. A chain of arithmetic theories is built from a **rung selector**, a rule that
picks, at each theory of the chain, a sentence true in `ℕ` and unprovable in it; the next theory
appends that sentence.

## Main results

* `RungSelector` / `ladderTheory` / `rung` — a chain builder, parametric in a rung selector:
  given a rule for picking, at each theory `T` in the chain, a sentence true in `ℕ` and unprovable
  in `T`, builds the theory that appends it, and the rung sentence itself, at every stage.
* `rung_true` / `rung_unprovable` / `rung_injective` — the chain's basic behavior: every rung is
  true and unprovable in the theory that precedes it, and distinct rungs are distinct sentences.
* `ladderTheory_lt_succ` — the chain ascends STRICTLY: each theory is strictly weaker than its
  successor, at any selector.
-/


@[expose] public section

namespace DeepLadder

open FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-! ## The chain builder -/

variable {B : ArithmeticTheory}

/-- A rung selector at base `B`: for every theory carrying its definability data, a sentence, true
in `ℕ` and unprovable in the theory, whenever the theory extends `B` and is true in `ℕ`. -/
structure RungSelector (B : ArithmeticTheory) where
  pick : (T : ArithmeticTheory) → T.Δ₁ → Sentence ℒₒᵣ
  true_pick : ∀ (T : ArithmeticTheory) (d : T.Δ₁) [B ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T], ℕ↓[ℒₒᵣ] ⊧ pick T d
  unprovable_pick : ∀ (T : ArithmeticTheory) (d : T.Δ₁) [B ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T], T ⊬ pick T d

variable (sel : RungSelector B) (T₀ : ArithmeticTheory) (d₀ : T₀.Δ₁)

/-- The chain, as a theory-plus-its-definability-data pair, by explicit `Nat.rec` (so the defining
equations below hold by `rfl`, not merely propositionally). -/
noncomputable def ladderPair : ℕ → Σ T : ArithmeticTheory, T.Δ₁ :=
  fun n => Nat.rec (motive := fun _ => Σ T : ArithmeticTheory, T.Δ₁) ⟨T₀, d₀⟩
    (fun _ p => ⟨insert (sel.pick p.1 p.2) p.1, by haveI := p.2; infer_instance⟩) n

/-- The theory at stage `n` of the ladder built from `sel` starting at `(T₀, d₀)`. -/
noncomputable def ladderTheory (n : ℕ) : ArithmeticTheory := (ladderPair sel T₀ d₀ n).1

/-- The `Δ₁`-definability data of `ladderTheory sel T₀ d₀ n`. -/
@[reducible] noncomputable def ladderDelta1 (n : ℕ) : (ladderTheory sel T₀ d₀ n).Δ₁ :=
  (ladderPair sel T₀ d₀ n).2

/-- The sentence appended at stage `n`: the selector's pick for the theory then current. -/
noncomputable def rung (n : ℕ) : Sentence ℒₒᵣ := sel.pick (ladderTheory sel T₀ d₀ n) (ladderDelta1 sel T₀ d₀ n)

theorem ladderTheory_zero : ladderTheory sel T₀ d₀ 0 = T₀ := rfl

theorem ladderTheory_succ (n : ℕ) :
    ladderTheory sel T₀ d₀ (n + 1) = insert (rung sel T₀ d₀ n) (ladderTheory sel T₀ d₀ n) := rfl

/-- The stage-`n` theory is exactly the base plus the first `n` rungs. -/
theorem ladderTheory_eq_union (n : ℕ) :
    ladderTheory sel T₀ d₀ n = T₀ ∪ {φ | ∃ i < n, φ = rung sel T₀ d₀ i} := by
  induction n with
  | zero => rw [ladderTheory_zero]; simp
  | succ n ih =>
    rw [ladderTheory_succ, ih]
    ext φ
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h | ⟨i, hi, hφ⟩)
      · exact Or.inr ⟨n, by omega, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, by omega, hφ⟩
    · rintro (h | ⟨i, hi, hφ⟩)
      · exact Or.inr (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
        · exact Or.inr (Or.inr ⟨i, hi', hφ⟩)
        · subst hi'; exact Or.inl hφ

theorem ladderTheory_subset {n m : ℕ} (h : n ≤ m) :
    ladderTheory sel T₀ d₀ n ⊆ ladderTheory sel T₀ d₀ m := by
  rw [ladderTheory_eq_union, ladderTheory_eq_union]
  apply Set.union_subset_union_right
  rintro φ ⟨i, hi, hφ⟩
  exact ⟨i, by omega, hφ⟩

theorem base_le_ladderTheory [B ⪯ T₀] (n : ℕ) : B ⪯ ladderTheory sel T₀ d₀ n := by
  have hsub : T₀ ⊆ ladderTheory sel T₀ d₀ n := by
    rw [ladderTheory_eq_union]; exact Set.subset_union_left
  exact FFL.Entailment.WeakerThan.trans (inferInstance : B ⪯ T₀) (FFL.Entailment.Axiomatized.le_of_subset hsub)

theorem rung_mem_succ (n : ℕ) : rung sel T₀ d₀ n ∈ ladderTheory sel T₀ d₀ (n + 1) := by
  rw [ladderTheory_succ]; exact Set.mem_insert _ _

variable [B ⪯ T₀] [ℕ↓[ℒₒᵣ] ⊧* T₀]

/-- The three per-stage facts, proved together: `models_ladderTheory`, `rung_true` and
`rung_unprovable` are mutually dependent (stage `n+1`'s model fact needs stage `n`'s rung-truth,
which itself needs stage `n`'s model fact to invoke the selector), so one induction proves all
three at once; they are restated as separate named theorems below for citation. -/
theorem ladder_facts (n : ℕ) :
    (ℕ↓[ℒₒᵣ] ⊧* ladderTheory sel T₀ d₀ n) ∧ (ℕ↓[ℒₒᵣ] ⊧ rung sel T₀ d₀ n) ∧
      (ladderTheory sel T₀ d₀ n ⊬ rung sel T₀ d₀ n) := by
  induction n with
  | zero =>
    have : ℕ↓[ℒₒᵣ] ⊧* ladderTheory sel T₀ d₀ 0 := by rw [ladderTheory_zero]; infer_instance
    have : B ⪯ ladderTheory sel T₀ d₀ 0 := base_le_ladderTheory sel T₀ d₀ 0
    exact ⟨inferInstance, sel.true_pick _ _, sel.unprovable_pick _ _⟩
  | succ n ih =>
    have : ℕ↓[ℒₒᵣ] ⊧* ladderTheory sel T₀ d₀ (n + 1) := by
      rw [ladderTheory_succ]; simp [ih.1, ih.2.1]
    have : B ⪯ ladderTheory sel T₀ d₀ (n + 1) := base_le_ladderTheory sel T₀ d₀ (n + 1)
    exact ⟨inferInstance, sel.true_pick _ _, sel.unprovable_pick _ _⟩

theorem models_ladderTheory (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧* ladderTheory sel T₀ d₀ n :=
  (ladder_facts sel T₀ d₀ n).1

theorem rung_true (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧ rung sel T₀ d₀ n :=
  (ladder_facts sel T₀ d₀ n).2.1

theorem rung_unprovable (n : ℕ) : ladderTheory sel T₀ d₀ n ⊬ rung sel T₀ d₀ n :=
  (ladder_facts sel T₀ d₀ n).2.2

theorem rung_injective : Function.Injective (rung sel T₀ d₀) := by
  intro m n hmn
  rcases lt_trichotomy m n with hlt | heq | hlt
  · exfalso
    have hmem : rung sel T₀ d₀ m ∈ ladderTheory sel T₀ d₀ n :=
      ladderTheory_subset sel T₀ d₀ (by omega) (rung_mem_succ sel T₀ d₀ m)
    have hprov : ladderTheory sel T₀ d₀ n ⊢ rung sel T₀ d₀ n := by
      rw [← hmn]; exact FFL.Entailment.Axiomatized.by_axm hmem
    exact rung_unprovable sel T₀ d₀ n hprov
  · exact heq
  · exfalso
    have hmem : rung sel T₀ d₀ n ∈ ladderTheory sel T₀ d₀ m :=
      ladderTheory_subset sel T₀ d₀ (by omega) (rung_mem_succ sel T₀ d₀ n)
    have hprov : ladderTheory sel T₀ d₀ m ⊢ rung sel T₀ d₀ m := by
      rw [hmn]; exact FFL.Entailment.Axiomatized.by_axm hmem
    exact rung_unprovable sel T₀ d₀ m hprov

/-- The ladder ascends strictly: each theory is strictly weaker than its successor, which proves
the rung the earlier theory cannot ([Inevitability] §6 Proposition 6.16). -/
theorem ladderTheory_lt_succ (n : ℕ) :
    ladderTheory sel T₀ d₀ n ⪱ ladderTheory sel T₀ d₀ (n + 1) := by
  have : ladderTheory sel T₀ d₀ n ⪯ ladderTheory sel T₀ d₀ (n + 1) :=
    FFL.Entailment.Axiomatized.le_of_subset (ladderTheory_subset sel T₀ d₀ (Nat.le_succ n))
  exact FFL.Entailment.StrictlyWeakerThan.of_unprovable_provable (rung_unprovable sel T₀ d₀ n)
    (FFL.Entailment.Axiomatized.by_axm (rung_mem_succ sel T₀ d₀ n))

theorem encode_rung_injective : Function.Injective (fun n => Encodable.encode (rung sel T₀ d₀ n)) := by
  intro m n hmn
  exact rung_injective sel T₀ d₀ (Encodable.encode_injective hmn)

end DeepLadder
