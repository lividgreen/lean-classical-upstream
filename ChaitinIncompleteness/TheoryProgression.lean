module

public import Foundation.FirstOrder.Incompleteness.Halting


/-!
# Progressions of theories: appending an unprovable truth at every stage

A **progression of theories** (Turing 1939; Feferman 1962) is built from a **sentence selector**, a
rule that picks, at each theory of the chain, a sentence true in `ℕ` and unprovable in it; the next
theory appends that sentence. This file builds the finite stages of such a progression.

## Main results

* `SentenceSelector` / `progressionTheory` / `selectedSentence` — the progression, parametric in a
  sentence selector: given a rule for picking, at each theory `T` in the chain, a sentence true in
  `ℕ` and unprovable in `T`, it builds the theory that appends it, and the sentence selected at
  every step.
* `selectedSentence_true` / `selectedSentence_unprovable` / `selectedSentence_injective` — the basic
  behavior: every selected sentence is true and unprovable in the theory that precedes it, and
  distinct steps select distinct sentences.
* `progressionTheory_lt_succ` — the progression ascends STRICTLY: each theory is strictly weaker
  than its successor, at any selector.
-/


@[expose] public section

namespace TheoryProgression

open FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-! ## The progression of theories -/

variable {B : ArithmeticTheory}

/-- A sentence selector at base `B`: for every theory carrying its definability data, a sentence,
true in `ℕ` and unprovable in the theory, whenever the theory extends `B` and is true in `ℕ`. -/
structure SentenceSelector (B : ArithmeticTheory) where
  pick : (T : ArithmeticTheory) → T.Δ₁ → Sentence ℒₒᵣ
  true_pick : ∀ (T : ArithmeticTheory) (d : T.Δ₁) [B ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T], ℕ↓[ℒₒᵣ] ⊧ pick T d
  unprovable_pick : ∀ (T : ArithmeticTheory) (d : T.Δ₁) [B ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T], T ⊬ pick T d

variable (sel : SentenceSelector B) (T₀ : ArithmeticTheory) (d₀ : T₀.Δ₁)

/-- The chain, as a theory-plus-its-definability-data pair, by explicit `Nat.rec` (so the defining
equations below hold by `rfl`, not merely propositionally). -/
noncomputable def progressionPair : ℕ → Σ T : ArithmeticTheory, T.Δ₁ :=
  fun n => Nat.rec (motive := fun _ => Σ T : ArithmeticTheory, T.Δ₁) ⟨T₀, d₀⟩
    (fun _ p => ⟨insert (sel.pick p.1 p.2) p.1, by haveI := p.2; infer_instance⟩) n

/-- The theory at stage `n` of the progression built from `sel` starting at `(T₀, d₀)`. -/
noncomputable def progressionTheory (n : ℕ) : ArithmeticTheory := (progressionPair sel T₀ d₀ n).1

/-- The `Δ₁`-definability data of `progressionTheory sel T₀ d₀ n`. -/
@[reducible] noncomputable def progressionDelta1 (n : ℕ) : (progressionTheory sel T₀ d₀ n).Δ₁ :=
  (progressionPair sel T₀ d₀ n).2

/-- The sentence appended at stage `n`: the selector's pick for the theory then current. -/
noncomputable def selectedSentence (n : ℕ) : Sentence ℒₒᵣ :=
    sel.pick (progressionTheory sel T₀ d₀ n) (progressionDelta1 sel T₀ d₀ n)

theorem progressionTheory_zero : progressionTheory sel T₀ d₀ 0 = T₀ := rfl

theorem progressionTheory_succ (n : ℕ) :
    progressionTheory sel T₀ d₀ (n + 1) =
        insert (selectedSentence sel T₀ d₀ n) (progressionTheory sel T₀ d₀ n) := rfl

/-- The stage-`n` theory is exactly the base plus the first `n` selected sentences. -/
theorem progressionTheory_eq_union (n : ℕ) :
    progressionTheory sel T₀ d₀ n = T₀ ∪ {φ | ∃ i < n, φ = selectedSentence sel T₀ d₀ i} := by
  induction n with
  | zero => rw [progressionTheory_zero]; simp
  | succ n ih =>
    rw [progressionTheory_succ, ih]
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

theorem progressionTheory_subset {n m : ℕ} (h : n ≤ m) :
    progressionTheory sel T₀ d₀ n ⊆ progressionTheory sel T₀ d₀ m := by
  rw [progressionTheory_eq_union, progressionTheory_eq_union]
  apply Set.union_subset_union_right
  rintro φ ⟨i, hi, hφ⟩
  exact ⟨i, by omega, hφ⟩

theorem base_le_progressionTheory [B ⪯ T₀] (n : ℕ) : B ⪯ progressionTheory sel T₀ d₀ n := by
  have hsub : T₀ ⊆ progressionTheory sel T₀ d₀ n := by
    rw [progressionTheory_eq_union]; exact Set.subset_union_left
  exact FFL.Entailment.WeakerThan.trans (inferInstance : B ⪯ T₀)
      (FFL.Entailment.Axiomatized.le_of_subset hsub)

theorem selectedSentence_mem_succ (n : ℕ) : selectedSentence sel T₀ d₀ n ∈
    progressionTheory sel T₀ d₀ (n + 1) := by
  rw [progressionTheory_succ]; exact Set.mem_insert _ _

variable [B ⪯ T₀] [ℕ↓[ℒₒᵣ] ⊧* T₀]

/-- The three per-stage facts, proved together: `models_progressionTheory`, `selectedSentence_true`
and `selectedSentence_unprovable` are mutually dependent (stage `n+1`'s model fact needs stage
`n`'s selected-sentence truth, which itself needs stage `n`'s model fact to invoke the selector),
so one induction proves all
three at once; they are restated as separate named theorems below for citation. -/
theorem progression_facts (n : ℕ) :
    (ℕ↓[ℒₒᵣ] ⊧* progressionTheory sel T₀ d₀ n) ∧ (ℕ↓[ℒₒᵣ] ⊧ selectedSentence sel T₀ d₀ n) ∧
      (progressionTheory sel T₀ d₀ n ⊬ selectedSentence sel T₀ d₀ n) := by
  induction n with
  | zero =>
    have : ℕ↓[ℒₒᵣ] ⊧* progressionTheory sel T₀ d₀ 0 := by
        rw [progressionTheory_zero]; infer_instance
    have : B ⪯ progressionTheory sel T₀ d₀ 0 := base_le_progressionTheory sel T₀ d₀ 0
    exact ⟨inferInstance, sel.true_pick _ _, sel.unprovable_pick _ _⟩
  | succ n ih =>
    have : ℕ↓[ℒₒᵣ] ⊧* progressionTheory sel T₀ d₀ (n + 1) := by
      rw [progressionTheory_succ]; simp [ih.1, ih.2.1]
    have : B ⪯ progressionTheory sel T₀ d₀ (n + 1) := base_le_progressionTheory sel T₀ d₀ (n + 1)
    exact ⟨inferInstance, sel.true_pick _ _, sel.unprovable_pick _ _⟩

theorem models_progressionTheory (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧* progressionTheory sel T₀ d₀ n :=
  (progression_facts sel T₀ d₀ n).1

theorem selectedSentence_true (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧ selectedSentence sel T₀ d₀ n :=
  (progression_facts sel T₀ d₀ n).2.1

theorem selectedSentence_unprovable (n : ℕ) : progressionTheory sel T₀ d₀ n ⊬ selectedSentence sel
    T₀ d₀ n :=
  (progression_facts sel T₀ d₀ n).2.2

theorem selectedSentence_injective : Function.Injective (selectedSentence sel T₀ d₀) := by
  intro m n hmn
  rcases lt_trichotomy m n with hlt | heq | hlt
  · exfalso
    have hmem : selectedSentence sel T₀ d₀ m ∈ progressionTheory sel T₀ d₀ n :=
      progressionTheory_subset sel T₀ d₀ (by omega) (selectedSentence_mem_succ sel T₀ d₀ m)
    have hprov : progressionTheory sel T₀ d₀ n ⊢ selectedSentence sel T₀ d₀ n := by
      rw [← hmn]; exact FFL.Entailment.Axiomatized.by_axm hmem
    exact selectedSentence_unprovable sel T₀ d₀ n hprov
  · exact heq
  · exfalso
    have hmem : selectedSentence sel T₀ d₀ n ∈ progressionTheory sel T₀ d₀ m :=
      progressionTheory_subset sel T₀ d₀ (by omega) (selectedSentence_mem_succ sel T₀ d₀ n)
    have hprov : progressionTheory sel T₀ d₀ m ⊢ selectedSentence sel T₀ d₀ m := by
      rw [hmn]; exact FFL.Entailment.Axiomatized.by_axm hmem
    exact selectedSentence_unprovable sel T₀ d₀ m hprov

/-- The progression ascends strictly: each theory is strictly weaker than its successor, which
proves the sentence the earlier theory cannot. -/
theorem progressionTheory_lt_succ (n : ℕ) :
    progressionTheory sel T₀ d₀ n ⪱ progressionTheory sel T₀ d₀ (n + 1) := by
  have : progressionTheory sel T₀ d₀ n ⪯ progressionTheory sel T₀ d₀ (n + 1) :=
    FFL.Entailment.Axiomatized.le_of_subset (progressionTheory_subset sel T₀ d₀ (Nat.le_succ n))
  exact FFL.Entailment.StrictlyWeakerThan.of_unprovable_provable
      (selectedSentence_unprovable sel T₀ d₀ n)
    (FFL.Entailment.Axiomatized.by_axm (selectedSentence_mem_succ sel T₀ d₀ n))

theorem encode_selectedSentence_injective : Function.Injective
    (fun n => Encodable.encode (selectedSentence sel T₀ d₀ n)) := by
  intro m n hmn
  exact selectedSentence_injective sel T₀ d₀ (Encodable.encode_injective hmn)

end TheoryProgression
