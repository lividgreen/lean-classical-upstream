module

public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Basic
public import Mathlib.Data.Finset.Card

/-!
# The dual Helly lower bound for learners whose hypotheses lie in a class

A learner of the realizable mistake-bound model
(`Cslib.MachineLearning.OnlineLearning.MistakeBound`) is *proper in `H`* here when its hypothesis
after every history that the concept class `C` realizes lies in a class `H`. Such a learner makes
at least `K - 1` mistakes on the sequences `C` realizes, where `K` is the dual Helly number of `C`
relative to `H`: the least `k` such that every set of labelled examples that no member of `H`
agrees with holds at most `k` examples that no member of `C` agrees with. The bound is stated in
Hanneke, Livni and Moran (2021, "Online learning with simple predictors and a combinatorial
characterization of minimax in 0/1 games", COLT, §2 Remark 1; arXiv 2102.01646). The adversary
presents, at each round, an example of an `H`-unrealizable set on which the current hypothesis is
wrong.

## Main definitions

* `DualHelly.HypothesesIn` — the learner's hypothesis after every history `C` realizes lies in `H`.

## Main results

* `DualHelly.exists_mistakes_eq` — over a set `S` of labelled examples that every member of `H`
  gets wrong somewhere in `S`, and every at most `m` of whose examples some concept of `C` fits,
  a learner with hypotheses in `H` makes exactly `m` mistakes on some sequence of `m` examples of
  `S` that `C` realizes. The two hypotheses on `S` together state that the dual Helly number
  exceeds `m`, so this is the `K - 1` bound of the source.
* `DualHelly.le_mistakeBound` — the same bound as an inequality in `ℕ∞` against `mistakeBound`.
* `DualHelly.exists_stream_mistakes_eq` — the case `K = ∞`, where the set of examples is realized
  by one concept `c` of `C`: if no member of `H` is `c`, there is a stream of instances on which
  the learner errs at every round, the examples labelled by `c`.
-/

@[expose] public section

namespace DualHelly

open Cslib.MachineLearning.OnlineLearning.MistakeBound
open Cslib.MachineLearning.PACLearning (ConceptClass)

variable {α : Type*}

/-- The learner's hypothesis after every history `C` realizes lies in `H`. -/
def HypothesesIn (A : OnlineLearner α) (C H : ConceptClass α Bool) : Prop :=
  ∀ h : List (α × Bool), Realizable C h → A h ∈ H

/-- One more round adds one mistake exactly when the learner's prediction after the history is
wrong. -/
theorem mistakes_append_singleton (A : OnlineLearner α) (L : List (α × Bool)) (p : α × Bool) :
    mistakes A (L ++ [p]) = mistakes A L + if A L p.1 = p.2 then 0 else 1 := by
  obtain ⟨x, y⟩ := p
  unfold mistakes
  rw [mistakesFrom_append, mistakesFrom_cons]
  simp

/-- A sequence of at most `m` examples of `S`, every at most `m` of which some concept of `C`
fits, is realizable by `C`. -/
private theorem realizable_of_length_le {C : ConceptClass α Bool} {S : Set (α × Bool)} {m : ℕ}
    (hm : ∀ T : Finset (α × Bool), (T : Set (α × Bool)) ⊆ S → T.card ≤ m →
      ∃ c ∈ C, ∀ p ∈ T, c p.1 = p.2)
    {L : List (α × Bool)} (hL : ∀ p ∈ L, p ∈ S) (hlen : L.length ≤ m) : Realizable C L := by
  classical
  obtain ⟨c, hc, hcT⟩ := hm L.toFinset
    (fun p hp => hL p (List.mem_toFinset.mp (Finset.mem_coe.mp hp)))
    (le_trans (List.toFinset_card_le L) hlen)
  exact realizable_iff.mpr ⟨c, hc, fun p hp => hcT p (List.mem_toFinset.mpr hp)⟩

/-- **The dual Helly lower bound.** Let `S` be a set of labelled examples that every member of `H`
gets wrong somewhere, and every at most `m` of whose examples some concept of `C` fits. A learner
whose hypotheses after the histories `C` realizes lie in `H` makes exactly `m` mistakes on some
sequence of `m` examples of `S` that `C` realizes: at each round the hypothesis lies in `H`, so it
gets some example of `S` wrong, and that example is presented next. -/
theorem exists_mistakes_eq {A : OnlineLearner α} {C H : ConceptClass α Bool}
    (hA : HypothesesIn A C H) {S : Set (α × Bool)}
    (hS : ∀ g ∈ H, ∃ p ∈ S, g p.1 ≠ p.2) {m : ℕ}
    (hm : ∀ T : Finset (α × Bool), (T : Set (α × Bool)) ⊆ S → T.card ≤ m →
      ∃ c ∈ C, ∀ p ∈ T, c p.1 = p.2) :
    ∃ L : List (α × Bool), (∀ p ∈ L, p ∈ S) ∧ L.length = m ∧ Realizable C L ∧
      mistakes A L = m := by
  suffices h : ∀ k ≤ m, ∃ L : List (α × Bool), (∀ p ∈ L, p ∈ S) ∧ L.length = k ∧
      Realizable C L ∧ mistakes A L = k from h m le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨[], by simp, rfl, realizable_of_length_le hm (by simp) (by simp), rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨L, hLS, hlen, hreal, hmis⟩ := ih (by omega)
    obtain ⟨p, hpS, hp⟩ := hS _ (hA L hreal)
    have hLS' : ∀ q ∈ L ++ [p], q ∈ S := by
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hLS q hq
      · rw [List.mem_singleton.mp hq]
        exact hpS
    refine ⟨L ++ [p], hLS', by simp [hlen], realizable_of_length_le hm hLS' (by simp [hlen]; omega),
      ?_⟩
    rw [mistakes_append_singleton, hmis]
    simp [hp]

/-- **The dual Helly lower bound, against the mistake bound.** In the setting of
`DualHelly.exists_mistakes_eq`, the learner's mistake bound on `C` is at least `m`. -/
theorem le_mistakeBound {A : OnlineLearner α} {C H : ConceptClass α Bool}
    (hA : HypothesesIn A C H) {S : Set (α × Bool)}
    (hS : ∀ g ∈ H, ∃ p ∈ S, g p.1 ≠ p.2) {m : ℕ}
    (hm : ∀ T : Finset (α × Bool), (T : Set (α × Bool)) ⊆ S → T.card ≤ m →
      ∃ c ∈ C, ∀ p ∈ T, c p.1 = p.2) :
    (m : ℕ∞) ≤ mistakeBound A C := by
  obtain ⟨L, -, -, hreal, hmis⟩ := exists_mistakes_eq hA hS hm
  rw [← hmis]
  exact mistakes_le_mistakeBound hreal

/-- **The case of an infinite dual Helly number.** A learner whose hypotheses after the histories
`C` realizes lie in `H`, against a concept `c` of `C` that no member of `H` equals, errs at every
round on some stream of instances labelled by `c`: the adversary presents, at each round, an
instance on which the current hypothesis differs from `c`. -/
theorem exists_stream_mistakes_eq {A : OnlineLearner α} {C H : ConceptClass α Bool}
    (hA : HypothesesIn A C H) {c : α → Bool} (hc : c ∈ C)
    (hcH : ∀ g ∈ H, ∃ x, g x ≠ c x) :
    ∃ x : ℕ → α, ∀ n, mistakes A ((List.range n).map fun t => (x t, c (x t))) = n := by
  classical
  have hreal : ∀ L : List (α × Bool), (∀ p ∈ L, p.2 = c p.1) → Realizable C L :=
    fun L hL => realizable_iff.mpr ⟨c, hc, fun p hp => (hL p hp).symm⟩
  obtain ⟨x0, -⟩ := hcH _ (hA [] (hreal [] (by simp)))
  let w : (α → Bool) → α := fun g => if h : ∃ x, g x ≠ c x then h.choose else x0
  have hw : ∀ g ∈ H, g (w g) ≠ c (w g) := by
    intro g hg
    have h : ∃ x, g x ≠ c x := hcH g hg
    simpa only [w, h, dite_true] using h.choose_spec
  let hist : ℕ → List (α × Bool) := fun n =>
    Nat.rec [] (fun _ L => L ++ [(w (A L), c (w (A L)))]) n
  have hsucc : ∀ n, hist (n + 1) = hist n ++ [(w (A (hist n)), c (w (A (hist n))))] :=
    fun _ => rfl
  have hlab : ∀ n, ∀ p ∈ hist n, p.2 = c p.1 := by
    intro n
    induction n with
    | zero => simp [hist]
    | succ n ih =>
      intro p hp
      rw [hsucc] at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ih p hp
      · rw [List.mem_singleton.mp hp]
  have hmis : ∀ n, mistakes A (hist n) = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hne := hw _ (hA _ (hreal _ (hlab n)))
      rw [hsucc, mistakes_append_singleton, ih]
      simp [hne]
  refine ⟨fun n => w (A (hist n)), fun n => ?_⟩
  have hlist : ∀ n, hist n = (List.range n).map fun t => (w (A (hist t)), c (w (A (hist t)))) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [hsucc, List.range_succ, List.map_append, ← ih]; rfl
  rw [← hlist, hmis]

/-- The hypotheses of `DualHelly.exists_mistakes_eq` hold together, at the two-point domain with
`C` all four functions to `Bool`, `H` the two constant functions, `S` the two examples
`(0, true)` and `(1, false)`, `m = 1`, and the learner predicting the constant `true`. -/
theorem exists_mistakes_eq_nonvacuous :
    HypothesesIn (fun _ _ => true : OnlineLearner (Fin 2)) (Set.univ : ConceptClass (Fin 2) Bool)
        ({fun _ => true, fun _ => false} : ConceptClass (Fin 2) Bool) ∧
      (∀ g ∈ ({fun _ => true, fun _ => false} : ConceptClass (Fin 2) Bool),
        ∃ p ∈ ({(0, true), (1, false)} : Set (Fin 2 × Bool)), g p.1 ≠ p.2) ∧
      (∀ T : Finset (Fin 2 × Bool),
        (T : Set (Fin 2 × Bool)) ⊆ ({(0, true), (1, false)} : Set (Fin 2 × Bool)) →
          T.card ≤ 1 → ∃ c ∈ (Set.univ : ConceptClass (Fin 2) Bool), ∀ p ∈ T, c p.1 = p.2) := by
  refine ⟨fun _ _ => by simp, ?_, ?_⟩
  · intro g hg
    rcases hg with rfl | rfl
    · exact ⟨(1, false), by simp, by simp⟩
    · exact ⟨(0, true), by simp, by simp⟩
  · intro T hT _
    refine ⟨fun x => decide (x = 0), Set.mem_univ _, fun p hp => ?_⟩
    rcases hT hp with rfl | rfl <;> decide

/-- The hypotheses of `DualHelly.exists_stream_mistakes_eq` hold together, at the domain
`Fin 2 → Bool` with `C` the two coordinate functions, `H` the first coordinate alone, `c` the
second coordinate, and the learner always predicting the first coordinate. -/
theorem exists_stream_mistakes_eq_nonvacuous :
    HypothesesIn (fun _ v => v 0 : OnlineLearner (Fin 2 → Bool))
        ({fun v => v 0, fun v => v 1} : ConceptClass (Fin 2 → Bool) Bool)
        ({fun v => v 0} : ConceptClass (Fin 2 → Bool) Bool) ∧
      (fun v : Fin 2 → Bool => v 1) ∈
        ({fun v => v 0, fun v => v 1} : ConceptClass (Fin 2 → Bool) Bool) ∧
      ∀ g ∈ ({fun v => v 0} : ConceptClass (Fin 2 → Bool) Bool),
        ∃ x, g x ≠ (fun v : Fin 2 → Bool => v 1) x := by
  refine ⟨fun _ _ => by simp, by simp, ?_⟩
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  exact ⟨fun i => decide (i = 0), by decide⟩

end DualHelly
