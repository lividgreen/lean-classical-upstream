module

public import ErgodicTheory.Rule18Kinks
import all ErgodicTheory.Rule18Kinks
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Push

/-!
# The parity of the kinks of rule `18`, and Jen's kink annihilation

A *kink* of a configuration over `ZMod 2` is a word `1 0^(2n) 1`
(`Rule18Kinks.kinkSet`). Sabrié and Törmä (2023, §4) state, crediting Jen (1990), that a
configuration with finitely many `1`s has, after some number of steps of Wolfram's rule `18`, at
most one kink. This module proves the two elementary facts that turn that statement into the
statement that the kinks vanish, and states Jen's theorem as a named proposition, proved in
`Rule18Lift.lean` (`Rule18Kinks.jenAnnihilation`).

## Main results

* `kinks_mod_two_of_extremes` — **the kinks of a finitely supported configuration are congruent
  to the distance between the first and the last set cell**, modulo two: the gaps between
  consecutive set cells sum to that distance, and a gap is a kink exactly when it is odd.
* `kinks_step_rule18_mod_two` — **the parity of the kinks is kept by rule `18`** on a finitely
  supported configuration: the image of a nonzero configuration has its first set cell one to the
  left and its last one to the right.
* `even_sub_of_kinks_eq_zero` — **a configuration with no kink is of one parity**: its set cells
  differ by even amounts.
* `JenAnnihilation` — **Jen's kink annihilation** (Jen 1990, as Sabrié and Törmä 2023 state it):
  a finitely supported configuration has, after some number of steps of rule `18`, at most one
  kink. Stated here, proved in `Rule18Lift.lean`.

With the parity of the kinks kept, a finitely supported configuration with an even number of kinks
has none after the steps Jen's theorem names, and is then of one parity.
-/

@[expose] public section

namespace Rule18Kinks

open LocalRuleColumns

open private exists_kink_between from ErgodicTheory.Rule18Kinks

/-! ## The kinks and the first and last set cells -/

private theorem kinks_mod_two_aux (S : Finset ℤ) :
    ∀ x : ℤ → ZMod 2, (∀ i, x i ≠ 0 ↔ i ∈ S) → ∀ a b : ℤ, a ∈ S → b ∈ S →
      (∀ i ∈ S, a ≤ i ∧ i ≤ b) → (kinks x : ℤ) % 2 = (b - a) % 2 := by
  induction S using Finset.induction_on_max with
  | empty =>
    intro x _ a b ha
    simp at ha
  | insert c s hlt ih =>
    intro x hx a b ha hb hab
    have hcb : c ≤ b := (hab c (Finset.mem_insert_self c s)).2
    have hbc : b = c := by
      rcases Finset.mem_insert.mp hb with h | h
      · exact h
      · have := hlt b h
        omega
    subst hbc
    have hxc : x b ≠ 0 := (hx b).2 (Finset.mem_insert_self b s)
    by_cases hne : s.Nonempty
    · -- the last cell `c` is added to a nonempty `s`
      set b' := s.max' hne with hb'def
      have hb's : b' ∈ s := Finset.max'_mem s hne
      have hb'lt : b' < b := hlt b' hb's
      have has : a ∈ s := by
        rcases Finset.mem_insert.mp ha with h | h
        · exfalso
          have := (hab b' (Finset.mem_insert_of_mem hb's)).1
          omega
        · exact h
      let x' : ℤ → ZMod 2 := fun i => if i = b then 0 else x i
      have hx'c : x' b = 0 := by simp [x']
      have hx'ne : ∀ i, i ≠ b → x' i = x i := fun i hi => by simp [x', hi]
      have hx's : ∀ i, x' i ≠ 0 ↔ i ∈ s := by
        intro i
        by_cases hi : i = b
        · subst hi
          have : i ∉ s := fun h => lt_irrefl _ (hlt i h)
          simp [hx'c, this]
        · rw [hx'ne i hi, hx i, Finset.mem_insert]
          simp [hi]
      have hih := ih x' hx's a b' has hb's fun i hi =>
        ⟨(hab i (Finset.mem_insert_of_mem hi)).1, Finset.le_max' s i hi⟩
      have hk : ∀ i, i ∈ kinkSet x ↔ i ∈ kinkSet x' ∨ (i = b' ∧ Odd (b - b')) := by
        intro i
        constructor
        · rintro ⟨hi, j, hij, hj, hodd, hbet⟩
          have hi' : i ∈ insert b s := (hx i).1 hi
          have hj' : j ∈ insert b s := (hx j).1 hj
          rcases Finset.mem_insert.mp hj' with rfl | hjs
          · have hib : i ≠ j := hij.ne
            have his : i ∈ s := (Finset.mem_insert.mp hi').resolve_left hib
            have hile : i ≤ b' := Finset.le_max' s i his
            have : i = b' := by
              by_contra hcon
              have hlt' : i < b' := lt_of_le_of_ne hile hcon
              exact ((hx b').2 (Finset.mem_insert_of_mem hb's)) (hbet b' hlt' hb'lt)
            exact Or.inr ⟨this, this ▸ hodd⟩
          · have hjb : j < b := hlt j hjs
            refine Or.inl ⟨?_, j, hij, ?_, hodd, fun m hm1 hm2 => ?_⟩
            · rw [hx'ne i (by omega)]
              exact hi
            · rw [hx'ne j (by omega)]
              exact hj
            · rw [hx'ne m (by omega)]
              exact hbet m hm1 hm2
        · rintro (⟨hi, j, hij, hj, hodd, hbet⟩ | ⟨hib', hodd⟩)
          · have his : i ∈ s := (hx's i).1 hi
            have hjs : j ∈ s := (hx's j).1 hj
            have hib : i < b := hlt i his
            have hjb : j < b := hlt j hjs
            refine ⟨?_, j, hij, ?_, hodd, fun m hm1 hm2 => ?_⟩
            · rw [← hx'ne i (by omega)]
              exact hi
            · rw [← hx'ne j (by omega)]
              exact hj
            · rw [← hx'ne m (by omega)]
              exact hbet m hm1 hm2
          · rw [hib']
            refine ⟨(hx b').2 (Finset.mem_insert_of_mem hb's), b, hb'lt, hxc, hodd, ?_⟩
            intro m hm1 hm2
            by_contra hm
            have hms : m ∈ s := by
              rcases Finset.mem_insert.mp ((hx m).1 hm) with h | h
              · omega
              · exact h
            have := Finset.le_max' s m hms
            omega
      have hfin' : (Function.support x').Finite :=
        s.finite_toSet.subset fun i hi => (hx's i).1 hi
      have hnot : b' ∉ kinkSet x' := by
        rintro ⟨_, j, hij, hj, _, _⟩
        have := Finset.le_max' s j ((hx's j).1 hj)
        omega
      by_cases hodd : Odd (b - b')
      · have hset : kinkSet x = insert b' (kinkSet x') := by
          ext i
          rw [hk i, Set.mem_insert_iff]
          constructor
          · rintro (h | ⟨h, _⟩)
            · exact Or.inr h
            · exact Or.inl h
          · rintro (h | h)
            · exact Or.inr ⟨h, hodd⟩
            · exact Or.inl h
        have hcard : kinks x = kinks x' + 1 := by
          unfold kinks
          rw [hset, Set.ncard_insert_of_notMem hnot (kinkSet_finite hfin')]
        rw [Int.odd_iff] at hodd
        rw [hcard]
        push_cast
        omega
      · have hset : kinkSet x = kinkSet x' := by
          ext i
          rw [hk i]
          constructor
          · rintro (h | ⟨_, h⟩)
            · exact h
            · exact absurd h hodd
          · exact Or.inl
        have hcard : kinks x = kinks x' := by
          unfold kinks
          rw [hset]
        rw [Int.not_odd_iff] at hodd
        rw [hcard]
        omega
    · -- `s` is empty: the configuration has the single set cell `c`
      have hs : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst hs
      have ha' : a = b := by
        rcases Finset.mem_insert.mp ha with h | h
        · exact h
        · simp at h
      subst ha'
      have hk0 : kinkSet x = ∅ := by
        ext i
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨hi, j, hij, hj, _, _⟩
        have h1 := (hx i).1 hi
        have h2 := (hx j).1 hj
        simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at h1 h2
        omega
      have : kinks x = 0 := by
        unfold kinks
        rw [hk0]
        simp
      rw [this]
      simp

/-- **The kinks and the extremes**: for a finitely supported configuration whose first set cell is
`a` and last set cell is `b`, the number of kinks is congruent to `b - a` modulo two. -/
theorem kinks_mod_two_of_extremes (x : ℤ → ZMod 2) (hx : (Function.support x).Finite)
    (a b : ℤ) (ha : x a ≠ 0) (hb : x b ≠ 0) (hlo : ∀ i, x i ≠ 0 → a ≤ i)
    (hhi : ∀ i, x i ≠ 0 → i ≤ b) : (kinks x : ℤ) % 2 = (b - a) % 2 :=
  kinks_mod_two_aux hx.toFinset x (fun i => by simp) a b (by simpa using ha) (by simpa using hb)
    fun i hi => ⟨hlo i (by simpa using hi), hhi i (by simpa using hi)⟩

/-! ## The parity of the kinks under rule `18` -/

private theorem z2_eq_one (z : ZMod 2) (h : z ≠ 0) : z = 1 := by
  revert z; decide

/-- **The parity of the kinks is kept by rule `18`** on a finitely supported configuration. -/
theorem kinks_step_rule18_mod_two (x : ℤ → ZMod 2) (hx : (Function.support x).Finite) :
    kinks (step rule18 x) % 2 = kinks x % 2 := by
  by_cases hx0 : ∀ i, x i = 0
  · have : step rule18 x = x := by
      funext i
      simp [step, hx0, rule18]
    rw [this]
  · push Not at hx0
    have hne : hx.toFinset.Nonempty := by
      obtain ⟨i, hi⟩ := hx0
      exact ⟨i, by simpa using hi⟩
    set a := hx.toFinset.min' hne with ha
    set b := hx.toFinset.max' hne with hb
    have hamem : x a ≠ 0 := by simpa using Finset.min'_mem hx.toFinset hne
    have hbmem : x b ≠ 0 := by simpa using Finset.max'_mem hx.toFinset hne
    have hlo : ∀ i, x i ≠ 0 → a ≤ i := fun i hi =>
      Finset.min'_le _ _ (by simpa using hi)
    have hhi : ∀ i, x i ≠ 0 → i ≤ b := fun i hi =>
      Finset.le_max' _ _ (by simpa using hi)
    have hxa : x a = 1 := z2_eq_one _ hamem
    have hxb : x b = 1 := z2_eq_one _ hbmem
    have hz : ∀ i, (i < a ∨ b < i) → x i = 0 := by
      intro i hi
      by_contra h
      have h1 := hlo i h
      have h2 := hhi i h
      omega
    have hy : ∀ i, step rule18 x i = (x (i - 1) + x (i + 1)) * (1 + x i) := fun _ => rfl
    have hylo : ∀ i, step rule18 x i ≠ 0 → a - 1 ≤ i := by
      intro i hi
      by_contra h
      apply hi
      rw [hy, hz (i - 1) (by omega), hz (i + 1) (by omega), hz i (by omega)]
      decide
    have hyhi : ∀ i, step rule18 x i ≠ 0 → i ≤ b + 1 := by
      intro i hi
      by_contra h
      apply hi
      rw [hy, hz (i - 1) (by omega), hz (i + 1) (by omega), hz i (by omega)]
      decide
    have hyfin : (Function.support (step rule18 x)).Finite :=
      (Finset.Icc (a - 1) (b + 1)).finite_toSet.subset fun i hi =>
        Finset.mem_Icc.mpr ⟨hylo i hi, hyhi i hi⟩
    have hya : step rule18 x (a - 1) ≠ 0 := by
      rw [hy, hz (a - 1 - 1) (by omega), hz (a - 1) (by omega),
        show a - 1 + 1 = a by ring, hxa]
      decide
    have hyb : step rule18 x (b + 1) ≠ 0 := by
      rw [hy, hz (b + 1 + 1) (by omega), hz (b + 1) (by omega),
        show b + 1 - 1 = b by ring, hxb]
      decide
    have h1 := kinks_mod_two_of_extremes x hx a b hamem hbmem hlo hhi
    have h2 := kinks_mod_two_of_extremes (step rule18 x) hyfin (a - 1) (b + 1) hya hyb hylo hyhi
    omega

/-! ## A configuration without kinks -/

/-- **A configuration with no kink is of one parity**: its set cells differ by even amounts. -/
theorem even_sub_of_kinks_eq_zero (x : ℤ → ZMod 2) (hx : (Function.support x).Finite)
    (h0 : kinks x = 0) (i j : ℤ) (hi : x i ≠ 0) (hj : x j ≠ 0) : Even (i - j) := by
  have hempty : kinkSet x = ∅ := (Set.ncard_eq_zero (kinkSet_finite hx)).1 h0
  have key : ∀ u v : ℤ, u < v → x u ≠ 0 → x v ≠ 0 → Even (v - u) := by
    intro u v huv hu hv
    by_contra hne
    obtain ⟨c, hc, _⟩ :=
      exists_kink_between x _ u v rfl huv hu hv (Int.not_even_iff_odd.mp hne)
    rw [hempty] at hc
    exact hc
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · have := key i j hlt hi hj
    rw [Int.even_iff] at this ⊢
    omega
  · simp
  · exact key j i hgt hj hi

/-! ## Jen's kink annihilation -/

/-- **Jen's kink annihilation** (Jen 1990, as Sabrié and Törmä 2023 state it): a finitely
supported configuration has, after some number of steps of rule `18`, at most one kink. Stated
here and proved in `Rule18Lift.lean` (`Rule18Kinks.jenAnnihilation`). -/
def JenAnnihilation : Prop :=
  ∀ x : ℤ → ZMod 2, (Function.support x).Finite → ∃ n, kinks ((step rule18)^[n] x) ≤ 1

end Rule18Kinks
