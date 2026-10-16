module

public import ErgodicTheory.LocalRuleColumns
public import ErgodicTheory.ElementaryRuleClasses
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Number conservation of the elementary rules

A local rule on `ZMod 2` conserves the number of ones when it moves them without creating or
destroying any. The setting here is the finitely supported configurations of the line `ℤ → ZMod 2`
acted on by `LocalRuleColumns.step`; `ones x` is the number of cells reading `1`.

A **flux** for a rule `f` is an integer `J a b` for each pair of adjacent cells, zero at the empty
pair, with `f a b c = b + J a b - J b c` over the integers: the cell keeps its own value, gains
what flows in from its left and loses what flows out to its right. The sum over a window then
telescopes to the sum of the values and two boundary fluxes, both `J 0 0`.

## Main results

* `ones_step_of_isFlux` — **a rule with a flux keeps the number of ones** of every finitely
  supported configuration, and the image is finitely supported again;
  `ones_step_of_isFlux_nonvacuous` meets its hypotheses at once.
* `exists_isFlux_of_mem` — the five elementary rules `170`, `184`, `204`, `226` and `240` have a
  flux, `fluxOf` giving it from its three values at `(0, 1)`, `(1, 0)` and `(1, 1)`.
* `conserves_iff` — **among the quiescent elementary rules, exactly the five conserve the number
  of ones**, by the images of the four configurations `1`, `11`, `101` and `111`
  (`ones_step_cfg_one` and its three companions) and a decision over the numbers
  (`counts_iff_mem`). The list is that of Boccara and Fukś (1998), §4, stated there on cyclic
  configurations; the characterization of conservation by a sum of the rule's values is Theorem 2.1
  of Boccara and Fukś (2002), which credits the general theorem on additive conserved quantities to
  Hattori and Takesue (1991), and the flux form used here is equivalent to that sum at three
  inputs. The setting here is the finitely supported configurations of the line.
* `exists_isFlux_iff` — at a quiescent number, a flux exists exactly at the five.
-/

@[expose] public section

namespace NumberConservation

open ElementaryRuleClasses LocalRuleColumns

/-- The number of ones of a configuration; meaningful where the support is finite. -/
noncomputable def ones (x : ℤ → ZMod 2) : ℕ := (Function.support x).ncard

/-- **A flux for a local rule**: an integer `J a b` for each pair of adjacent cells, zero at the
empty pair, with `f a b c = b + J a b - J b c` over the integers. -/
def IsFlux (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (J : ZMod 2 → ZMod 2 → ℤ) : Prop :=
  J 0 0 = 0 ∧ ∀ a b c, ((f a b c).val : ℤ) = (b.val : ℤ) + J a b - J b c

/-- The flux with values `j01`, `j10`, `j11` at `(0, 1)`, `(1, 0)`, `(1, 1)` and `0` at
`(0, 0)`. -/
def fluxOf (j01 j10 j11 : ℤ) : ZMod 2 → ZMod 2 → ℤ := fun a b =>
  if a = 0 then (if b = 0 then 0 else j01) else (if b = 0 then j10 else j11)

/-- A rule with a flux sends `0 0 0` to `0`. -/
theorem map_zero_of_isFlux {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {J : ZMod 2 → ZMod 2 → ℤ}
    (hJ : IsFlux f J) : f 0 0 0 = 0 := by
  have h := hJ.2 0 0 0
  rw [hJ.1] at h
  simp only [ZMod.val_zero, Nat.cast_zero, add_zero, sub_zero] at h
  exact (ZMod.val_eq_zero _).1 (by exact_mod_cast h)

/-- The value in `ℕ` of an element of `ZMod 2` is `1` where it is nonzero, else `0`. -/
theorem val_eq_ite (a : ZMod 2) : a.val = if a ≠ 0 then 1 else 0 := by
  revert a
  decide

/-- On a finset containing the support, the number of ones is the sum of the values. -/
theorem ones_eq_sum (x : ℤ → ZMod 2) (W : Finset ℤ) (h : ∀ i, x i ≠ 0 → i ∈ W) :
    ones x = ∑ i ∈ W, (x i).val := by
  have hs : Function.support x = ↑(W.filter fun i => x i ≠ 0) := by
    ext i
    simp only [Function.mem_support, Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun hi => ⟨h i hi, hi⟩, fun hi => hi.2⟩
  unfold ones
  rw [hs, Set.ncard_coe_finset, Finset.card_filter]
  exact Finset.sum_congr rfl fun i _ => (val_eq_ite (x i)).symm

/-- The cells of the window `-M, …, M`, as the image of a range, for telescoping. -/
private def window (M : ℕ) : Finset ℤ := (Finset.range (2 * M + 1)).image fun k : ℕ => (k : ℤ) - M

private theorem mem_window {M : ℕ} {i : ℤ} (h1 : -(M : ℤ) ≤ i) (h2 : i ≤ M) : i ∈ window M := by
  unfold window
  rw [Finset.mem_image]
  refine ⟨(i + M).toNat, ?_, ?_⟩
  · rw [Finset.mem_range]; omega
  · omega

private theorem sum_window (M : ℕ) (F : ℤ → ℤ) :
    ∑ i ∈ window M, F i = ∑ k ∈ Finset.range (2 * M + 1), F ((k : ℤ) - M) := by
  unfold window
  rw [Finset.sum_image]
  intro a _ b _ hab
  have : (a : ℤ) = b := by simpa using hab
  exact_mod_cast this

private theorem telescope (M : ℕ) (g : ℤ → ℤ) :
    ∑ i ∈ window M, (g i - g (i + 1)) = g (-(M : ℤ)) - g ((M : ℤ) + 1) := by
  rw [sum_window]
  have h := Finset.sum_range_sub' (fun k : ℕ => g ((k : ℤ) - M)) (2 * M + 1)
  have e1 : ∀ k : ℕ, g (((k : ℤ) - M) + 1) = g (((k + 1 : ℕ) : ℤ) - M) := fun k => by
    congr 1; push_cast; ring
  simp only [e1]
  rw [h]
  congr 2 <;> push_cast <;> ring

/-- A configuration with finite support vanishes outside a window `-N, …, N`. -/
private theorem exists_bound (x : ℤ → ZMod 2) (hx : (Function.support x).Finite) :
    ∃ N : ℕ, ∀ i, x i ≠ 0 → -(N : ℤ) ≤ i ∧ i ≤ N := by
  obtain ⟨b, hb⟩ := Set.Finite.bddAbove hx
  obtain ⟨a, ha⟩ := Set.Finite.bddBelow hx
  refine ⟨(max |a| |b|).toNat, fun i hi => ?_⟩
  have h1 := ha (show i ∈ Function.support x from hi)
  have h2 := hb (show i ∈ Function.support x from hi)
  have := abs_nonneg a
  have := abs_nonneg b
  have := neg_abs_le a
  have := le_abs_self b
  have := le_max_left |a| |b|
  have := le_max_right |a| |b|
  omega

/-- **A rule with a flux conserves the number of ones.** -/
theorem ones_step_of_isFlux {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {J : ZMod 2 → ZMod 2 → ℤ}
    (hJ : IsFlux f J) (x : ℤ → ZMod 2) (hx : (Function.support x).Finite) :
    (Function.support (LocalRuleColumns.step f x)).Finite ∧
      ones (LocalRuleColumns.step f x) = ones x := by
  have hq := map_zero_of_isFlux hJ
  obtain ⟨N, hN⟩ := exists_bound x hx
  -- the image vanishes outside the window of radius `N + 1`
  have hstep : ∀ i, LocalRuleColumns.step f x i ≠ 0 →
      -((N + 1 : ℕ) : ℤ) ≤ i ∧ i ≤ ((N + 1 : ℕ) : ℤ) := by
    intro i hi
    by_contra hc
    apply hi
    have e1 : x (i - 1) = 0 := by
      by_contra h; have := hN _ h; push_cast at hc; omega
    have e2 : x i = 0 := by
      by_contra h; have := hN _ h; push_cast at hc; omega
    have e3 : x (i + 1) = 0 := by
      by_contra h; have := hN _ h; push_cast at hc; omega
    simp only [LocalRuleColumns.step, e1, e2, e3]
    exact hq
  refine ⟨?_, ?_⟩
  · refine (Set.finite_Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ)).subset fun i hi => ?_
    exact hstep i hi
  · set M := N + 1 with hM
    have hxM : ∀ i, x i ≠ 0 → i ∈ window M := fun i hi => by
      have := hN i hi
      exact mem_window (by simp only [hM]; push_cast; omega) (by simp only [hM]; push_cast; omega)
    rw [ones_eq_sum _ (window M) fun i hi => mem_window (hstep i hi).1 (hstep i hi).2,
      ones_eq_sum _ (window M) hxM]
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_sum, Nat.cast_sum]
    have hsum : ∀ i, (((LocalRuleColumns.step f x i).val : ℕ) : ℤ) =
        ((x i).val : ℤ) + (J (x (i - 1)) (x i) - J (x i) (x (i + 1))) := fun i => by
      have := hJ.2 (x (i - 1)) (x i) (x (i + 1))
      simp only [LocalRuleColumns.step]
      linarith
    rw [Finset.sum_congr rfl fun i _ => hsum i, Finset.sum_add_distrib]
    have ht := telescope M fun i => J (x (i - 1)) (x i)
    simp only [add_sub_cancel_right] at ht
    rw [ht]
    have b1 : x (-(M : ℤ) - 1) = 0 := by
      by_contra h; have := hN _ h; simp only [hM] at this; push_cast at this; omega
    have b2 : x (-(M : ℤ)) = 0 := by
      by_contra h; have := hN _ h; simp only [hM] at this; push_cast at this; omega
    have b3 : x (M : ℤ) = 0 := by
      by_contra h; have := hN _ h; simp only [hM] at this; push_cast at this; omega
    have b4 : x ((M : ℤ) + 1) = 0 := by
      by_contra h; have := hN _ h; simp only [hM] at this; push_cast at this; omega
    rw [b1, b2, b3, b4, hJ.1]
    simp

/-- The fluxes of the five conserving rules, as `fluxOf` of the values at `(0, 1)`, `(1, 0)` and
`(1, 1)`. -/
theorem isFlux_170 : IsFlux (elementaryRule 170) (fluxOf (-1) 0 (-1)) := by
  unfold IsFlux; decide +kernel

theorem isFlux_184 : IsFlux (elementaryRule 184) (fluxOf 0 1 0) := by
  unfold IsFlux; decide +kernel

theorem isFlux_204 : IsFlux (elementaryRule 204) (fluxOf 0 0 0) := by
  unfold IsFlux; decide +kernel

theorem isFlux_226 : IsFlux (elementaryRule 226) (fluxOf (-1) 0 0) := by
  unfold IsFlux; decide +kernel

theorem isFlux_240 : IsFlux (elementaryRule 240) (fluxOf 0 1 1) := by
  unfold IsFlux; decide +kernel

/-- **`ones_step_of_isFlux` is not vacuous**: rule `170` with its flux on the configuration that
reads `1` at cell `0` and `0` elsewhere meets both hypotheses, and the number of ones is kept. -/
theorem ones_step_of_isFlux_nonvacuous :
    IsFlux (elementaryRule 170) (fluxOf (-1) 0 (-1)) ∧
      (Function.support (Pi.single (0 : ℤ) (1 : ZMod 2))).Finite ∧
        (Function.support (LocalRuleColumns.step (elementaryRule 170)
          (Pi.single (0 : ℤ) (1 : ZMod 2)))).Finite ∧
        ones (LocalRuleColumns.step (elementaryRule 170) (Pi.single (0 : ℤ) (1 : ZMod 2))) =
          ones (Pi.single (0 : ℤ) (1 : ZMod 2)) := by
  have hfin : (Function.support (Pi.single (0 : ℤ) (1 : ZMod 2))).Finite :=
    (Set.finite_singleton (0 : ℤ)).subset fun i hi => by
      by_contra h
      exact hi (Pi.single_eq_of_ne h _)
  obtain ⟨h1, h2⟩ := ones_step_of_isFlux isFlux_170 _ hfin
  exact ⟨isFlux_170, hfin, h1, h2⟩

/-- The five conserving rules have a flux. -/
theorem exists_isFlux_of_mem (n : Fin 256)
    (h : n ∈ ({170, 184, 204, 226, 240} : Finset (Fin 256))) :
    ∃ J, IsFlux (ElementaryRuleClasses.elementaryRule n) J := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, isFlux_170⟩
  · exact ⟨_, isFlux_184⟩
  · exact ⟨_, isFlux_204⟩
  · exact ⟨_, isFlux_226⟩
  · exact ⟨_, isFlux_240⟩

/-- **The configuration reading `1` on a finite set of cells** and `0` elsewhere. -/
def cfg (S : Finset ℤ) : ℤ → ZMod 2 := fun i => if i ∈ S then 1 else 0

/-- The configuration `cfg S` has `S.card` ones. -/
theorem ones_cfg (S : Finset ℤ) : ones (cfg S) = S.card := by
  rw [ones_eq_sum _ S fun i hi => by
    by_contra h; exact hi (by simp [cfg, h])]
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [cfg, hi]
  rfl

/-- At a quiescent rule, the image of `cfg S` for `S` inside `{0, 1, 2}` has its ones among the
cells `-1, …, 3`, and their number is the sum of the values there. -/
theorem ones_step_cfg {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} (hq : f 0 0 0 = 0) (S : Finset ℤ)
    (hS : S ⊆ Finset.Icc 0 2) :
    ones (LocalRuleColumns.step f (cfg S)) =
      ∑ i ∈ ({-1, 0, 1, 2, 3} : Finset ℤ), (f (cfg S (i - 1)) (cfg S i) (cfg S (i + 1))).val := by
  apply ones_eq_sum
  intro i hi
  by_contra hn
  apply hi
  have hz : ∀ j, j ∉ S → cfg S j = 0 := fun j hj => by simp [cfg, hj]
  have hnot : ∀ j, (j < 0 ∨ 2 < j) → j ∉ S := fun j hj hmem => by
    have := Finset.mem_Icc.1 (hS hmem); omega
  have hi' : i < -1 ∨ 3 < i := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn; omega
  simp only [LocalRuleColumns.step]
  rw [hz _ (hnot _ (by omega)), hz _ (hnot _ (by omega)), hz _ (hnot _ (by omega))]
  exact hq

/-- The images of the four configurations `1`, `11`, `101` and `111` at a quiescent rule have
these numbers of ones; each value is read in `ℕ`. -/
theorem ones_step_cfg_one {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} (hq : f 0 0 0 = 0) :
    ones (LocalRuleColumns.step f (cfg {0})) = (f 0 0 1).val + (f 0 1 0).val + (f 1 0 0).val := by
  rw [ones_step_cfg hq {0} (by decide)]
  simp [Finset.sum_insert, cfg, hq]
  omega

theorem ones_step_cfg_two {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} (hq : f 0 0 0 = 0) :
    ones (LocalRuleColumns.step f (cfg {0, 1})) =
      (f 0 0 1).val + (f 0 1 1).val + (f 1 1 0).val + (f 1 0 0).val := by
  rw [ones_step_cfg hq {0, 1} (by decide)]
  simp [Finset.sum_insert, cfg, hq]
  omega

theorem ones_step_cfg_gap {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} (hq : f 0 0 0 = 0) :
    ones (LocalRuleColumns.step f (cfg {0, 2})) =
      (f 0 0 1).val + (f 0 1 0).val + (f 1 0 1).val + (f 0 1 0).val + (f 1 0 0).val := by
  rw [ones_step_cfg hq {0, 2} (by decide)]
  simp [Finset.sum_insert, cfg]
  omega

theorem ones_step_cfg_three {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} (hq : f 0 0 0 = 0) :
    ones (LocalRuleColumns.step f (cfg {0, 1, 2})) =
      (f 0 0 1).val + (f 0 1 1).val + (f 1 1 1).val + (f 1 1 0).val + (f 1 0 0).val := by
  rw [ones_step_cfg hq {0, 1, 2} (by decide)]
  simp [Finset.sum_insert, cfg]
  omega

/-- **The decision over the quiescent numbers**: the four sums equal `1`, `2`, `2` and `3`
exactly at the five numbers. -/
theorem counts_iff_mem (n : Fin 256) (hq : elementaryRule n 0 0 0 = 0) :
    ((elementaryRule n 0 0 1).val + (elementaryRule n 0 1 0).val + (elementaryRule n 1 0 0).val = 1
      ∧ (elementaryRule n 0 0 1).val + (elementaryRule n 0 1 1).val + (elementaryRule n 1 1 0).val
          + (elementaryRule n 1 0 0).val = 2
      ∧ (elementaryRule n 0 0 1).val + (elementaryRule n 0 1 0).val + (elementaryRule n 1 0 1).val
          + (elementaryRule n 0 1 0).val + (elementaryRule n 1 0 0).val = 2
      ∧ (elementaryRule n 0 0 1).val + (elementaryRule n 0 1 1).val + (elementaryRule n 1 1 1).val
          + (elementaryRule n 1 1 0).val + (elementaryRule n 1 0 0).val = 3)
      ↔ n ∈ ({170, 184, 204, 226, 240} : Finset (Fin 256)) := by
  revert n
  decide +kernel

/-- **Among the quiescent elementary rules, exactly five conserve the number of ones**
(Boccara and Fukś 1998). -/
theorem conserves_iff (n : Fin 256) (hq : ElementaryRuleClasses.elementaryRule n 0 0 0 = 0) :
    (∀ x : ℤ → ZMod 2, (Function.support x).Finite →
        ones (LocalRuleColumns.step (ElementaryRuleClasses.elementaryRule n) x) = ones x)
      ↔ n ∈ ({170, 184, 204, 226, 240} : Finset (Fin 256)) := by
  constructor
  · intro h
    refine (counts_iff_mem n hq).1 ?_
    have hfin : ∀ S : Finset ℤ, (Function.support (cfg S)).Finite := fun S =>
      S.finite_toSet.subset fun i hi => by
        by_contra hn
        exact hi (by simp [cfg, show i ∉ S from hn])
    have e1 := h _ (hfin {0})
    have e2 := h _ (hfin {0, 1})
    have e3 := h _ (hfin {0, 2})
    have e4 := h _ (hfin {0, 1, 2})
    rw [ones_step_cfg_one hq, ones_cfg] at e1
    rw [ones_step_cfg_two hq, ones_cfg] at e2
    rw [ones_step_cfg_gap hq, ones_cfg] at e3
    rw [ones_step_cfg_three hq, ones_cfg] at e4
    refine ⟨e1.trans ?_, e2.trans ?_, e3.trans ?_, e4.trans ?_⟩ <;> decide
  · intro hmem x hx
    obtain ⟨J, hJ⟩ := exists_isFlux_of_mem n hmem
    exact (ones_step_of_isFlux hJ x hx).2

/-- **At a quiescent number, a flux exists exactly at the five conserving rules.** -/
theorem exists_isFlux_iff (n : Fin 256) (hq : ElementaryRuleClasses.elementaryRule n 0 0 0 = 0) :
    (∃ J, IsFlux (ElementaryRuleClasses.elementaryRule n) J)
      ↔ n ∈ ({170, 184, 204, 226, 240} : Finset (Fin 256)) := by
  refine ⟨fun ⟨J, hJ⟩ => (conserves_iff n hq).1 fun x hx => (ones_step_of_isFlux hJ x hx).2,
    exists_isFlux_of_mem n⟩

end NumberConservation
