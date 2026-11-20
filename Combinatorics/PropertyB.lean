module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Property B: Erdős's count of two-colourings

A family of finite sets has **property B** (Bernstein's, in Erdős's usage) when the points of the
union can be coloured with two colours so that no member is of one colour. Equivalently, some set
`B` meets every member and contains none.

Erdős, P. (1963), On a combinatorial problem, *Nordisk Mat. Tidskr.* 11, 5–10, Theorem 1: a
family of finite sets `A₁, …, A_k` with `|A_i| = x_i ≥ 2` has property B whenever the sum of
`2 ^ (-x_i)` is at most one half. In particular at most `2 ^ (p - 1)` sets of `p` points each,
`p ≥ 2`, always have it.

## Main results

* `PropertyB` — a set `B` meets every member of the indexed family and contains none.
* `PropertyB.of_sum_le` — Erdős (1963, Theorem 1), by counting the colourings of the union.
* `PropertyB.of_card_le_two_pow` — the corollary for at most `2 ^ (p - 1)` sets of at least `p`
  points each.
* `PropertyB.not_three_pairs` and `PropertyB.not_singleton` — the families that show the bound of
  the theorem cannot be raised to three quarters and the hypothesis `2 ≤ |A_i|` cannot be dropped:
  the three pairs of three points, with sum three quarters, and the one-point set.
* `PropertyB.of_sum_le_nonvacuous` and `PropertyB.of_card_le_two_pow_nonvacuous` — a family meeting
  the hypotheses of each theorem at the boundary.
-/

@[expose] public section

/-- **Property B.** A family `A` of finite sets, indexed by `I`, has property B when some set `B`
meets every member and contains none: both colours, `B` and its complement, occur in every
member. -/
def PropertyB {ι α : Type*} (I : Finset ι) (A : ι → Finset α) : Prop :=
  ∃ B : Set α, ∀ i ∈ I, (∃ a ∈ A i, a ∈ B) ∧ ∃ a ∈ A i, a ∉ B

namespace PropertyB

/-- The colourings of `X`, as subsets, that leave `A` of one colour: those containing `A` and
those disjoint from `A`. -/
private def mono {α : Type*} [DecidableEq α] (X A : Finset α) : Finset (Finset α) :=
  X.powerset.filter fun S => A ⊆ S ∨ Disjoint A S

/-- The colourings of `X` that leave `A ⊆ X` of one colour number at most
`2 * 2 ^ (|X| - |A|)`. -/
private theorem card_mono_le {α : Type*} [DecidableEq α] (X A : Finset α) (hA : A ⊆ X) :
    (mono X A).card ≤ 2 * 2 ^ (X.card - A.card) := by
  have hpow : ((X \ A).powerset).card = 2 ^ (X.card - A.card) := by
    rw [Finset.card_powerset, Finset.card_sdiff_of_subset hA]
  have h1 : (X.powerset.filter fun S => Disjoint A S).card ≤ 2 ^ (X.card - A.card) := by
    rw [← hpow]
    refine Finset.card_le_card ?_
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    rw [Finset.mem_powerset]
    intro x hx
    rw [Finset.mem_sdiff]
    exact ⟨hS.1 hx, fun hxA => Finset.disjoint_left.mp hS.2 hxA hx⟩
  have h2 : (X.powerset.filter fun S => A ⊆ S).card ≤ 2 ^ (X.card - A.card) := by
    rw [← hpow]
    refine Finset.card_le_card_of_injOn (fun S => S \ A) ?_ ?_
    · intro S hS
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS
      rw [Finset.mem_coe, Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff hS.1 le_rfl
    · intro S hS T hT hST
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS hT
      have : S \ A ∪ A = T \ A ∪ A := by
        change S \ A = T \ A at hST
        rw [hST]
      rwa [Finset.sdiff_union_of_subset hS.2, Finset.sdiff_union_of_subset hT.2] at this
  unfold mono
  rw [Finset.filter_or]
  calc _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 2 ^ (X.card - A.card) + 2 ^ (X.card - A.card) := Nat.add_le_add h2 h1
    _ = _ := by ring

/-- The colourings of `X` that leave a member of the family of one colour, counted against the
bound on the sum: `∑ |mono X (A i)| ≤ 2 ^ |X|` when `∑ 2 ^ (-|A i|) ≤ 1 / 2`. -/
private theorem sum_card_mono_le {ι α : Type*} [DecidableEq α] (I : Finset ι) (A : ι → Finset α)
    (X : Finset α) (hAX : ∀ i ∈ I, A i ⊆ X)
    (hsum : ∑ i ∈ I, ((1 : ℝ) / 2) ^ (A i).card ≤ 1 / 2) :
    ∑ i ∈ I, (mono X (A i)).card ≤ 2 ^ X.card := by
  have hterm : ∀ i ∈ I,
      ((mono X (A i)).card : ℝ) ≤ 2 * 2 ^ X.card * ((1 : ℝ) / 2) ^ (A i).card := by
    intro i hi
    have hk : (A i).card ≤ X.card := Finset.card_le_card (hAX i hi)
    have h := card_mono_le X (A i) (hAX i hi)
    have h' : ((mono X (A i)).card : ℝ) ≤ 2 * 2 ^ (X.card - (A i).card) := by exact_mod_cast h
    refine h'.trans (le_of_eq ?_)
    obtain ⟨m, hm⟩ : ∃ m, X.card = (A i).card + m := ⟨X.card - (A i).card, by omega⟩
    rw [hm, Nat.add_sub_cancel_left, pow_add]
    have : (2 : ℝ) ^ (A i).card ≠ 0 := by positivity
    rw [one_div_pow]
    have h1 : (2 : ℝ) ^ (A i).card * (1 / 2 ^ (A i).card) = 1 := by
      rw [mul_one_div, div_self this]
    calc 2 * (2 : ℝ) ^ m = 2 * 2 ^ m * ((2 : ℝ) ^ (A i).card * (1 / 2 ^ (A i).card)) := by
          rw [h1, mul_one]
      _ = _ := by ring
  have h1 : (∑ i ∈ I, ((mono X (A i)).card : ℝ)) ≤ 2 ^ X.card := by
    calc _ ≤ ∑ i ∈ I, 2 * (2 : ℝ) ^ X.card * ((1 : ℝ) / 2) ^ (A i).card := Finset.sum_le_sum hterm
      _ = 2 * 2 ^ X.card * ∑ i ∈ I, ((1 : ℝ) / 2) ^ (A i).card := by rw [Finset.mul_sum]
      _ ≤ 2 * 2 ^ X.card * (1 / 2) := by
        apply mul_le_mul_of_nonneg_left hsum
        positivity
      _ = 2 ^ X.card := by ring
  exact_mod_cast h1

/-- **Erdős (1963, Theorem 1).** A family of finite sets of at least two points each, the sum of
`2 ^ (-|A i|)` over which is at most one half, has property B. The proof counts the two-colourings
of the union: the ones leaving `A i` of one colour number at most `2 * 2 ^ (|X| - |A i|)`, so at
most `2 ^ |X|` in all, and the all-false colouring is among them for every member, which makes the
union bound strict once there are two members. -/
theorem of_sum_le {ι α : Type*} (I : Finset ι) (A : ι → Finset α)
    (h2 : ∀ i ∈ I, 2 ≤ (A i).card)
    (hsum : ∑ i ∈ I, ((1 : ℝ) / 2) ^ (A i).card ≤ 1 / 2) : PropertyB I A := by
  classical
  by_cases hI : I.card ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hI with h0 | h1
    · rw [Finset.card_eq_zero] at h0
      subst h0
      exact ⟨∅, by simp⟩
    · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h1
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (h2 j (Finset.mem_singleton_self j))
      refine ⟨{a}, fun i hi => ?_⟩
      rw [Finset.mem_singleton] at hi
      subst hi
      exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, fun h => hab (Set.mem_singleton_iff.mp h).symm⟩⟩
  · by_contra hnot
    set X : Finset α := I.biUnion A with hX
    have hAX : ∀ i ∈ I, A i ⊆ X := fun i hi => Finset.subset_biUnion_of_mem A hi
    have hcover : ∀ S ∈ X.powerset.erase ∅, S ∈ I.biUnion fun i => (mono X (A i)).erase ∅ := by
      intro S hS
      rw [Finset.mem_erase, Finset.mem_powerset] at hS
      by_contra hno
      apply hnot
      refine ⟨(S : Set α), fun i hi => ?_⟩
      have hi' : S ∉ (mono X (A i)).erase ∅ := fun h =>
        hno (Finset.mem_biUnion.mpr ⟨i, hi, h⟩)
      have hm : S ∉ mono X (A i) := fun h => hi' (Finset.mem_erase.mpr ⟨hS.1, h⟩)
      unfold mono at hm
      rw [Finset.mem_filter, not_and, not_or] at hm
      have hm' := hm (Finset.mem_powerset.mpr hS.2)
      refine ⟨?_, ?_⟩
      · obtain ⟨a, ha1, ha2⟩ := Finset.not_disjoint_iff.mp hm'.2
        exact ⟨a, ha1, ha2⟩
      · obtain ⟨a, ha1, ha2⟩ := Finset.not_subset.mp hm'.1
        exact ⟨a, ha1, ha2⟩
    have hempty : ∀ i ∈ I, ∅ ∈ mono X (A i) := fun i _ => by
      unfold mono
      rw [Finset.mem_filter]
      exact ⟨Finset.empty_mem_powerset _, Or.inr (Finset.disjoint_empty_right _)⟩
    have ha : (X.powerset.erase ∅).card + 1 = 2 ^ X.card := by
      rw [Finset.card_erase_add_one (Finset.empty_mem_powerset _), Finset.card_powerset]
    have hb : (X.powerset.erase ∅).card ≤ ∑ i ∈ I, ((mono X (A i)).erase ∅).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have hc : ∑ i ∈ I, ((mono X (A i)).erase ∅).card + I.card =
        ∑ i ∈ I, (mono X (A i)).card := by
      rw [Finset.card_eq_sum_ones I, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i hi => Finset.card_erase_add_one (hempty i hi)
    have hd := sum_card_mono_le I A X hAX hsum
    omega

/-- **At most `2 ^ (p - 1)` sets of at least `p ≥ 2` points have property B** (Erdős 1963,
Theorem 1, and the remark after it): each member weighs at most `2 ^ (-p)`, so the sum is at most
`2 ^ (p - 1) * 2 ^ (-p) = 1 / 2`. -/
theorem of_card_le_two_pow {ι α : Type*} (I : Finset ι) (A : ι → Finset α) (p : ℕ) (hp : 2 ≤ p)
    (hA : ∀ i ∈ I, p ≤ (A i).card) (hI : I.card ≤ 2 ^ (p - 1)) : PropertyB I A := by
  refine of_sum_le I A (fun i hi => hp.trans (hA i hi)) ?_
  have hterm : ∀ i ∈ I, ((1 : ℝ) / 2) ^ (A i).card ≤ ((1 : ℝ) / 2) ^ p := fun i hi =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (hA i hi)
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hI' : (I.card : ℝ) ≤ 2 ^ q := by exact_mod_cast hI
  calc ∑ i ∈ I, ((1 : ℝ) / 2) ^ (A i).card ≤ ∑ _i ∈ I, ((1 : ℝ) / 2) ^ (q + 1) :=
        Finset.sum_le_sum hterm
    _ = I.card * ((1 : ℝ) / 2) ^ (q + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ q * ((1 : ℝ) / 2) ^ (q + 1) :=
        mul_le_mul_of_nonneg_right hI' (by positivity)
    _ = 1 / 2 := by rw [one_div_pow, pow_succ]; field_simp

/-- **The sum bound of Erdős's theorem is met by a family of two pairs.** The pairs `{0, 1}` and
`{0, 2}` of the points of `Fin 3` satisfy both hypotheses of `PropertyB.of_sum_le`, the sum of
`2 ^ (-|A i|)` being exactly one half, and there are at least two members. -/
theorem of_sum_le_nonvacuous :
    ∃ (ι α : Type) (I : Finset ι) (A : ι → Finset α), (∀ i ∈ I, 2 ≤ (A i).card) ∧
      ∑ i ∈ I, ((1 : ℝ) / 2) ^ (A i).card ≤ 1 / 2 ∧ 2 ≤ I.card := by
  have hcard : ∀ i : Fin 2, (({0, i.succ} : Finset (Fin 3))).card = 2 := fun i =>
    Finset.card_pair (Fin.succ_ne_zero i).symm
  refine ⟨Fin 2, Fin 3, Finset.univ, fun i => {0, i.succ}, fun i _ => (hcard i).ge, ?_, ?_⟩
  · simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  · simp

/-- **The corollary is met at its boundary.** The two pairs `{0, 1}` and `{0, 2}` of the points of
`Fin 3` are `2 ^ (p - 1)` sets of `p` points each at `p = 2`. -/
theorem of_card_le_two_pow_nonvacuous :
    ∃ (ι α : Type) (I : Finset ι) (A : ι → Finset α) (p : ℕ), 2 ≤ p ∧
      (∀ i ∈ I, p ≤ (A i).card) ∧ I.card ≤ 2 ^ (p - 1) ∧ I.card = 2 ^ (p - 1) ∧ 2 ≤ I.card := by
  have hcard : ∀ i : Fin 2, (({0, i.succ} : Finset (Fin 3))).card = 2 := fun i =>
    Finset.card_pair (Fin.succ_ne_zero i).symm
  exact ⟨Fin 2, Fin 3, Finset.univ, fun i => {0, i.succ}, 2, le_rfl, fun i _ => (hcard i).ge,
    by simp, by simp, by simp⟩

/-- **The bound of the theorem cannot be raised to three quarters.** The three pairs of the three
points of `Fin 3` have no property B: the sum of `2 ^ (-|A i|)` is three quarters, and every set of
points misses a pair or contains one. -/
theorem not_three_pairs :
    ¬ PropertyB (Finset.univ : Finset (Fin 3)) (fun i => Finset.univ.erase i) := by
  rintro ⟨B, hB⟩
  have h0 := hB 0 (Finset.mem_univ _)
  have h1 := hB 1 (Finset.mem_univ _)
  have h2 := hB 2 (Finset.mem_univ _)
  simp [Fin.exists_fin_succ] at h0 h1 h2
  tauto

/-- **The hypothesis `2 ≤ |A i|` cannot be dropped.** The family of the one set `{0}` over `Fin 1`
has no property B, though the sum of `2 ^ (-|A i|)` is one half: a set meeting `{0}` contains
it. -/
theorem not_singleton :
    ¬ PropertyB (Finset.univ : Finset (Fin 1)) (fun _ => ({0} : Finset (Fin 1))) := by
  rintro ⟨B, hB⟩
  obtain ⟨⟨a, ha, haB⟩, b, hb, hbB⟩ := hB 0 (Finset.mem_univ _)
  rw [Finset.mem_singleton] at ha hb
  subst ha
  subst hb
  exact hbB haB

end PropertyB

end
