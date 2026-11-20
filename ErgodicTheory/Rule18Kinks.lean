module

public import ErgodicTheory.LocalRuleColumns
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Tactic.Push

/-!
# The kink count of a finitely supported configuration never increases under rule `18`

A *kink* of a configuration over `ZMod 2` is a word `1 0^(2n) 1`: a set cell together with the next
set cell, at odd distance. Sabrié and Törmä (2023, §4), after Kůrka (2003), show that one step of
Wolfram's rule `18` does not create kinks in a word: a word with `n` kinks has an image with at
most `n`. Their proof is read off a discussion and a figure. This module proves the sentence on a
finitely supported configuration of the line, which is their statement at the word padded with two
clear cells on each side, and proves it for every local rule that fixes `000` and `010` at zero and
sends at most one of the neighbourhoods `011` and `110` to one, among them the rules agreeing with
rule `90` on the five neighbourhoods without two adjacent set cells.

## Main results

* `rule18`, `kinkSet`, `kinks` — Wolfram's rule `18` over `ZMod 2`, the set cells of a
  configuration followed at odd distance by the next set cell, and their number;
  `kinkSet_finite` makes the count honest on finitely supported configurations.
* `kinks_step_le` — **the kink count never increases in one step** of a local rule that fixes
  `000` and `010` at zero and does not send both `011` and `110` to one, on a finitely supported
  configuration.
* `kinks_step_le_of_agree` — the same at a rule with the five values of rule `90` on the
  neighbourhoods without two adjacent set cells.
* `kinks_step_rule18_le` — **rule `18` does not create kinks** (Sabrié and Törmä 2023, §4).

The proof pairs each set cell of the image with a set cell of the configuration at distance one,
chosen to be non-decreasing; the pair of images at odd distance then has anchors at odd distance,
between which lies a kink of the configuration, and distinct kinks of the image get distinct kinks
of the configuration.
-/

@[expose] public section

namespace Rule18Kinks

open LocalRuleColumns

/-- Wolfram's rule `18` over `ZMod 2`: the new value is one exactly at the neighbourhoods `001` and
`100`. -/
abbrev rule18 : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 := fun a b c => (a + c) * (1 + b)

/-- **The kinks of a configuration**: the set cells `i` whose next set cell lies at odd distance,
that is, the left ends of the words `1 0^(2n) 1`. -/
def kinkSet (x : ℤ → ZMod 2) : Set ℤ :=
  {i | x i ≠ 0 ∧ ∃ j, i < j ∧ x j ≠ 0 ∧ Odd (j - i) ∧ ∀ m, i < m → m < j → x m = 0}

/-- **The number of kinks** of a configuration. -/
noncomputable def kinks (x : ℤ → ZMod 2) : ℕ := Set.ncard (kinkSet x)

/-- The kinks lie in the support, so a finitely supported configuration has finitely many. -/
theorem kinkSet_finite {x : ℤ → ZMod 2} (hx : (Function.support x).Finite) :
    (kinkSet x).Finite :=
  hx.subset fun _ hi => hi.1

private theorem exists_kink_between (x : ℤ → ZMod 2) :
    ∀ (d : ℕ) (u v : ℤ), (v - u).toNat = d → u < v → x u ≠ 0 → x v ≠ 0 → Odd (v - u) →
      ∃ c ∈ kinkSet x, u ≤ c ∧ c < v := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro u v hd huv hu hv hodd
    by_cases hbetween : ∃ w, u < w ∧ w < v ∧ x w ≠ 0
    · obtain ⟨w, huw, hwv, hw⟩ := hbetween
      rw [Int.odd_iff] at hodd
      by_cases hwu : (w - u) % 2 = 1
      · obtain ⟨c, hc, hc1, hc2⟩ :=
          ih (w - u).toNat (by omega) u w rfl huw hu hw (Int.odd_iff.mpr hwu)
        exact ⟨c, hc, hc1, by omega⟩
      · obtain ⟨c, hc, hc1, hc2⟩ :=
          ih (v - w).toNat (by omega) w v rfl hwv hw hv (Int.odd_iff.mpr (by omega))
        exact ⟨c, hc, by omega, hc2⟩
    · push Not at hbetween
      exact ⟨u, ⟨hu, v, huv, hv, hodd, fun m h1 h2 => hbetween m h1 h2⟩, le_rfl, huv⟩

private theorem kinks_le_of_anchor {x y : ℤ → ZMod 2} (hx : (Function.support x).Finite)
    (a : ℤ → ℤ) (ha₁ : ∀ i, y i ≠ 0 → x (a i) ≠ 0)
    (ha₂ : ∀ i, y i ≠ 0 → a i = i - 1 ∨ a i = i + 1)
    (hmono : ∀ u v, y u ≠ 0 → y v ≠ 0 → u ≤ v → a u ≤ a v) : kinks y ≤ kinks x := by
  have key : ∀ i ∈ kinkSet y, ∃ c ∈ kinkSet x, ∃ j, i < j ∧ y j ≠ 0 ∧
      (∀ m, i < m → m < j → y m = 0) ∧ a i ≤ c ∧ c < a j := by
    rintro i ⟨hi, j, hij, hj, hodd, hbet⟩
    have h1 := ha₁ i hi
    have h2 := ha₁ j hj
    have hm := hmono i j hi hj hij.le
    have hodd2 : (a j - a i) % 2 = 1 := by
      rw [Int.odd_iff] at hodd
      rcases ha₂ i hi with e | e <;> rcases ha₂ j hj with e' | e' <;> omega
    have hlt : a i < a j := by omega
    obtain ⟨c, hc, hc1, hc2⟩ :=
      exists_kink_between x _ (a i) (a j) rfl hlt h1 h2 (Int.odd_iff.mpr hodd2)
    exact ⟨c, hc, j, hij, hj, hbet, hc1, hc2⟩
  choose! g hg using key
  unfold kinks
  refine Set.ncard_le_ncard_of_injOn g (fun i hi => (hg i hi).1) ?_ (kinkSet_finite hx)
  intro i hi k hk hik
  by_contra hne
  obtain ⟨_, j, hij, hj, hbet, hc1, hc2⟩ := hg i hi
  obtain ⟨_, j', hkj, hj', hbet', hd1, hd2⟩ := hg k hk
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hjk : j ≤ k := by
      by_contra h
      exact hk.1 (hbet k hlt (not_le.mp h))
    have := hmono j k hj hk.1 hjk
    omega
  · have hjk : j' ≤ i := by
      by_contra h
      exact hi.1 (hbet' i hgt (not_le.mp h))
    have := hmono j' i hj' hi.1 hjk
    omega

/-- **The kink count never increases in one step** of a local rule `f` over `ZMod 2` on a finitely
supported configuration, for every `f` that fixes `000` and `010` at zero and sends at most one of
the neighbourhoods `011` and `110` to one. This is the statement over the whole class of such rules,
which generalizes Sabrié and Törmä (2023, §4) at rule `18`. -/
theorem kinks_step_le (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (h000 : f 0 0 0 = 0)
    (h010 : f 0 1 0 = 0) (hone : ¬ (f 0 1 1 = 1 ∧ f 1 1 0 = 1)) (x : ℤ → ZMod 2)
    (hx : (Function.support x).Finite) : kinks (step f x) ≤ kinks x := by
  have z2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have z1 : ∀ z : ZMod 2, z ≠ 0 → z = 1 := fun z hz => (z2 z).resolve_left hz
  have hz0 : ∀ b : ZMod 2, f 0 b 0 = 0 := by
    intro b
    rcases z2 b with rfl | rfl <;> assumption
  have hy : ∀ i, step f x i = f (x (i - 1)) (x i) (x (i + 1)) := fun _ => rfl
  by_cases hA : f 0 1 1 = 0
  · -- anchor: the left neighbour when it is set, the right one otherwise
    refine kinks_le_of_anchor hx (fun i => if x (i - 1) ≠ 0 then i - 1 else i + 1) ?_ ?_ ?_
    · intro i hi
      rw [hy] at hi
      split_ifs with hl
      · exact hl
      · intro h0
        have hl' : x (i - 1) = 0 := not_not.mp hl
        rw [hl', h0] at hi
        exact hi (hz0 _)
    · intro i _
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro u v hu hv huv
      rw [hy] at hu hv
      rcases huv.eq_or_lt with rfl | hlt
      · exact le_rfl
      by_cases hv2 : u + 2 ≤ v
      · split_ifs <;> omega
      · have hv1 : v = u + 1 := by omega
        subst hv1
        by_cases h1 : x (u - 1) ≠ 0
        · split_ifs <;> omega
        · by_cases h2 : x (u + 1 - 1) ≠ 0
          · exfalso
            have e1 : x (u - 1) = 0 := not_not.mp h1
            have e2 : x u = 1 := z1 _ (by simpa using h2)
            rw [e1, e2] at hu
            rcases z2 (x (u + 1)) with e3 | e3 <;> rw [e3] at hu
            · exact hu h010
            · exact hu hA
          · split_ifs; omega
  · have hB : f 1 1 0 = 0 := by
      by_contra hB
      exact hone ⟨(z2 _).resolve_left hA, (z2 _).resolve_left hB⟩
    -- anchor: the right neighbour when it is set, the left one otherwise
    refine kinks_le_of_anchor hx (fun i => if x (i + 1) ≠ 0 then i + 1 else i - 1) ?_ ?_ ?_
    · intro i hi
      rw [hy] at hi
      split_ifs with hr
      · exact hr
      · intro h0
        have hr' : x (i + 1) = 0 := not_not.mp hr
        rw [hr', h0] at hi
        exact hi (hz0 _)
    · intro i _
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    · intro u v hu hv huv
      rw [hy] at hu hv
      rcases huv.eq_or_lt with rfl | hlt
      · exact le_rfl
      by_cases hv2 : u + 2 ≤ v
      · split_ifs <;> omega
      · have hv1 : v = u + 1 := by omega
        subst hv1
        by_cases h1 : x (u + 1) ≠ 0
        · by_cases h2 : x (u + 1 + 1) ≠ 0
          · split_ifs; omega
          · exfalso
            have e1 : x (u + 1 + 1) = 0 := not_not.mp h2
            have e2 : x (u + 1) = 1 := z1 _ h1
            rw [e1, e2] at hv
            rcases z2 (x (u + 1 - 1)) with e3 | e3 <;> rw [e3] at hv
            · exact hv h010
            · exact hv hB
        · split_ifs <;> omega

/-- **The kink count never increases in one step** of a local rule `f` over `ZMod 2` on a finitely
supported configuration, when `f` takes the values `0` at `000` and `010`, and sends at most one
of the neighbourhoods `011` and `110` to one. The values `001`, `100` and `101` of rule `90` are
not used by the proof; this is `kinks_step_le` with them as extra hypotheses. -/
theorem kinks_step_le_of_agree (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (h000 : f 0 0 0 = 0)
    (_h001 : f 0 0 1 = 1) (_h100 : f 1 0 0 = 1) (h010 : f 0 1 0 = 0) (_h101 : f 1 0 1 = 0)
    (hone : ¬ (f 0 1 1 = 1 ∧ f 1 1 0 = 1)) (x : ℤ → ZMod 2)
    (hx : (Function.support x).Finite) : kinks (step f x) ≤ kinks x :=
  kinks_step_le f h000 h010 hone x hx

/-- **Rule `18` does not create kinks** (Sabrié and Törmä 2023, §4, after Kůrka 2003): on a
finitely supported configuration of the line, one step of rule `18` leaves at most as many kinks as
the configuration has. Their statement is on words; this is its instance at the word padded with two
clear cells on each side, whose image is the configuration's image on its possible support. -/
theorem kinks_step_rule18_le (x : ℤ → ZMod 2) (hx : (Function.support x).Finite) :
    kinks (step rule18 x) ≤ kinks x :=
  kinks_step_le_of_agree rule18 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) x hx

end Rule18Kinks
