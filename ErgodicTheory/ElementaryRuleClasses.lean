module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# The elementary rules and their classes under reflection and complementation

The elementary rule of Wolfram number `n < 256` is the local rule `ZMod 2 → ZMod 2 → ZMod 2 →
ZMod 2` whose value at `(a, b, c)` is bit `4 a + 2 b + c` of `n` (Wolfram 1983). Reading a rule
right to left, and conjugating it by the exchange of `0` and `1`, are two commuting involutions on
the numbers; their orbits are the classes of Li and Packard (1990).

## Main results

* `elementaryRule`, `reflectNum`, `complementNum` — the rule of a number and the numbers of the
  rule read right to left and of its complement conjugate (`elementaryRule_reflectNum`,
  `elementaryRule_complementNum`); both maps are involutions and commute.
* `card_classes` — **the elementary rules fall into `88` classes** (Li and Packard 1990, §3 and
  appendix), counted as the numbers that are least of their class.
* `card_classes_one`, `card_classes_two`, `card_classes_four` — the classes of sizes one, two and
  four number `8`, `36` and `44`; `sum_classSize` — their sizes add to `256`.
-/

@[expose] public section

namespace ElementaryRuleClasses

/-- **The elementary rule of Wolfram number `n`** (Wolfram 1983): its value at `(a, b, c)` is bit
`4 a + 2 b + c` of `n`. -/
def elementaryRule (n : Fin 256) : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 :=
  fun a b c => if (n : ℕ).testBit (4 * a.val + 2 * b.val + c.val) then 1 else 0

/-- The `0`-or-`1` value of bit `j` of the number `n`. -/
def bitVal (n : Fin 256) (j : ℕ) : ℕ := (n.val.testBit j).toNat

/-- A bit is `0` or `1`. -/
theorem bitVal_le_one (n : Fin 256) (j : ℕ) : bitVal n j ≤ 1 := Bool.toNat_le _

/-- **The number of the rule read right to left**: bit `4 a + 2 b + c` of the result is bit
`4 c + 2 b + a` of `n`, so bits `1 ↔ 4` and `3 ↔ 6` swap. -/
def reflectNum (n : Fin 256) : Fin 256 :=
  ⟨bitVal n 0 + 2 * bitVal n 4 + 4 * bitVal n 2 + 8 * bitVal n 6 + 16 * bitVal n 1
    + 32 * bitVal n 5 + 64 * bitVal n 3 + 128 * bitVal n 7, by
    have := bitVal_le_one n 0; have := bitVal_le_one n 1; have := bitVal_le_one n 2
    have := bitVal_le_one n 3; have := bitVal_le_one n 4; have := bitVal_le_one n 5
    have := bitVal_le_one n 6; have := bitVal_le_one n 7
    omega⟩

/-- **The number of the rule conjugated by exchanging `0` and `1`**: bit `i` of the result is the
complement of bit `7 - i` of `n`. -/
def complementNum (n : Fin 256) : Fin 256 :=
  ⟨(1 - bitVal n 7) + 2 * (1 - bitVal n 6) + 4 * (1 - bitVal n 5) + 8 * (1 - bitVal n 4)
    + 16 * (1 - bitVal n 3) + 32 * (1 - bitVal n 2) + 64 * (1 - bitVal n 1)
    + 128 * (1 - bitVal n 0), by omega⟩

/-- **Reflection**: `reflectNum n` is the rule of `n` read right to left. -/
theorem elementaryRule_reflectNum (n : Fin 256) (a b c : ZMod 2) :
    elementaryRule (reflectNum n) a b c = elementaryRule n c b a := by
  revert n a b c
  decide +kernel

/-- **Complementation**: `complementNum n` is the rule of `n` conjugated by the exchange of `0`
and `1`. -/
theorem elementaryRule_complementNum (n : Fin 256) (a b c : ZMod 2) :
    elementaryRule (complementNum n) a b c = 1 + elementaryRule n (1 + a) (1 + b) (1 + c) := by
  revert n a b c
  decide +kernel

/-- Reflection is an involution. -/
theorem reflectNum_involutive : Function.Involutive reflectNum := by
  intro n
  revert n
  decide +kernel

/-- Complementation is an involution. -/
theorem complementNum_involutive : Function.Involutive complementNum := by
  intro n
  revert n
  decide +kernel

/-- Reflection and complementation commute. -/
theorem reflectNum_complementNum_comm (n : Fin 256) :
    reflectNum (complementNum n) = complementNum (reflectNum n) := by
  revert n
  decide +kernel

/-- A number is the least of its class under reflection, complementation and both. -/
def IsClassLeast (n : Fin 256) : Prop :=
  n ≤ reflectNum n ∧ n ≤ complementNum n ∧ n ≤ reflectNum (complementNum n)

instance (n : Fin 256) : Decidable (IsClassLeast n) := by
  unfold IsClassLeast; infer_instance

/-- The number of members of the class of `n`: its orbit under reflection and complementation. -/
def classSize (n : Fin 256) : ℕ :=
  ({n, reflectNum n, complementNum n, reflectNum (complementNum n)} : Finset (Fin 256)).card

/-- A class has one member exactly when `n` is fixed by both maps. -/
theorem classSize_eq_one_iff (n : Fin 256) :
    classSize n = 1 ↔ reflectNum n = n ∧ complementNum n = n := by
  revert n
  decide +kernel

/-- **The elementary rules fall into `88` classes** under reflection and complementation
(Li and Packard 1990, §3 and appendix), counted as the numbers least of their class. -/
theorem card_classes : (Finset.univ.filter fun n : Fin 256 => IsClassLeast n).card = 88 := by
  decide +kernel

/-- **Eight classes have one member**: the numbers fixed by both maps. -/
theorem card_classes_one :
    (Finset.univ.filter fun n : Fin 256 => IsClassLeast n ∧ classSize n = 1).card = 8 := by
  decide +kernel

/-- **Thirty-six classes have two members** (Li and Packard 1990, appendix). -/
theorem card_classes_two :
    (Finset.univ.filter fun n : Fin 256 => IsClassLeast n ∧ classSize n = 2).card = 36 := by
  decide +kernel

/-- **Forty-four classes have four members** (Li and Packard 1990, appendix). -/
theorem card_classes_four :
    (Finset.univ.filter fun n : Fin 256 => IsClassLeast n ∧ classSize n = 4).card = 44 := by
  decide +kernel

/-- Every class has one, two or four members: the least numbers' class sizes add to `256`. -/
theorem sum_classSize :
    ∑ n ∈ Finset.univ.filter (fun n : Fin 256 => IsClassLeast n), classSize n = 256 := by
  decide +kernel

end ElementaryRuleClasses
