module

public import Mathlib.Computability.Primrec.List

/-!
# Bit-strings as naturals, and their primitive recursiveness

The bijection between bit-strings and natural numbers, and the computability of the layer built on
it.

## What this establishes

* `bitsToNat`, `natToBits`: a bit-string/natural bijection, `[] ↦ 0`.
* `natToBits`, `bitsToNat` are `Primrec`: a fuel-bounded reformulation of `natToBits` fitting
  `Primrec.nat_iterate`, bridged to the well-founded definition by `natToBitsFuel_eq`.
* The prefix relation on bit-strings is a `PrimrecRel` (`primrec_isPrefix`), and so is list
  membership (`primrec_mem_list`).

## What this does NOT establish (flagged)

* The bijection's two inverse laws and its length law live with the prefix machine in
  `AIT/PrefixMachine.lean`, which imports this module.
-/


@[expose] public section

namespace PrefixMachine

/-! ## A bit-string / natural bijection -/

/-- Bit-strings as naturals, most-significant-bit first: the number whose binary digits are
`1 :: p`, less one. `[] ↦ 0`. -/
def bitsToNat (p : List Bool) : ℕ :=
  p.foldl (fun acc b => 2 * acc + b.toNat) 1 - 1

/-- The inverse of `bitsToNat`: the bits of `n + 1`, most-significant-bit first, with the leading
`1` dropped. Well-founded recursion, peeling the low bit at each step. -/
def natToBits (n : ℕ) : List Bool :=
  if _ : n + 1 < 2 then []
  else natToBits ((n + 1) / 2 - 1) ++ [decide ((n + 1) % 2 = 1)]
termination_by n
decreasing_by omega

theorem natToBits_zero : natToBits 0 = [] := by
  rw [natToBits]; simp

/-! ## `natToBits`, `bitsToNat` are primitive recursive -/

/-- One step of peeling `natToBits`'s low bit: idle once the state has bottomed out at `0`,
otherwise move to the smaller state and cons the peeled bit onto the accumulator. -/
def natToBitsStep (st : ℕ × List Bool) : ℕ × List Bool :=
  if st.1 + 1 < 2 then st else ((st.1 + 1) / 2 - 1, decide ((st.1 + 1) % 2 = 1) :: st.2)

/-- `natToBits` by fuel: peel the low bit of `m + 1` and cons it, `fuel` times, over the state
`(m, acc)` starting at `(n, [])`. -/
def natToBitsFuel (fuel n : ℕ) : List Bool :=
  (natToBitsStep^[fuel] (n, [])).2

/-- Once the state has bottomed out at `0`, every further step is idle. -/
private theorem natToBitsStep_idle_zero (acc : List Bool) :
    ∀ fuel : ℕ, natToBitsStep^[fuel] (0, acc) = (0, acc)
  | 0 => rfl
  | fuel + 1 => by
      rw [Function.iterate_succ_apply', natToBitsStep_idle_zero acc fuel]
      simp [natToBitsStep]

/-- With any starting accumulator, and fuel exceeding the state, peeling reaches `0` and the
accumulator gains exactly `natToBits` of the starting state, prepended. -/
private theorem natToBitsStep_iterate_acc (n fuel : ℕ) (acc : List Bool) (h : n < fuel) :
    natToBitsStep^[fuel] (n, acc) = (0, natToBits n ++ acc) := by
  induction n using natToBits.induct generalizing fuel acc with
  | case1 n hn =>
      have hn0 : n = 0 := by omega
      subst hn0
      rw [natToBits_zero, List.nil_append]
      exact natToBitsStep_idle_zero acc fuel
  | case2 n hn ih =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
      rw [Function.iterate_succ_apply]
      have hstep : natToBitsStep (n, acc)
          = ((n + 1) / 2 - 1, decide ((n + 1) % 2 = 1) :: acc) := by
        simp [natToBitsStep, hn]
      rw [hstep]
      have hk : (n + 1) / 2 - 1 < k := by omega
      rw [ih k (decide ((n + 1) % 2 = 1) :: acc) hk]
      have hnb : natToBits n = natToBits ((n + 1) / 2 - 1) ++ [decide ((n + 1) % 2 = 1)] := by
        conv_lhs => rw [natToBits]
        simp [hn]
      rw [hnb, List.append_assoc]
      simp

theorem natToBitsFuel_eq (n : ℕ) : natToBitsFuel (n + 1) n = natToBits n := by
  unfold natToBitsFuel
  rw [natToBitsStep_iterate_acc n (n + 1) [] (by omega), List.append_nil]

private theorem primrec_natToBitsStep : Primrec natToBitsStep := by
  have hc : Primrec fun st : ℕ × List Bool => decide (st.1 + 1 < 2) :=
    Primrec.nat_lt.decide.comp (Primrec.succ.comp Primrec.fst) (Primrec.const 2)
  have hdiv : Primrec fun st : ℕ × List Bool => (st.1 + 1) / 2 - 1 :=
    Primrec.nat_sub.comp
      (Primrec.nat_div.comp (Primrec.succ.comp Primrec.fst) (Primrec.const 2))
      (Primrec.const 1)
  have hbit : Primrec fun st : ℕ × List Bool => decide ((st.1 + 1) % 2 = 1) :: st.2 :=
    Primrec.list_cons.comp
      (Primrec.eq.decide.comp
        (Primrec.nat_mod.comp (Primrec.succ.comp Primrec.fst) (Primrec.const 2))
        (Primrec.const 1))
      Primrec.snd
  have hfalse : Primrec fun st : ℕ × List Bool =>
      ((st.1 + 1) / 2 - 1, decide ((st.1 + 1) % 2 = 1) :: st.2) := hdiv.pair hbit
  have := Primrec.cond hc Primrec.id hfalse
  refine this.of_eq fun st => ?_
  unfold natToBitsStep
  simp only [id]
  rw [Bool.cond_decide]

private theorem primrec₂_natToBitsFuel : Primrec₂ natToBitsFuel := by
  have hh : Primrec₂ fun (_ : ℕ × ℕ) (x : ℕ × List Bool) => natToBitsStep x :=
    primrec_natToBitsStep.comp Primrec.snd
  have := Primrec.nat_iterate (α := ℕ × ℕ) Primrec.fst
    (Primrec.snd.pair (Primrec.const ([] : List Bool))) hh
  exact (Primrec.snd.comp this).of_eq fun p => rfl

theorem primrec_natToBits : Primrec natToBits := by
  have := primrec₂_natToBitsFuel.comp Primrec.succ Primrec.id
  exact this.of_eq natToBitsFuel_eq

theorem primrec_bitsToNat : Primrec bitsToNat := by
  have hstep : Primrec₂ fun (acc : ℕ) (b : Bool) => 2 * acc + b.toNat :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
      ((Primrec.dom_bool Bool.toNat).comp Primrec.snd)
  have hh : Primrec₂ fun (_ : List Bool) (sb : ℕ × Bool) => 2 * sb.1 + sb.2.toNat :=
    Primrec.comp₂ hstep Primrec₂.right
  have hfold : Primrec fun p : List Bool => p.foldl (fun acc b => 2 * acc + b.toNat) 1 :=
    Primrec.list_foldl Primrec.id (Primrec.const 1) hh
  exact (Primrec.nat_sub.comp hfold (Primrec.const 1)).of_eq fun p => by
    simp [bitsToNat]


/-- **Prefix of one bit-string by another**: `p <+: q ↔ List.take p.length q = p`. -/
theorem primrec_isPrefix : PrimrecRel fun p q : List Bool => p <+: q :=
  (Primrec.eq.comp₂ (Primrec₂.left)
      (Primrec₂.comp₂ Primrec.list_take (Primrec.list_length.comp₂ Primrec₂.left)
        Primrec₂.right)).of_eq
    fun _ _ => (List.prefix_iff_eq_take).symm

/-- The relation `foldStep` tests: some earlier-accepted input is comparable, as a bit-string, to
the candidate. -/
private theorem primrec_foldStep_rel :
    PrimrecRel fun m n : ℕ => natToBits m <+: natToBits n ∨ natToBits n <+: natToBits m := by
  have hA : PrimrecRel fun m n : ℕ => natToBits m <+: natToBits n :=
    primrec_isPrefix.comp₂ (Primrec.comp₂ primrec_natToBits Primrec₂.left)
      (Primrec.comp₂ primrec_natToBits Primrec₂.right)
  have hB : PrimrecRel fun m n : ℕ => natToBits n <+: natToBits m :=
    primrec_isPrefix.comp₂ (Primrec.comp₂ primrec_natToBits Primrec₂.right)
      (Primrec.comp₂ primrec_natToBits Primrec₂.left)
  exact hA.or hB

/-- List membership is a `PrimrecRel`. -/
theorem primrec_mem_list : PrimrecRel fun (L : List ℕ) (n : ℕ) => n ∈ L :=
  (Primrec.eq.exists_mem_list).of_eq fun _ n =>
    ⟨fun ⟨_, hm, he⟩ => he ▸ hm, fun h => ⟨n, h, rfl⟩⟩

end PrefixMachine
