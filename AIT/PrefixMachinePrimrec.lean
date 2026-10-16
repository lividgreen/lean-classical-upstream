module

public import AIT.PrefixMachine
public import CodeLayer.BitStringPrimrec
import all CodeLayer.BitStringPrimrec

/-!
# The prefix machine's computability, and `pfy`'s uniform partial recursiveness

Over the universal prefix machine `PrefixMachine.pfy`.
Extends `AIT/PrefixMachine.lean` (`foldStep`, `newlyHalting`, `acceptedList`, `pfy`) with the
bit-string computability layer of `CodeLayer/BitStringPrimrec.lean`.

## What this establishes

* `foldStep`, `newlyHalting`, `acceptedList` are `Primrec₂`.
* **`pfy_partrec`**: `pfy` is partial recursive, uniformly in the machine — the open boundary
  `AIT/PrefixMachine.lean` flags at `pfy`'s own definition.

## What this does NOT establish (flagged)

* The algorithmic probability `QB`'s lower-semicomputability and the coding theorem itself are not
  attempted here.
-/


@[expose] public section

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity CodeEvalLaws KolmogorovComplexity

/-! ## `foldStep`, `newlyHalting`, `acceptedList` are primitive recursive -/

private theorem primrec₂_foldStep : Primrec₂ foldStep := by
  have hExists : PrimrecRel fun (L : List ℕ) (n : ℕ) =>
      ∃ m ∈ L, natToBits m <+: natToBits n ∨ natToBits n <+: natToBits m :=
    primrec_foldStep_rel.exists_mem_list
  exact (Primrec.ite hExists Primrec.fst Primrec.list_concat).of_eq fun p => by
    unfold foldStep
    rfl

private theorem primrec₂_newlyHalting : Primrec₂ newlyHalting := by
  have hf : Primrec fun a : Code × ℕ => List.range (a.2 + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)
  have hq1 : Primrec fun p : (Code × ℕ) × ℕ => ((p.1.2 + 1, p.1.1), p.2) :=
    ((Primrec.succ.comp (Primrec.snd.comp Primrec.fst)).pair
      (Primrec.fst.comp Primrec.fst)).pair Primrec.snd
  have hEv1 : Primrec fun p : (Code × ℕ) × ℕ => evaln (p.1.2 + 1) p.1.1 p.2 := by
    have := Nat.Partrec.Code.primrec_evaln.comp hq1
    exact this.of_eq fun p => rfl
  have hq0 : Primrec fun p : (Code × ℕ) × ℕ => ((p.1.2, p.1.1), p.2) :=
    ((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.fst)).pair Primrec.snd
  have hEv0 : Primrec fun p : (Code × ℕ) × ℕ => evaln p.1.2 p.1.1 p.2 := by
    have := Nat.Partrec.Code.primrec_evaln.comp hq0
    exact this.of_eq fun p => rfl
  have hCond : Primrec fun p : (Code × ℕ) × ℕ =>
      (evaln (p.1.2 + 1) p.1.1 p.2).isSome && !(evaln p.1.2 p.1.1 p.2).isSome :=
    Primrec.and.comp (Primrec.option_isSome.comp hEv1)
      (Primrec.not.comp (Primrec.option_isSome.comp hEv0))
  have hg : Primrec₂ fun (a : Code × ℕ) (n : ℕ) =>
      cond ((evaln (a.2 + 1) a.1 n).isSome && !(evaln a.2 a.1 n).isSome) (some n) none :=
    Primrec.cond hCond (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  have hres := Primrec.listFilterMap hf hg
  refine hres.of_eq fun a => ?_
  simp only [newlyHalting, ← List.filterMap_eq_filter, Bool.cond_eq_ite, Option.guard]

theorem primrec₂_acceptedList : Primrec₂ acceptedList := by
  have hf' : Primrec fun a : Code × (ℕ × List ℕ) => newlyHalting a.1 a.2.1 :=
    Primrec.comp primrec₂_newlyHalting (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  have hg' : Primrec fun a : Code × (ℕ × List ℕ) => a.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hh' : Primrec₂ fun (_ : Code × (ℕ × List ℕ)) (sb : List ℕ × ℕ) => foldStep sb.1 sb.2 :=
    Primrec.comp₂ primrec₂_foldStep Primrec₂.right
  have hfold : Primrec fun a : Code × (ℕ × List ℕ) =>
      (newlyHalting a.1 a.2.1).foldl foldStep a.2.2 :=
    Primrec.list_foldl hf' hg' hh'
  have hfold₂ : Primrec₂ fun (c : Code) (sa : ℕ × List ℕ) =>
      (newlyHalting c sa.1).foldl foldStep sa.2 := hfold
  have := Primrec.nat_rec (f := fun _ : Code => ([] : List ℕ)) (Primrec.const []) hfold₂
  refine this.of_eq fun c s => ?_
  induction s with
  | zero => rfl
  | succ s ih =>
      change (newlyHalting c s).foldl foldStep (Nat.rec [] _ s) = acceptedList c (s + 1)
      rw [ih]
      rfl

/-! ## `pfy` is partial recursive, uniformly in the machine -/

private theorem primrec₂_acceptedList_mem :
    Primrec₂ fun (cn : Code × ℕ) (s : ℕ) => decide (cn.2 ∈ acceptedList cn.1 s) := by
  have hL : Primrec fun p : (Code × ℕ) × ℕ => acceptedList p.1.1 p.2 :=
    Primrec.comp primrec₂_acceptedList (Primrec.fst.comp Primrec.fst |>.pair Primrec.snd)
  have hn0 : Primrec fun p : (Code × ℕ) × ℕ => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  exact (primrec_mem_list.comp hL hn0).decide

open scoped Classical in
/-- Once the state has bottomed out, `Nat.rfind` over acceptance-by-stage reproduces `pfy`'s own
`Nat.find`. -/
private theorem rfind_acceptedList_eq (c : Code) (n : ℕ) :
    Nat.rfind (fun s => Part.some (decide (n ∈ acceptedList c s))) =
      if h : ∃ s, n ∈ acceptedList c s then Part.some (Nat.find h) else Part.none := by
  split
  · rename_i h
    apply Part.eq_some_iff.mpr
    apply Nat.mem_rfind.mpr
    refine ⟨by simp [Nat.find_spec h], fun {m} hm => ?_⟩
    simp only [Part.mem_some_iff]
    exact (decide_eq_false (Nat.find_min h hm)).symm
  · rename_i h
    apply Part.eq_none_iff.mpr
    rintro v hv
    replace hv := Nat.mem_rfind.mp hv
    apply h
    refine ⟨v, ?_⟩
    have := hv.1
    simp only [Part.mem_some_iff] at this
    simpa using this.symm

/-- **`pfy` is `Nat.rfind`-then-`evaln`**, over the stage at which `n` first gets accepted. -/
theorem pfy_eq_bind (c : Code) (n : ℕ) :
    pfy c n = (Nat.rfind fun s => Part.some (decide (n ∈ acceptedList c s))) >>=
      fun s => (evaln s c n : Part ℕ) := by
  change pfy c n =
    (Nat.rfind fun s => Part.some (decide (n ∈ acceptedList c s))).bind
      fun s => (evaln s c n : Part ℕ)
  rw [rfind_acceptedList_eq]
  unfold pfy
  split
  · rename_i h
    rw [Part.bind_some]
    conv_rhs =>
      rw [← Option.some_get (evaln_isSome_of_mem_acceptedList c (Nat.find h) (Nat.find_spec h))]
    rfl
  · rename_i h
    exact (Part.bind_none _).symm

/-- **`pfy` is partial recursive, uniformly in the machine.** -/
theorem pfy_partrec : Partrec₂ fun (c : Code) (n : ℕ) => pfy c n := by
  have hcomp : Computable₂ fun (cn : Code × ℕ) (s : ℕ) => decide (cn.2 ∈ acceptedList cn.1 s) :=
    primrec₂_acceptedList_mem.to_comp
  have hpart : Partrec₂ fun (cn : Code × ℕ) (s : ℕ) =>
      Part.some (decide (cn.2 ∈ acceptedList cn.1 s)) :=
    hcomp.partrec₂
  have hrfind : Partrec fun cn : Code × ℕ =>
      Nat.rfind fun s => Part.some (decide (cn.2 ∈ acceptedList cn.1 s)) :=
    Partrec.rfind hpart
  have hevalnc : Computable fun p : (Code × ℕ) × ℕ => evaln p.2 p.1.1 p.1.2 := by
    have hq : Primrec fun p : (Code × ℕ) × ℕ => ((p.2, p.1.1), p.1.2) :=
      (Primrec.snd.pair (Primrec.fst.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.fst)
    have := Primrec.comp Nat.Partrec.Code.primrec_evaln hq
    exact this.to_comp.of_eq fun p => rfl
  have hg : Partrec₂ fun (cn : Code × ℕ) (s : ℕ) => (evaln s cn.1 cn.2 : Part ℕ) :=
    Computable.ofOption hevalnc
  have hbind : Partrec fun cn : Code × ℕ =>
      (Nat.rfind fun s => Part.some (decide (cn.2 ∈ acceptedList cn.1 s))) >>=
        fun s => (evaln s cn.1 cn.2 : Part ℕ) :=
    Partrec.bind hrfind hg
  exact hbind.of_eq fun cn => (pfy_eq_bind cn.1 cn.2).symm

end PrefixMachine
