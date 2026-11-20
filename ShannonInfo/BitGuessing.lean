module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import ShannonInfo.CslibFrontier.Probability.Divergence
import ShannonInfo.FiniteInfoTheory

/-!
# The bits of a string a guesser reads from a short message

Let `z` be uniform on `Fin N → Bool` and let `φ z` be a message about `z` from a finite alphabet
`V`. A guesser of bit `k` that reads the message and only the bits before `k` is right on at most
`N / 2 + √(N ln |V| / 2)` of the `N` bits on average over `z`: the message carries at most `ln |V|`
nats about the string, the chain rule for relative entropy spends them across the bits in order,
Pinsker's inequality bounds each bit's advantage by the square root of half its share, and the
Cauchy–Schwarz inequality sums the `N` square roots.

## Main definitions

* `BitGuessing.Causal`: a family of guessers of the bits, each reading only the earlier bits.

## Main results

* `BitGuessing.sum_hits_le`: the bound on the total number of bits guessed right.

## The proof

The proof is an induction on the number of bits that splits off the first bit and carries a
nonnegative weight on pairs of a message and a string in place of the uniform law.
The information of a weight is `N · mass · ln 2` plus the entropy sum of the masses of the messages
minus that of the weights, which is the divergence of the weight from the product of its message
marginal and the uniform law on the string.
It is the divergence of the first bit's conditional law from the even coin, averaged over the
messages, plus the information of the two weights of the remaining bits, which is the chain rule.
Pinsker's inequality for one bit and the Cauchy–Schwarz inequality combine the first bit with the
two remaining parts.
For the indicator weight of the graph of `φ` the information is the entropy of the message, at most
`ln |V|` by Gibbs' inequality.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006]:
  the chain rule for relative entropy (Section 2.5) and Pinsker's inequality (Section 11.6).
* [A. Nayak, *Optimal lower bounds for quantum automata and random access codes*, 40th FOCS
  (1999), Theorem 2.3] and [Z. Bar-Yossef, T. S. Jayram, R. Krauthgamer and R. Kumar, *The
  sketching complexity of pattern matching*, APPROX-RANDOM 2004, Lemma 2]: the nearest stated
  forms. The first bounds the information a message carries about a bit at every position, with
  the later bits as side information. The second bounds it at a uniformly random position, with a
  window of the preceding bits as side information. The averaged whole-prefix form proved here is
  neither of the two.
* [R. Raz, *A parallel repetition theorem*, SIAM J. Comput. 27 (1998)] and
  [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*,
  Theory of Computing 5 (2009)]: bounding what a message reveals about independent coordinates by
  the chain rule for relative entropy and Pinsker's inequality.
-/

@[expose] public section

namespace BitGuessing

open Cslib.Probability

/-- Pinsker's inequality for a bit: the divergence of a bias `p` from the fair coin dominates
twice the squared bias, `2 (p - 1/2)^2 ≤ ln 2 - h(p)` with `h` the entropy in nats. -/
private lemma bernPinsker {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    2 * (p - 1 / 2) ^ 2 ≤ Real.log 2 - Real.negMulLog p - Real.negMulLog (1 - p) := by
  let q : PMF Bool := PMF.ofFintype
    (fun b => if b then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) (by
      rw [Fintype.sum_bool]
      simp only [ite_true, Bool.false_eq_true, ite_false]
      rw [← ENNReal.ofReal_add h0 (by linarith)]
      simp)
  have hq : ∀ b, (q b).toReal = if b then p else 1 - p := by
    intro b
    cases b
    · simp [q, PMF.ofFintype_apply, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - p)]
    · simp [q, PMF.ofFintype_apply, ENNReal.toReal_ofReal h0]
  have hsub : q.support ⊆ (PMF.uniformOfFintype Bool).support := by
    intro b _
    simp
  have h := PMF.two_mul_dist_sq_le_sum_mul_log_div hsub
  rw [PMF.dist_uniformOfFintype_bool, hq, sq_abs, Fintype.sum_bool] at h
  have hu : ∀ b, ((PMF.uniformOfFintype Bool) b).toReal = 1 / 2 := by
    intro b
    simp [PMF.uniformOfFintype_apply]
  simp only [hu, hq, ite_true, Bool.false_eq_true, ite_false] at h
  have e1 : p * Real.log (p / (1 / 2)) = p * Real.log 2 - Real.negMulLog p := by
    rcases eq_or_lt_of_le h0 with h | h
    · subst h; simp
    · rw [show p / (1 / 2) = p * 2 by ring, Real.log_mul h.ne' (by norm_num), Real.negMulLog]
      ring
  have e2 : (1 - p) * Real.log ((1 - p) / (1 / 2)) =
      (1 - p) * Real.log 2 - Real.negMulLog (1 - p) := by
    rcases eq_or_lt_of_le (sub_nonneg.2 h1) with h | h
    · rw [← h]; simp
    · rw [show (1 - p) / (1 / 2) = (1 - p) * 2 by ring, Real.log_mul h.ne' (by norm_num),
        Real.negMulLog]
      ring
  rw [e1, e2] at h
  linarith

/-- The divergence of the split `(a, b)` of a mass `a + b` from the even split, unnormalised:
`a ln (2a / (a + b)) + b ln (2b / (a + b))`, written through `Real.negMulLog`. -/
private noncomputable def klBit (a b : ℝ) : ℝ :=
  Real.negMulLog (a + b) - Real.negMulLog a - Real.negMulLog b + (a + b) * Real.log 2

private lemma klBit_pinsker {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) ^ 2 ≤ 2 * (a + b) * klBit a b := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with hs | hs
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0
    simp [klBit]
  · set s := a + b with hsdef
    set p := b / s with hp
    have hp0 : 0 ≤ p := div_nonneg hb hs.le
    have hp1 : p ≤ 1 := by rw [hp, div_le_one hs]; linarith
    have hbs : b = s * p := by rw [hp]; field_simp
    have has : a = s * (1 - p) := by
      have : a = s - b := by linarith
      rw [this, hbs]; ring
    have hk : klBit a b = s * (Real.log 2 - Real.negMulLog p - Real.negMulLog (1 - p)) := by
      unfold klBit
      rw [← hsdef]
      have e1 := Real.negMulLog_mul s (1 - p)
      have e2 := Real.negMulLog_mul s p
      rw [← has] at e1
      rw [← hbs] at e2
      rw [e1, e2]
      ring
    have hpin := bernPinsker hp0 hp1
    rw [hk]
    have h1 : (a - b) ^ 2 = 4 * s ^ 2 * (p - 1 / 2) ^ 2 := by
      rw [has, hbs]; ring
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left hpin (sq_nonneg s)]

private lemma klBit_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ klBit a b := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with hs | hs
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0
    simp [klBit]
  · have := klBit_pinsker ha hb
    have h2 : 0 ≤ 2 * (a + b) * klBit a b := le_trans (sq_nonneg _) this
    by_contra hneg
    push Not at hneg
    nlinarith


private lemma cs3 {x1 x2 x3 y1 y2 y3 : ℝ} (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3)
    (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hy3 : 0 ≤ y3) :
    √x1 * √y1 + √x2 * √y2 + √x3 * √y3 ≤ √(x1 + x2 + x3) * √(y1 + y2 + y3) := by
  have := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin 3)) (f := ![x1, x2, x3])
    (g := ![y1, y2, y3]) (by intro i; fin_cases i <;> simpa) (by intro i; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_succ, add_assoc] using this

section

variable {V : Type} [Fintype V]

private lemma sum_abs_le (a b : V → ℝ) (ha : ∀ v, 0 ≤ a v) (hb : ∀ v, 0 ≤ b v) :
    ∑ v, |a v - b v| / 2 ≤ √(∑ v, (a v + b v)) * √((∑ v, klBit (a v) (b v)) / 2) := by
  have hpt : ∀ v, |a v - b v| ≤ √(a v + b v) * √(2 * klBit (a v) (b v)) := by
    intro v
    rw [← Real.sqrt_mul (add_nonneg (ha v) (hb v))]
    exact Real.abs_le_sqrt (by
      have := klBit_pinsker (ha v) (hb v)
      linarith)
  have hk : ∀ v, 0 ≤ klBit (a v) (b v) := fun v => klBit_nonneg (ha v) (hb v)
  have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset V)
    (f := fun v => a v + b v) (g := fun v => 2 * klBit (a v) (b v))
    (fun v => add_nonneg (ha v) (hb v)) (fun v => by have := hk v; linarith)
  have hsum : ∑ v, |a v - b v| ≤
      √(∑ v, (a v + b v)) * √(∑ v, 2 * klBit (a v) (b v)) :=
    le_trans (Finset.sum_le_sum fun v _ => hpt v) hcs
  rw [← Finset.mul_sum] at hsum
  have hK : 0 ≤ ∑ v, klBit (a v) (b v) := Finset.sum_nonneg fun v _ => hk v
  have h2 : √(2 * ∑ v, klBit (a v) (b v)) = 2 * √((∑ v, klBit (a v) (b v)) / 2) := by
    rw [show 2 * ∑ v, klBit (a v) (b v) = 2 ^ 2 * ((∑ v, klBit (a v) (b v)) / 2) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h2] at hsum
  rw [← Finset.sum_div]
  linarith


/-- A family of guessers is causal when the guess of bit `k` reads only the earlier bits. -/
def Causal {N : ℕ} {V : Type} (g : Fin N → V → (Fin N → Bool) → Bool) : Prop :=
  ∀ (k : Fin N) (v : V) (z z' : Fin N → Bool), (∀ s : Fin N, s < k → z s = z' s) →
    g k v z = g k v z'

private lemma sum_cons {N : ℕ} {β : Type*} [AddCommMonoid β] (F : (Fin (N + 1) → Bool) → β) :
    ∑ z, F z = ∑ b : Bool, ∑ z' : Fin N → Bool, F (Fin.cons b z' : Fin (N + 1) → Bool) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool)) _ _ (fun _ => rfl)).symm

/-- The information of a nonnegative weight on messages and bit strings: `N` times the mass times
`ln 2`, plus the entropy sum of the message masses, minus that of the weights. -/
private noncomputable def info {N : ℕ} (w : V → (Fin N → Bool) → ℝ) : ℝ :=
  N * (∑ v, ∑ z, w v z) * Real.log 2 + ∑ v, Real.negMulLog (∑ z, w v z) -
    ∑ v, ∑ z, Real.negMulLog (w v z)

private noncomputable def mass {N : ℕ} (w : V → (Fin N → Bool) → ℝ) : ℝ := ∑ v, ∑ z, w v z

private def tailW {N : ℕ} (w : V → (Fin (N + 1) → Bool) → ℝ) (b : Bool) :
    V → (Fin N → Bool) → ℝ :=
  fun v z => w v (Fin.cons b z)

private lemma mass_succ {N : ℕ} (w : V → (Fin (N + 1) → Bool) → ℝ) :
    mass w = mass (tailW w false) + mass (tailW w true) := by
  unfold mass tailW
  simp only [sum_cons, Fintype.sum_bool, Finset.sum_add_distrib]
  ring

omit [Fintype V] in
private lemma sum_tail {N : ℕ} (w : V → (Fin (N + 1) → Bool) → ℝ) (v : V) :
    ∑ z, w v z = ∑ z, tailW w false v z + ∑ z, tailW w true v z := by
  rw [sum_cons, Fintype.sum_bool, add_comm]
  rfl

omit [Fintype V] in
private lemma sum_tail_negMulLog {N : ℕ} (w : V → (Fin (N + 1) → Bool) → ℝ) (v : V) :
    ∑ z, Real.negMulLog (w v z) =
      ∑ z, Real.negMulLog (tailW w false v z) + ∑ z, Real.negMulLog (tailW w true v z) := by
  rw [sum_cons, Fintype.sum_bool, add_comm]
  rfl

private lemma info_succ {N : ℕ} (w : V → (Fin (N + 1) → Bool) → ℝ) :
    info w = ∑ v, klBit (∑ z, tailW w false v z) (∑ z, tailW w true v z) +
      info (tailW w false) + info (tailW w true) := by
  unfold info klBit
  simp only [sum_tail, sum_tail_negMulLog, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_add, add_mul]
  simp only [← Finset.sum_mul]
  push_cast
  ring

private lemma info_nonneg : ∀ (N : ℕ) (w : V → (Fin N → Bool) → ℝ), (∀ v z, 0 ≤ w v z) →
    0 ≤ info w := by
  intro N
  induction N with
  | zero => intro w hw; simp [info]
  | succ N ih =>
    intro w hw
    rw [info_succ]
    have h1 : ∀ v, 0 ≤ ∑ z, tailW w false v z := fun v => Finset.sum_nonneg fun z _ => hw _ _
    have h2 : ∀ v, 0 ≤ ∑ z, tailW w true v z := fun v => Finset.sum_nonneg fun z _ => hw _ _
    have := ih (tailW w false) (fun v z => hw _ _)
    have := ih (tailW w true) (fun v z => hw _ _)
    have : 0 ≤ ∑ v, klBit (∑ z, tailW w false v z) (∑ z, tailW w true v z) :=
      Finset.sum_nonneg fun v _ => klBit_nonneg (h1 v) (h2 v)
    linarith

/-- The number of the bits `k` at which the guess `g k v z` of the string `z` is right. -/
private noncomputable def hits {N : ℕ} (g : Fin N → V → (Fin N → Bool) → Bool) (v : V)
    (z : Fin N → Bool) : ℝ :=
  ∑ k, if g k v z = z k then (1 : ℝ) else 0

private def shiftG {N : ℕ} (g : Fin (N + 1) → V → (Fin (N + 1) → Bool) → Bool) (b : Bool) :
    Fin N → V → (Fin N → Bool) → Bool :=
  fun k v z => g k.succ v (Fin.cons b z)

omit [Fintype V] in
private lemma shiftG_causal {N : ℕ} {g : Fin (N + 1) → V → (Fin (N + 1) → Bool) → Bool}
    (hg : Causal g) (b : Bool) : Causal (shiftG g b) := by
  intro k v z z' h
  unfold shiftG
  apply hg
  intro s hs
  induction s using Fin.cases with
  | zero => simp
  | succ s' =>
    simp only [Fin.cons_succ]
    exact h s' (Fin.succ_lt_succ_iff.1 hs)

omit [Fintype V] in
private lemma hits_succ {N : ℕ} {g : Fin (N + 1) → V → (Fin (N + 1) → Bool) → Bool}
    (hg : Causal g) (v : V) (b : Bool) (z' : Fin N → Bool) :
    hits g v (Fin.cons b z' : Fin (N + 1) → Bool) =
      (if g 0 v (fun _ => false) = b then 1 else 0) + hits (shiftG g b) v z' := by
  unfold hits
  rw [Fin.sum_univ_succ]
  congr 1
  · have : g 0 v (Fin.cons b z' : Fin (N + 1) → Bool) = g 0 v (fun _ => false) :=
      hg 0 v _ _ (fun s hs => absurd hs (Fin.not_lt_zero _))
    simp [this]

private noncomputable def score {N : ℕ} (w : V → (Fin N → Bool) → ℝ)
    (g : Fin N → V → (Fin N → Bool) → Bool) : ℝ :=
  ∑ v, ∑ z, w v z * hits g v z

private lemma score_succ {N : ℕ} (w : V → (Fin (N + 1) → Bool) → ℝ)
    {g : Fin (N + 1) → V → (Fin (N + 1) → Bool) → Bool} (hg : Causal g) :
    score w g =
      ∑ v, (if g 0 v (fun _ => false) then ∑ z, tailW w true v z else ∑ z, tailW w false v z) +
        score (tailW w false) (shiftG g false) + score (tailW w true) (shiftG g true) := by
  have hv : ∀ v, ∑ z, w v z * hits g v z =
      (if g 0 v (fun _ => false) then ∑ z, tailW w true v z else ∑ z, tailW w false v z) +
        (∑ z, tailW w false v z * hits (shiftG g false) v z +
          ∑ z, tailW w true v z * hits (shiftG g true) v z) := by
    intro v
    rw [sum_cons, Fintype.sum_bool]
    simp only [hits_succ hg, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    cases h : g 0 v (fun _ => false) <;> simp [tailW] <;> ring
  unfold score
  simp only [hv, Finset.sum_add_distrib]
  ring

private lemma score_le : ∀ (N : ℕ) (w : V → (Fin N → Bool) → ℝ), (∀ v z, 0 ≤ w v z) →
    ∀ g : Fin N → V → (Fin N → Bool) → Bool, Causal g →
    score w g ≤ N * mass w / 2 + √(N * mass w) * √(info w / 2) := by
  intro N
  induction N with
  | zero => intro w hw g hg; simp [score, mass, info, hits]
  | succ N ih =>
    intro w hw g hg
    have hs := score_succ w hg
    have ihf := ih (tailW w false) (fun v z => hw _ _) (shiftG g false) (shiftG_causal hg false)
    have iht := ih (tailW w true) (fun v z => hw _ _) (shiftG g true) (shiftG_causal hg true)
    have hinfo := info_succ w
    have hmass := mass_succ w
    set a : V → ℝ := fun v => ∑ z, tailW w false v z with ha_def
    set b : V → ℝ := fun v => ∑ z, tailW w true v z with hb_def
    have ha : ∀ v, 0 ≤ a v := fun v => Finset.sum_nonneg fun z _ => hw _ _
    have hb : ∀ v, 0 ≤ b v := fun v => Finset.sum_nonneg fun z _ => hw _ _
    have hmf : mass (tailW w false) = ∑ v, a v := rfl
    have hmt : mass (tailW w true) = ∑ v, b v := rfl
    have hfirst : ∀ v, (if g 0 v (fun _ => false) then b v else a v) ≤
        (a v + b v) / 2 + |a v - b v| / 2 := by
      intro v
      have h1 := le_abs_self (a v - b v)
      have h2 := le_abs_self (b v - a v)
      rw [abs_sub_comm] at h2
      cases g 0 v (fun _ => false) <;> simp <;> linarith
    have hsum1 : ∑ v, (if g 0 v (fun _ => false) then b v else a v) ≤
        (mass (tailW w false) + mass (tailW w true)) / 2 + ∑ v, |a v - b v| / 2 := by
      calc _ ≤ ∑ v, ((a v + b v) / 2 + |a v - b v| / 2) := Finset.sum_le_sum fun v _ => hfirst v
        _ = _ := by
          rw [Finset.sum_add_distrib, hmf, hmt, ← Finset.sum_div, Finset.sum_add_distrib]
    have habs := sum_abs_le a b ha hb
    have hK : ∑ v, (a v + b v) = mass w := by
      rw [hmass, hmf, hmt, Finset.sum_add_distrib]
    rw [hK] at habs
    have hmf0 : 0 ≤ mass (tailW w false) := Finset.sum_nonneg fun v _ => ha v
    have hmt0 : 0 ≤ mass (tailW w true) := Finset.sum_nonneg fun v _ => hb v
    have hk0 : 0 ≤ ∑ v, klBit (a v) (b v) := Finset.sum_nonneg fun v _ => klBit_nonneg (ha v) (hb v)
    have hif0 := info_nonneg N (tailW w false) (fun v z => hw _ _)
    have hit0 := info_nonneg N (tailW w true) (fun v z => hw _ _)
    have hw0 : 0 ≤ mass w := by rw [hmass]; linarith
    have hcs := cs3 (x1 := mass w) (x2 := N * mass (tailW w false)) (x3 := N * mass (tailW w true))
      (y1 := (∑ v, klBit (a v) (b v)) / 2) (y2 := info (tailW w false) / 2)
      (y3 := info (tailW w true) / 2) hw0 (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity)
    have hx : mass w + N * mass (tailW w false) + N * mass (tailW w true) =
        ((N + 1 : ℕ) : ℝ) * mass w := by
      rw [hmass]; push_cast; ring
    have hy : (∑ v, klBit (a v) (b v)) / 2 + info (tailW w false) / 2 + info (tailW w true) / 2 =
        info w / 2 := by
      rw [hinfo]; ring
    rw [hx, hy] at hcs
    have hmw : ((N + 1 : ℕ) : ℝ) * mass w / 2 =
        mass w / 2 + (N * mass (tailW w false) / 2 + N * mass (tailW w true) / 2) := by
      rw [hmass]; push_cast; ring
    rw [hs]
    rw [hmw]
    linarith

open Classical in
/-- The information of the fibres of a message map is at most the logarithm of the message
alphabet, weighted by the number of strings. -/
private lemma info_indicator_le {N : ℕ} (φ : (Fin N → Bool) → V) :
    info (fun (v : V) (z : Fin N → Bool) => if φ z = v then (1 : ℝ) else 0) ≤
      2 ^ N * Real.log (Fintype.card V) := by
  classical
  set w : V → (Fin N → Bool) → ℝ := fun v z => if φ z = v then 1 else 0 with hw
  have hne : Nonempty V := ⟨φ (fun _ => false)⟩
  have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  set m : V → ℝ := fun v => ∑ z, w v z with hm
  have hmsum : ∑ v, m v = 2 ^ N := by
    simp only [hm, hw]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  have hm0 : ∀ v, 0 ≤ m v := fun v =>
    Finset.sum_nonneg fun z _ => by simp only [hw]; split_ifs <;> simp
  have hent : ∑ v, ∑ z, Real.negMulLog (w v z) = 0 := by
    refine Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun z _ => ?_
    simp only [hw]
    split_ifs <;> simp
  set r : ℝ := 2 ^ N / Fintype.card V with hr
  have hr0 : 0 < r := by positivity
  have hterm : ∀ v, m v - r ≤ m v * Real.log (m v / r) := fun v =>
    FiniteInfoTheory.gibbs_term (hm0 v) hr0.le (fun _ => hr0)
  have hsum := Finset.sum_le_sum fun v (_ : v ∈ (Finset.univ : Finset V)) => hterm v
  have hid : ∀ v, m v * Real.log (m v / r) = -Real.negMulLog (m v) - m v * Real.log r := by
    intro v
    rcases eq_or_lt_of_le (hm0 v) with h | h
    · rw [← h]; simp
    · rw [Real.log_div h.ne' hr0.ne', Real.negMulLog]; ring
  simp only [hid, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.sum_mul, Finset.sum_neg_distrib, hmsum] at hsum
  have hlogr : Real.log r = N * Real.log 2 - Real.log (Fintype.card V) := by
    rw [hr, Real.log_div (by positivity) hV.ne', Real.log_pow]
  have hr' : (Fintype.card V : ℝ) * r = 2 ^ N := by rw [hr]; field_simp
  have e1 : ∑ v, ∑ z, w v z = 2 ^ N := hmsum
  have e2 : ∑ v, Real.negMulLog (∑ z, w v z) = ∑ v, Real.negMulLog (m v) := rfl
  unfold info
  rw [e1, e2, hent]
  rw [hlogr, hr'] at hsum
  linarith

/-- **The bits a short message lets a causal guesser predict.** Let `z` be uniform on `Fin N → Bool`
and `φ z` a message from a finite alphabet `V`. A guesser of bit `k`, from the message and the bits
before `k`, is right on the bits `k` of at most `N / 2 + √(N ln |V| / 2)` of the `N` positions on
average over `z`. Proved from the chain rule for relative entropy, which spends the information of
the message across the bits in order, and Pinsker's inequality for each bit, with the Cauchy–Schwarz
inequality to sum the square roots. -/
theorem sum_hits_le {N : ℕ} {V : Type} [Fintype V] (φ : (Fin N → Bool) → V)
    (g : Fin N → V → (Fin N → Bool) → Bool) (hg : Causal g) :
    ∑ z : Fin N → Bool, ∑ k : Fin N, (if g k (φ z) z = z k then (1 : ℝ) else 0) ≤
      2 ^ N * (N / 2 + √(N * Real.log (Fintype.card V) / 2)) := by
  classical
  set w : V → (Fin N → Bool) → ℝ := fun v z => if φ z = v then 1 else 0 with hw
  have hnn : ∀ v z, 0 ≤ w v z := fun v z => by simp only [hw]; split_ifs <;> simp
  have hne : Nonempty V := ⟨φ (fun _ => false)⟩
  have hlog : 0 ≤ Real.log (Fintype.card V) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hscore : score w g = ∑ z : Fin N → Bool, ∑ k : Fin N,
      (if g k (φ z) z = z k then (1 : ℝ) else 0) := by
    unfold score
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [hw, hits, ite_mul]
  have hmass : mass w = 2 ^ N := by
    unfold mass
    simp only [hw]
    rw [Finset.sum_comm]
    simp
  have hinfo : info w ≤ 2 ^ N * Real.log (Fintype.card V) := info_indicator_le φ
  have h1 := score_le N w hnn g hg
  rw [hscore, hmass] at h1
  have h2 : √(info w / 2) ≤ √(2 ^ N * Real.log (Fintype.card V) / 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have h3 : √((N : ℝ) * 2 ^ N) * √(info w / 2) ≤
      √((N : ℝ) * 2 ^ N) * √(2 ^ N * Real.log (Fintype.card V) / 2) :=
    mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
  have h4 : √((N : ℝ) * 2 ^ N) * √(2 ^ N * Real.log (Fintype.card V) / 2) =
      2 ^ N * √(N * Real.log (Fintype.card V) / 2) := by
    rw [← Real.sqrt_mul (by positivity),
      show (N : ℝ) * 2 ^ N * (2 ^ N * Real.log (Fintype.card V) / 2) =
        ((2 : ℝ) ^ N) ^ 2 * (N * Real.log (Fintype.card V) / 2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have h5 : (N : ℝ) * 2 ^ N / 2 = 2 ^ N * (N / 2) := by ring
  rw [mul_add, ← h5, ← h4]
  linarith

end

end BitGuessing
