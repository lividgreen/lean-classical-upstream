module

public import AIT.KolmogorovComplexity
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Nat.Size

/-!
# Time-bounded Kolmogorov complexity + bit-length refinement

Extends `AIT/KolmogorovComplexity.lean` (`codelen`, `Computes`, `K`, `K_le`,
`exists_min_code`, `K_unbounded`, `K_not_computable`).

Status: PROVED. This file adds the time-bounded measure and the bit-length value-reconnection.

## `K_t` is classical time-bounded K
`K_t` below is **classical time-bounded Kolmogorov complexity** (Li and Vitányi §7.1): the least
program length over *deterministic* codes outputting a fixed `x` within a step budget.

## What this DOES establish
* `K_t`: time-bounded (least-index) Kolmogorov complexity — least program length over codes
  outputting `x` from input `0` within `t` `evaln`-steps; `⊤ : ℕ∞` if none halts in budget `t`.
* `K_le_K_t`, `K_t_antitone`, `K_t_eventually`: `K ≤ K_t`; antitone in the budget; and `K_t = K`
  for all large enough budgets (the optimal program halts in finite time).
* `K_bitlen` (= the program length in *bits*) with `K_bitlen_eq : K_bitlen x = Nat.size (K x)` — the
  precise reconnection to the index `K` (same minimizer; `Nat.size` monotone) — and
  `K_bitlen_unbounded`.

## What this does NOT establish (flagged)
* Does NOT reconnect `K`/`K_t`/`K_bitlen` to the abstract `r`/`K` reals of the other files
  — `K_bitlen` reconnects the *measure* to bit-length, but substituting it for such abstract
  variables is a separate later step.
* `K_t` uses the *index* `codelen` (consistent with `K`), so it inherits `K`'s
  index-vs-bit-length caveat; a description length is in bits. A bit-length time-bounded version
  `Nat.size ∘ K_t` is DEFERRED (alongside the other bit-length items).
* `K_bitlen_not_computable` is DEFERRED — it needs `Computable Nat.size`, absent from Mathlib
  (would need a `Primrec Nat.size` detour); `K_not_computable` already proves the
  uncomputability headline, and `K_bitlen = Nat.size ∘ K` differs only by a computable monotone map.
  Two-machine invariance is also DEFERRED.
* NOT the structure function.

## Hypotheses: standard vs added
* Standard: time-bounded complexity + monotonicity/limit; bit-length `r`; `= ∞` on
  empty budget.
* Added / modeling: `t` = `evaln` step-count as the budget; `ℕ∞`/`⊤` rendering; least-**index**
  still underlies `K` (bit-length is `Nat.size` of it).
-/


@[expose] public section

namespace KolmogorovComplexity

open Nat.Partrec Nat.Partrec.Code

/-- Code-lengths of programs outputting `x` from input `0` within `t` steps (`evaln`). -/
def tCodelens (t x : ℕ) : Set ℕ := { l | ∃ c, x ∈ Code.evaln t c 0 ∧ codelen c = l }

/-- Time-bounded (least-index) Kolmogorov complexity: least program length over
codes that output `x` from input `0` within `t` `evaln`-steps; `⊤` if none halts in budget `t`. -/
noncomputable def K_t (t x : ℕ) : ℕ∞ := sInf ((Nat.cast : ℕ → ℕ∞) '' tCodelens t x)

/-- More compute never hurts the unbounded bound: `K x ≤ K_t t x` — the `t`-bounded programs are a
sub-collection of all programs (`evaln_sound`). -/
theorem K_le_K_t (t x : ℕ) : (K x : ℕ∞) ≤ K_t t x := by
  apply le_sInf
  rintro _ ⟨_, ⟨c, hev, rfl⟩, rfl⟩
  exact_mod_cast K_le (Part.eq_some_iff.mpr (evaln_sound hev))

/-- Antitone in the budget: more steps ⇒ no larger `K_t` (more programs qualify, `evaln_mono`). -/
theorem K_t_antitone {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) (x : ℕ) : K_t t₂ x ≤ K_t t₁ x := by
  apply sInf_le_sInf
  apply Set.image_mono
  rintro l ⟨c, hev, rfl⟩
  exact ⟨c, evaln_mono h hev, rfl⟩

/-- Eventually meets the unbounded `K`: the optimal program halts in finite time, so for every
budget at least that, `K_t t x = K x`. -/
theorem K_t_eventually (x : ℕ) : ∃ T, ∀ t, T ≤ t → K_t t x = (K x : ℕ∞) := by
  obtain ⟨c, hcomp, hlen⟩ := exists_min_code x
  obtain ⟨T, hT⟩ := evaln_complete.1 (Part.eq_some_iff.mp hcomp)
  refine ⟨T, fun t ht => le_antisymm ?_ (K_le_K_t t x)⟩
  -- `c` halts within budget `t ≥ T`, so its length `K x` is in the budget-`t` set.
  apply csInf_le'
  exact ⟨codelen c, ⟨c, evaln_mono ht hT, rfl⟩, by rw [hlen]⟩

/-- Bit-length program measure: `Nat.size (encode c)` — the program length in *bits*,
vs `codelen = encode c` (index). -/
def codelen' (c : Code) : ℕ := Nat.size (codelen c)

/-- Bit-length Kolmogorov complexity. -/
noncomputable def K_bitlen (x : ℕ) : ℕ := sInf { l | ∃ c, Computes c x ∧ codelen' c = l }

/-- Value-reconnection: the bit-length complexity is exactly `Nat.size` of the index `K`
(same minimizer — `Nat.size` is monotone; value = bit-length of the index). This is the precise
"bit-length = `Nat.size ∘` (index-`K`)" link between the two measures. -/
theorem K_bitlen_eq (x : ℕ) : K_bitlen x = Nat.size (K x) := by
  apply le_antisymm
  · -- the K-minimizing code witnesses `Nat.size (K x)` in the bit-length set
    obtain ⟨c, hcomp, hlen⟩ := exists_min_code x
    exact Nat.sInf_le ⟨c, hcomp, by simp [codelen', hlen]⟩
  · -- `Nat.size (K x)` lower-bounds the bit-length set (size monotone, `K x ≤ codelen c`)
    apply le_csInf
    · exact ⟨codelen' (Code.const x), Code.const x, const_computes x, rfl⟩
    · rintro l ⟨c, hcomp, rfl⟩
      exact Nat.size_le_size (K_le hcomp)

/-- `K_bitlen` is unbounded (incompressible objects in bits too). -/
theorem K_bitlen_unbounded (n : ℕ) : ∃ x, n < K_bitlen x := by
  obtain ⟨x, hx⟩ := K_unbounded (2 ^ n)
  refine ⟨x, ?_⟩
  rw [K_bitlen_eq, Nat.lt_size]
  exact le_of_lt hx

end KolmogorovComplexity
