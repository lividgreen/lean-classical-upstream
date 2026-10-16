module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Polynomial-bound arithmetic below the SQ model

The `PolyBounded` predicate ("Assumption A", `d_SQ = poly(r)`), the modeled exponential
statistical dimension `dSQ`, and the three pure real-arithmetic facts about version-space pruning
that the SQ oracle, the SQ objects and the SQ envelope consume: `candidates_polyBounded`,
`truth_survives_pruning` and `truth_survives_pruning_noisy`.
Nothing here mentions a query, an oracle or a concept class.
-/

@[expose] public section

namespace SQBounds

open Asymptotics Filter

/-- Modeled parity statistical dimension: exponential in the rule complexity `r`
(`2^{Ω(n)}` with `r ≈ n`, the base folded into `ε > 0`). -/
noncomputable def dSQ (ε r : ℝ) : ℝ := Real.exp (ε * r)

/-- "Assumption A": `d_SQ` is polynomially bounded in `r`. The weakest
reasonable form of "poly-bounded" (genuine natural-number degree `k`), so its negation is the
strongest faithful "not polynomial" claim. -/
def PolyBounded (f : ℝ → ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ r in atTop, f r ≤ C * r ^ k

/-- **T1 — version-space bound**:
if the statistical dimension `dSQ` is polynomially bounded in `r` (Assumption A) and the candidate
set / version space is bounded by a polynomial in `dSQ` (the modeled BFJKMR envelope
`candidates ≤ A · dSQ^m`), then the candidate set is itself `poly(r)`.

This is the POSITIVE direction: a polynomially bounded dimension delivers a `poly(r)` candidate
set. -/
theorem candidates_polyBounded
    (dSQ candidates : ℝ → ℝ)
    (hd : PolyBounded dSQ)
    (A : ℝ) (m : ℕ) (hA : 0 ≤ A)
    (hcand : ∀ᶠ r in atTop, candidates r ≤ A * (dSQ r) ^ m)
    (hdpos : ∀ᶠ r in atTop, 0 ≤ dSQ r) :
    PolyBounded candidates := by
  obtain ⟨C, k, hCk⟩ := hd
  refine ⟨A * C ^ m, k * m, ?_⟩
  filter_upwards [hcand, hdpos, hCk] with r hcr hdr hCkr
  have hstep : (dSQ r) ^ m ≤ (C * r ^ k) ^ m := pow_le_pow_left₀ hdr hCkr m
  have hmain : candidates r ≤ A * (C * r ^ k) ^ m :=
    hcr.trans (mul_le_mul_of_nonneg_left hstep hA)
  have heq : A * C ^ m * r ^ (k * m) = A * (C * r ^ k) ^ m := by
    rw [mul_pow, ← pow_mul]; ring
  rw [heq]; exact hmain

/-- **T2a — the truth survives**: the pruning rule drops any candidate whose
predicted statistic deviates from the empirical answer by `> 2τ`. If the empirical answer `emp` is
within `τ` of the truth's mean `predR` (Birkhoff + concentration, modeled as `hemp`), then the
truth's own deviation `|predR − emp|` is `≤ 2τ` — so the truth is NEVER pruned. -/
theorem truth_survives_pruning
    (predR emp τ : ℝ) (hτ : 0 ≤ τ)
    (hemp : |emp - predR| ≤ τ) :
    |predR - emp| ≤ 2 * τ := by
  rw [abs_sub_comm]; linarith

-- `hτ`, `hη` are kept for regime faithfulness (they parallel the noiseless lemma and the
-- `η, τ ≥ 0` budget) though the arithmetic needs only the budget `2η ≤ τ`; hence the underscores.
/-- **T2a-noisy — the truth survives noisy pruning** (the window-noise refinement of
`truth_survives_pruning`).  The empirical answer concentrates on the noisy answer `a`
(`|emp − a| ≤ τ`), and `a` sits within the window-noise gap `2η` of the deterministic-prediction
truth `predR` (`|a − predR| ≤ 2η`).  Then, provided the window-noise budget `2η ≤ τ` holds, the
truth's deviation `|predR − emp|` from the empirical answer is still `≤ 2τ` — so the *unchanged*
`2τ`-pruning rule never discards it.  At `η = 0` (forcing `a = predR`) this is
`truth_survives_pruning`. -/
theorem truth_survives_pruning_noisy
    (predR a emp τ η : ℝ) (_hτ : 0 ≤ τ) (_hη : 0 ≤ η)
    (hbudget : 2 * η ≤ τ) (hconc : |emp - a| ≤ τ) (hnoise : |a - predR| ≤ 2 * η) :
    |predR - emp| ≤ 2 * τ := by
  have h := abs_sub_le predR a emp
  rw [abs_sub_comm predR a, abs_sub_comm a emp] at h
  linarith

end SQBounds
