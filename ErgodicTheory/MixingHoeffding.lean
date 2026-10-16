module

public import Mathlib.Probability.Moments.SubGaussian


/-!
# The mixing-Hoeffding predicates

The single-orbit Hoeffding hypothesis `MixingHoeffding` (in the shape of Fan, Jiang and Sun 2021),
its finite-horizon twin `MixingHoeffdingTo`, and the two lemmas relating them.
Both predicates are stated over the single-orbit empirical mean, the sum
`(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z i ω` written out; nothing
here uses an ergodic theorem, and the predicates are named hypotheses, not proved concentration
statements.
-/

@[expose] public section

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-- **FJS-shaped mixing Hoeffding hypothesis** (Fan–Jiang–Sun, JMLR 22(139), 2021, Thm 1).
For a stationary Markov trajectory law with absolute spectral gap `1 − λ ∈ (0, 1]` — where
`λ = ‖P − Π‖` is the operator norm of the transition operator on the mean-zero subspace of `L²(π)`,
so that reversibility is NOT required — the single-orbit empirical mean of a bounded query-ensemble
`Z` concentrates around its stationary mean `predZ` with the Hoeffding variance proxy inflated by
the mixing constant `c = (1 + λ)/(1 − λ) ≥ 1`.  (For a query bounded in `[a, b]` the constant is
`((b − a)²/4)·(1 + λ)/(1 − λ)`; the `[−1, 1]` normalization used throughout here makes the leading
factor `1`.)

This is the single-orbit analogue of `SQOracle.sq_oracle_concentration`; at `c = 1` (`λ = 0`,
the i.i.d. case) the two coincide.  It is stated as a *hypothesis*:
`MarkovHoeffding.mixingHoeffding_of_gap` derives it, for a finite-state chain, from an
operator-norm spectral gap and a chain trajectory law, at an explicit (non-sharp) constant
`cGap lam`; `MarkovHoeffding.exists_mixingHoeffding_of_gap` supplies that chain trajectory law
too, unconditionally. -/
def MixingHoeffding (μ : Measure (ℕ → X)) (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 1 ≤ n → 0 ≤ τ →
    μ.real {ω | τ ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z i ω - predZ|} ≤
      2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * c))

namespace MixingHoeffding

/-- **`MixingHoeffding` bounded to a finite horizon `N`.**  `MixingHoeffding` with its `∀ n`
quantifier restricted to `n ≤ N`, and nothing else moved: the reference answer stays the declared
stationary `predZ`, not the orbit's own cycle average — against the cycle average the predicate
would hold trivially at any horizon past the period while delivering nothing a consumer uses — and
the constant keeps the FJS shape and the `[−1, 1]` normalization, so every consumer of
`MixingHoeffding` above applies verbatim at `n ≤ N`.
`mixingHoeffding_iff_forall_mixingHoeffdingTo` recovers `MixingHoeffding` as the quantifier over
every horizon. -/
def MixingHoeffdingTo (N : ℕ) (μ : Measure (ℕ → X)) (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 1 ≤ n → n ≤ N → 0 ≤ τ →
    μ.real {ω | τ ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z i ω - predZ|} ≤
      2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * c))

/-- The unbounded hypothesis implies the bounded one at every horizon: dropping `n ≤ N` only widens
the universal it must satisfy. -/
theorem mixingHoeffdingTo_of_mixingHoeffding (N : ℕ) (μ : Measure (ℕ → X))
    (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) (h : MixingHoeffding μ Z predZ c) :
    MixingHoeffdingTo N μ Z predZ c :=
  fun n τ hn _ hτ => h n τ hn hτ

/-- **`MixingHoeffding` is the bounded predicate at every horizon.**  The unbounded hypothesis holds
iff the bounded one holds at every `N`: the forward direction drops `n ≤ N`
(`mixingHoeffdingTo_of_mixingHoeffding`), and the converse instantiates at `N := n` via `le_rfl`. -/
theorem mixingHoeffding_iff_forall_mixingHoeffdingTo (μ : Measure (ℕ → X))
    (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) :
    MixingHoeffding μ Z predZ c ↔ ∀ N, MixingHoeffdingTo N μ Z predZ c :=
  ⟨fun h N => mixingHoeffdingTo_of_mixingHoeffding N μ Z predZ c h,
    fun h n τ hn hτ => h n n τ hn le_rfl hτ⟩

end MixingHoeffding
