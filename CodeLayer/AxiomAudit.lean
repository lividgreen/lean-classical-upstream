module

public import CodeLayer.AdditiveComplexity
public import CodeLayer.BinaryConstant
public import CodeLayer.BinaryKraft
public import CodeLayer.BitStringPrimrec
public import CodeLayer.Code.BitGates
public import CodeLayer.PolyTime
public import CodeLayer.PrefixInvariance
public import CodeLayer.PriorNormalization
public import CodeLayer.TimeCost


/-!
# Axiom audit for the `CodeLayer` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

-- The serialization of a program is a prefix code: it parses uniquely, so distinct programs have
-- distinct bit-strings. Pure structural induction on the AST — no choice, and no `Quot.sound`.
/-- info: 'AdditiveComplexity.E_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.E_injective

-- Prefix codes are uniquely decodable, so McMillan's counting argument prices the program
-- lengths: the weights `2 ^ (-elen c)` sum to at most one over ALL programs at once.
set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.kraft_KP_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.kraft_KP_E

-- The object-indexed semimeasure: reindexing `kraft_KP_E` along `x ↦ minCode x` (each value's own
-- shortest program) turns the program-indexed Kraft sum into one over the naturals themselves.
set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.kraft_KE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.kraft_KE

-- The supply side of the incompressibility method: a budget of `L` bits describes at most
-- `2 ^ (L + 1)` naturals, because distinct values need distinct shortest programs and there are
-- fewer than `2 ^ (L + 1)` bit-strings of length at most `L`. Choosing a shortest program per value
-- is the classical step.
set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.card_KE_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.card_KE_le

-- The same count at `2 ^ L`, by Kraft's inequality for `KE` (`kraft_KE`) instead of by counting
-- bit-strings: each value weighs at least `2 ^ (-L)` in a series bounded by one.
set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.card_KE_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.card_KE_le_two_pow

-- Additive AST complexity `KE` (the two-machine-invariance core): the additive
-- program-length laws the `encodeCode` index measure cannot give — subadditivity
-- `KE (Nat.pair x y) ≤ KE x + KE y + 3` (`KE_subadditive`), the composition bound (`KE_comp_le`),
-- and the time-bounded resource step `KE ≤ KE_t` (`KE_le_KE_t`).
set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.KE_subadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.KE_subadditive

set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.KE_comp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.KE_comp_le

set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.KE_le_KE_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.KE_le_KE_t

-- The length-efficient binary constant `bconst`:
-- correct (`eval_bconst`) with additive length `O(Nat.size n)` (`elen_bconst_le`) — the
-- `Θ(n)`-vs-`O(log)` fix over `Code.const`. `Classical.choice` is genuinely used (the doubling code
-- `dbl` is extracted from universality via `Classical.choose`).
set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.eval_bconst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.eval_bconst

set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.elen_bconst_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.elen_bconst_le

-- Payoffs: a description-length bound `S_T ≤ r + O(log n)` via the binary `bconst`
-- (`prop_2_2_core`) and the multiplicative-optimality model-bridge (`KE x ≤ elen d +
-- O(log p) + c`, `invariance_general`).
set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.prop_2_2_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.prop_2_2_core

set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.invariance_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.invariance_general

-- Two-machine invariance of the additive prior measure.
-- `KE_interp_le` — the ADDITIVE compose-method bound `KE (I⟦x⟧) ≤ KE x + elen I + 3` (the index
-- measure `KP` is walled by `encodeCode`'s quadratic pairing; the general-method case is the
-- κ-multiplicative `invariance_general` above). `prior_weight_machine_indep_compose` — the
-- machine-independence of the `2^{−KE}` prior weight up to a fixed `2^{−O(1)}` factor.
set_option linter.style.longLine false in
/-- info: 'PrefixInvariance.KE_interp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixInvariance.KE_interp_le

set_option linter.style.longLine false in
/-- info: 'PrefixInvariance.prior_weight_machine_indep_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixInvariance.prior_weight_machine_indep_compose

-- The native sequential-time cost (`CodeLayer/TimeCost.lean`) and its `prec` bound.
-- `eval_eq_val`: value-agreement — on the rfind'-free fragment the cost's value component IS
-- `eval`, so the cost carries NO value cap (the contrast with `evaln`). `tc_prec_le`: the generic
-- engine — a uniform per-step bound `B` gives `prec` a LINEAR, magnitude-independent step count.
/-- info: 'TimeCost.eval_eq_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.eval_eq_val

/-- info: 'TimeCost.tc_prec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.tc_prec_le

-- The native SPACE cost — the maximum intermediate bitlength (`Nat.size`), companion to `tc`.
-- `spaceCost_prec_le`: the Capacity-Bounded Evaluation crux — where `tc_prec_le` is a SUM linear in
-- the iteration count, the space bound is a `max` INDEPENDENT of it. Under a per-step workspace
-- bound `S` taken relative to a small accumulator (the satisfiable form — a literal
-- `∀ x, spaceCost cg x ≤ S` cannot hold, space grows with input bitlength) and an
-- accumulator-bitlength bound `S`, the whole `prec` stays `≤ max (spaceCost cf a) S`. This is the
-- poly-space-workspace regime a bounded checker lives in — the same loop on which `tc` is
-- astronomically large.
/-- info: 'TimeCost.spaceCost_prec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.spaceCost_prec_le

-- The `PolyTime` predicate and its closure toolkit (`CodeLayer/PolyTime.lean`), downstream
-- infra for bounding a concrete algorithm's native `tc`. `PolyTime` bundles an rfind'-free witness,
-- a poly-in-input-bit-length step count, and a poly output bit-length (the last clause is required
-- for composition to close). `polyTime_comp` — closure under composition (its proof genuinely
-- consumes the inner map's output-size clause, since the outer code's cost is measured against the
-- inner OUTPUT bit-length). `polyTime_prec` — the bounded-recursion / loop-cost closure via
-- `tc_prec_le'`, with the accumulator-poly and iteration-count premises explicit. `PolyTime` (a
-- def) is even choice-free.
/-- info: 'TimeCost.PolyTime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.PolyTime

/-- info: 'TimeCost.polyTime_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.polyTime_comp

/-- info: 'TimeCost.polyTime_prec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.polyTime_prec

-- `PolyTime` validation — the `polyTime_prec` `hiter` blocker, the repaired loop closure, and a
-- fully-discharged worked example (`CodeLayer/PolyTime.lean`). `unpair_snd_not_polyBounded` — a raw
-- second-projection slot is NOT poly-bounded in the input bit-length (exponential family
-- `⟨0, 2^j⟩`), so `polyTime_prec`'s `hiter` cannot be discharged for a genuine loop.
-- `polyTime_loop` — the usable bounded-recursion closure where the iteration COUNT is a poly-bit
-- VALUE function of the ACTUAL input (`hCval : PolyBounded count`), not a raw slot; realized as
-- `comp (prec cf cg) shaper` and bounded via `tc_prec_le'`. `polyTime_loop_worked_example` — a
-- 3-iteration loop with a genuinely non-constant per-step cost (nested inner loop over the index,
-- so only `tc_prec_le'` applies) and a scaling poly-bit accumulator, PolyTime with every premise
-- discharged concretely.
set_option linter.style.longLine false in
/-- info: 'TimeCost.unpair_snd_not_polyBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.unpair_snd_not_polyBounded

/-- info: 'TimeCost.polyTime_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.polyTime_loop

set_option linter.style.longLine false in
/-- info: 'TimeCost.polyTime_loop_worked_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.polyTime_loop_worked_example

-- The inner scan primitives of the greedy 1-DL consistency solver
-- (`Learning/DecisionListSolver.lean`). THE FINDING: the native `tc` makes value-arithmetic
-- (general `=`, `isZero`, `add`) value-linear, so the scan must use a BIT-LOGIC gate library
-- (binary features/labels) and avoid label equality (track `sawZero`/`sawOne` bits instead).
-- `val_cAnd`/`val_cEqBit` — the gate semantics; each gate is bit-closed and `O(1)`-`tc` on bits.
-- `val_cPurity` — the purity primitive `val` law (loop = iterated carried-suffix step).
-- `purity_correct` — the scan realises the covered-label fold over `zip msks exs`.
-- `purity_is_pure_iff`/`purity_common_label`/`purity_saw_any` — the 3-field verdict
-- `⟨isPure, ⟨commonLabel, sawAny⟩⟩` reads out as "isPure iff not both a covered 0-label and covered
-- 1-label", "commonLabel = sawOne", and "sawAny ≠ 0 iff the literal covers ≥1 remaining example"
-- (the covering bit that stops a vacuous pure literal stalling greedy). `polyTime_c_scan` — the
-- scan loop is `PolyTime` via `polyTime_loop`: `rfind'`-freeness, the shaper `PolyTime`s, the base
-- cost, and the accumulator-size bound (`polyBounded_acc`) are all discharged; the WF/bit residuals
-- (count poly-bit `hCval` from `readM_le_size`; the per-visited-step cost bound) are threaded as
-- premises exactly as `polyTime_peel` threads its index bound.
/-- info: 'BitGates.val_cAnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BitGates.val_cAnd

/-- info: 'BitGates.val_cEqBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BitGates.val_cEqBit

-- Binary Kraft–McMillan, the shared arithmetic (`CodeLayer/BinaryKraft.lean`): Mathlib's inequality
-- specialized to the binary alphabet and reindexed along an injective code, finite
-- (`indexed_finset_sum_le_one`) and countable (`indexed_tsum_le_one`). Both the universal
-- prior and the program-length side (`AdditiveComplexity.kraft_KP_E`) consume these.
set_option linter.style.longLine false in
/-- info: 'BinaryKraft.indexed_finset_sum_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BinaryKraft.indexed_finset_sum_le_one

set_option linter.style.longLine false in
/-- info: 'BinaryKraft.indexed_tsum_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BinaryKraft.indexed_tsum_le_one

set_option linter.style.longLine false in
/-- info: 'PriorNormalization.prior_tsum_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PriorNormalization.prior_tsum_le_one

-- A poly-bounded function stays poly-bounded under an inner map of linearly bounded bit-length.
set_option linter.style.longLine false in
/-- info: 'TimeCost.PolyBounded.comp_size_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.PolyBounded.comp_size_le

-- The basic laws of the code layer's reusable surface: the base and composition clauses of `eval`,
-- uniqueness of the value a code computes, the small bit-length facts, the identity's failure to be
-- poly-bounded and the transfer of `PolyTime` along equal functions and to a domain, the constant
-- code's identification with Mathlib's tower, the remaining additive length laws, and the
-- complexity bounds `KE_le_const`, `KE_pair_le` and `KE_unbounded`.

/-- info: 'CodeEvalLaws.eval_comp' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms CodeEvalLaws.eval_comp

/-- info: 'CodeEvalLaws.eval_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms CodeEvalLaws.eval_zero

/-- info: 'CodeEvalLaws.eval_succ' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms CodeEvalLaws.eval_succ

/-- info: 'KolmogorovComplexity.Computes.unique' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.Computes.unique

set_option linter.style.longLine false in
/-- info: 'CodeSizeArith.size_succ_le_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodeSizeArith.size_succ_le_size

set_option linter.style.longLine false in
/-- info: 'CodeSizeArith.size_two_mul_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodeSizeArith.size_two_mul_succ_le

set_option linter.style.longLine false in
/-- info: 'CodeSizeArith.size_le_size_pair_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodeSizeArith.size_le_size_pair_left

set_option linter.style.longLine false in
/-- info: 'CodeSizeArith.size_le_size_pair_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodeSizeArith.size_le_size_pair_right

set_option linter.style.longLine false in
/-- info: 'TimeCost.not_polyBounded_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.not_polyBounded_id

/-- info: 'TimeCost.PolyTime.congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.PolyTime.congr

/-- info: 'TimeCost.PolyBounded.polyBoundedOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.PolyBounded.polyBoundedOn

/-- info: 'TimeCost.PolyTime.polyTimeOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.PolyTime.polyTimeOn

/-- info: 'TimeCost.constCode_eq_const' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.constCode_eq_const

/-- info: 'AdditiveComplexity.E_len_prec' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.E_len_prec

/-- info: 'AdditiveComplexity.E_len_rfind'' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.E_len_rfind'

/-- info: 'AdditiveComplexity.elen_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.elen_zero

/-- info: 'AdditiveComplexity.elen_succ' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.elen_succ

/-- info: 'AdditiveComplexity.elen_left' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.elen_left

/-- info: 'AdditiveComplexity.elen_right' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.elen_right

set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.KE_le_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.KE_le_const

set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.KE_pair_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.KE_pair_le

set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.KE_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.KE_unbounded
