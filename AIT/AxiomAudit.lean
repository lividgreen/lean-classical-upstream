module

public import AIT.AlgorithmicProbability
public import AIT.CodingTheorem
public import AIT.CodingTheoremBitwise
public import AIT.CodingTheoremDecoder
public import AIT.EliasBound
public import AIT.KolmogorovBitlen
public import AIT.KolmogorovComplexity
public import AIT.KolmogorovTimeBounded
public import AIT.KraftChaitin
public import AIT.KraftMinimality
public import AIT.PrefixComplexity
public import AIT.PrefixCounting
public import AIT.PrefixInvarianceKB
public import AIT.PrefixMachine
public import AIT.PrefixMachinePrimrec
public import AIT.PrefixModelCost
public import AIT.PrefixPairKB
public import AIT.StructureFunction


/-!
# Axiom audit for the `AIT` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

-- The local prefix-freeness predicate on bit-strings is Mathlib's `IsPrefixFree` at the binary
-- alphabet: the bridge through which the two Kraft-layer theorems are Mathlib's.
/-- info: 'PrefixMachine.prefixFree_iff_isPrefixFree' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.prefixFree_iff_isPrefixFree

-- The prefix-free-ification `pfy`'s domain, read as bit-strings, contains no member a proper
-- prefix of another: the standard greedy-by-stage construction of a prefix machine.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.pfy_prefixFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.pfy_prefixFree

-- `pfy` is partial recursive, uniformly in the machine: a bit-string layer over `natToBits`,
-- `foldStep`, `newlyHalting` and `acceptedList`, closing the boundary `pfy`'s own definition flags.
/-- info: 'PrefixMachine.pfy_partrec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.pfy_partrec

-- The prefix complexity `KB` (over the universal prefix machine `pfy`) is additively below the
-- additive complexity `KE`: hardcode a datum-free guard, halting on input `0` alone.
/-- info: 'PrefixMachine.KB_le_KE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_KE

-- `KB`'s counting bound: at most finitely many naturals are describable within a fixed budget.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.setOf_KB_le_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.setOf_KB_le_finite

-- `KB` is a semimeasure: `∑ₓ 2⁻ᴷᴮ⁽ˣ⁾ ≤ 1`, the double sum over machines and their prefix-free
-- arguments bounded by `kraft_KP_E` and by Kraft over each prefix-free domain.
/-- info: 'PrefixMachine.kraft_KB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.kraft_KB

-- The algorithmic probability `QB`: the shortest description is one term of its Kraft sum, so
-- `2⁻ᴷᴮ⁽ˣ⁾ ≤ QB x`.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.two_pow_neg_KB_le_QB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.two_pow_neg_KB_le_QB

-- `QB` is a semimeasure: `∑ₓ QB x ≤ 1`.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.tsum_QB_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.tsum_QB_le_one

-- `QB` is lower-semicomputable: a computable, monotone dyadic approximation rising to it from
-- below, over the bit-string layer's computability.
/-- info: 'PrefixMachine.QB_lsc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.QB_lsc

-- Time-bounded Kolmogorov complexity: on Mathlib's `Code`, the resource
-- hierarchy `K ≤ K_t` (`K_le_K_t`), `K_t` antitone in the time budget (`K_t_antitone`), and
-- `K_t = K` for all sufficiently large budgets (`K_t_eventually`). These live in `namespace
-- KolmogorovComplexity` (the file is `KolmogorovTimeBounded.lean`).
set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.K_le_K_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_le_K_t

set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.K_t_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_t_antitone

set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.K_t_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_t_eventually

-- Prefix-free Kolmogorov complexity `KP` is a SEMIMEASURE: the universal
-- a-priori / Solomonoff–Levin bound `∑ₓ 2⁻ᴷᴾ⁽ˣ⁾ ≤ 1` (`kraft_KP`, via Mathlib's Kraft route +
-- the injective least-index `K`), and the prior `w(R') = 2⁻ᴷᴾ⁽ᵉⁿᶜᵒᵈᵉ ᴿ'⁾` as a
-- semimeasure over any encodable rule class (`kraft_prior`).
/-- info: 'PrefixComplexity.kraft_KP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixComplexity.kraft_KP

set_option linter.style.longLine false in
/-- info: 'PrefixComplexity.kraft_prior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixComplexity.kraft_prior

-- Uncomputability of `KP` — the Kleene-`fixed_point₂` Berry argument (mirrors
-- `K_bitlen_not_computable`); a sanity follow-on to the semimeasure headline.
set_option linter.style.longLine false in
/-- info: 'PrefixComplexity.KP_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixComplexity.KP_not_computable

-- Base Kolmogorov complexity (`AIT/KolmogorovComplexity.lean`): unboundedness of `K`
-- (`K_unbounded`) and the headline uncomputability of `K` (`K_not_computable`).
set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.K_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_unbounded

set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.K_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_not_computable

-- Bit-length Kolmogorov complexity (`AIT/KolmogorovBitlen.lean`, namespace
-- `KolmogorovComplexity`): uncomputability of the bit-length complexity
-- (`K_bitlen_not_computable`).
set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.K_bitlen_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_bitlen_not_computable

-- Kolmogorov structure function, the 45° / geometric lower bound on the additive carrier.
-- Two-part description (per model) `KE_le_of_model`; the four
-- targets: antitone `structFn_antitone`, singleton collapse `structFn_singleton`, the 45° slice
-- `KE_le_structFn` (`KE x ≤ α + c₁·h_x(α) + c₂`, `c₁ = 15 + elen dbl`), and the lower-bound form
-- `structFn_ge`. `Classical.choice` is genuinely used (`extractor`/`mkSingleton` from
-- universality).
set_option linter.style.longLine false in
/-- info: 'StructureFunction.KE_le_of_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructureFunction.KE_le_of_model

set_option linter.style.longLine false in
/-- info: 'StructureFunction.structFn_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructureFunction.structFn_antitone

set_option linter.style.longLine false in
/-- info: 'StructureFunction.structFn_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructureFunction.structFn_singleton

set_option linter.style.longLine false in
/-- info: 'StructureFunction.KE_le_structFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructureFunction.KE_le_structFn

set_option linter.style.longLine false in
/-- info: 'StructureFunction.structFn_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructureFunction.structFn_ge

-- The coding theorem with a logarithmic loss: for a lower-semicomputable semimeasure, a decoder
-- built from the level-`k` request/firing search over the approximation's own witness, its
-- `gammaCode`/`bitsFixed` description read off the requester's rank among the firings.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.coding_theorem_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.coding_theorem_weak

-- The instance of the coding theorem with a logarithmic loss at the algorithmic probability `QB`.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.coding_theorem_weak_QB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.coding_theorem_weak_QB

-- The online Kraft–Chaitin assignment's own capstone: the words it ever assigns, over the whole
-- history of a mass-respecting request stream, are pairwise prefix-free.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.kcWord_prefixFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.kcWord_prefixFree

-- Levin's coding theorem's request-stream budget: an improving step's own level, plus a silent
-- step's own index, both shifted by two, keep the online Kraft–Chaitin partial sums at most one.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.levinReq_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.levinReq_mass

-- Levin's coding theorem, the `O(1)` form: on the prefix machine every lower-semicomputable
-- semimeasure is an ideal code up to an additive constant, via the online Kraft–Chaitin decoder.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.coding_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.coding_theorem

-- The instance of Levin's coding theorem at the algorithmic probability `QB`.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.coding_theorem_QB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.coding_theorem_QB

-- Both directions at `QB`: with `two_pow_neg_KB_le_QB`, `QB` and `2 ^ (-KB)` agree up to a
-- multiplicative constant.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.QB_le_two_pow_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.QB_le_two_pow_mul

-- The coding theorem in multiplicative form, at a general lower-semicomputable semimeasure.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.coding_theorem_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.coding_theorem_mul

-- `QB`'s universality: it dominates every lower-semicomputable semimeasure up to a constant
-- factor — a universal (maximal) lower-semicomputable semimeasure, never "the" one.
/-- info: 'PrefixMachine.QB_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.QB_universal

-- The joint-satisfiability witness for `QB_universal`'s hypotheses: the point mass at `0`.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.QB_universal_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.QB_universal_nonvacuous

-- Prefix complexity's minimality: an upper-semicomputable `f` with `KB ≤ f + c` for some `c` iff
-- its Kraft weight is summable.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.KB_le_add_of_upperSemicomputable_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_add_of_upperSemicomputable_summable

-- The joint-satisfiability witness for the minimality lemma's two hypotheses, at twice the
-- bit-length.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.KB_le_add_of_upperSemicomputable_summable_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_add_of_upperSemicomputable_summable_nonvacuous

-- The converse half: `KB ≤ f + c` for some `c` forces `f`'s Kraft weight to be summable.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.summable_of_KB_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.summable_of_KB_le_add

-- Both halves of the minimality lemma, as one `iff`, at an upper-semicomputable `f`.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.KB_le_add_iff_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_add_iff_summable

-- The plain bit-length `K_bitlen` is upper-semicomputable, by a staged least-index search.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.upperSemicomputable_K_bitlen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.upperSemicomputable_K_bitlen

-- The first additive form between `KB` and `K_bitlen` is exactly the plain Kraft weight's
-- summability — not decided here in either direction.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.KB_le_K_bitlen_add_iff_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_K_bitlen_add_iff_summable

-- A second proof of `PrefixMachine.KB_le_two_mul_size`, through the coding theorem's minimality.
set_option linter.style.longLine false in
/-- info: 'PrefixMachine.KB_le_two_mul_size'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_two_mul_size'

/-! ## `KB`'s invariance under computable maps (`AIT/PrefixInvarianceKB.lean`)

The universal prefix machine `univPrefix`, its own halting domain prefix-free, and the invariance
bound `KB_map_le` it carries, a corollary of the partial-map generalization
`KB_partial_map_le`. -/

set_option linter.style.longLine false in
/-- info: 'PrefixMachine.prefixFree_univPrefix_dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.prefixFree_univPrefix_dom

set_option linter.style.longLine false in
/-- info: 'PrefixMachine.KB_partial_map_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_partial_map_le

/-- info: 'PrefixMachine.KB_map_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_map_le

/-- info: 'PrefixMachine.KB_pair_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_pair_le

set_option linter.style.longLine false in
/-- info: 'PrefixMachine.prefixFree_eliasDecoder_dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.prefixFree_eliasDecoder_dom

set_option linter.style.longLine false in
/-- info: 'PrefixMachine.KB_le_size_add_two_mul_size_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_size_add_two_mul_size_size

set_option linter.style.longLine false in
/-- info: 'PrefixMachine.KB_le_two_mul_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_two_mul_size

set_option linter.style.longLine false in
/-- info: 'PrefixMachine.KB_le_K_bitlen_add_two_mul_size_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_K_bitlen_add_two_mul_size_of

set_option linter.style.longLine false in
/-- info: 'PrefixMachine.KB_le_K_bitlen_add_two_mul_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_K_bitlen_add_two_mul_size

/-- info: 'PrefixMachine.KB_le_KP_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_KP_of

/-- info: 'PrefixMachine.KB_le_KP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_KP

/-! ## Counting bounds on `KB` and `K_bitlen`, and `KB`'s non-computability
(`AIT/PrefixCounting.lean`)

The counting bound `kraft_KB` buys on `KB`, the same constant on `K_bitlen` by injectivity instead,
and `KB`'s non-computability via the already-proved partial-map invariance, no fixed point
needed. -/

set_option linter.style.longLine false in
/-- info: 'PrefixMachine.finset_card_KB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.finset_card_KB_le

/-- info: 'PrefixMachine.card_KB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.card_KB_le

set_option linter.style.longLine false in
/-- info: 'PrefixMachine.finset_card_K_bitlen_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.finset_card_K_bitlen_le

set_option linter.style.longLine false in
/-- info: 'PrefixMachine.card_K_bitlen_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.card_K_bitlen_le

set_option linter.style.longLine false in
/-- info: 'PrefixMachine.KB_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_not_computable
