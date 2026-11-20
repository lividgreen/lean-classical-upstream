# lean-classical-upstream

[![CI](https://github.com/lividgreen/lean-classical-upstream/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/lividgreen/lean-classical-upstream/actions/workflows/lean_action_ci.yml)
[![API docs](https://img.shields.io/badge/docs-API%20reference-4c1)](https://lividgreen.github.io/lean-classical-upstream/)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.23257423-blue)](https://doi.org/10.5281/zenodo.23257423)
[![Lean](https://img.shields.io/badge/Lean%204-Mathlib-black)](https://leanprover-community.github.io/)
[![License](https://img.shields.io/badge/license-Apache--2.0-lightgrey)](LICENSE)

**Classical theorems of algorithmic information theory, learning theory,
information theory, ergodic theory, realizability and combinatorics, machine-checked in Lean 4
with Mathlib.** Every statement here is one the literature already makes; what
this repository adds is its proof in Lean, under an axiom audit that the build
enforces.

## What it holds

Nine library roots, one per field, each built and imported on its own name:

- `AIT` — plain, time-bounded and prefix Kolmogorov complexity, algorithmic
  probability, Levin's coding theorem, the Kraft–Chaitin assignment and
  Chaitin's Ω, over one fixed universal machine.
- `ChaitinIncompleteness` — Chaitin's incompleteness theorem for first-order
  theories of arithmetic, in its plain and its additive form, and the finite
  stages of a progression of theories.
- `Learning` — the statistical-query model, two learning algorithms verified
  correct and polynomial-step, and the redundancy bound of a Bayes mixture.
- `AnytimeValid` — Ville's inequality for non-negative supermartingales.
- `ErgodicTheory` — the pointwise ergodic theorem, Hoeffding's bound for
  finite-state Markov chains, the columns of a local rule on the line, the
  classes of the elementary rules under reflection and complementation, and
  the number-conserving ones.
- `ShannonInfo` — entropy and mutual information on finite types, data
  processing and Fano's inequality.
- `Realizability` — the category of assemblies over Kleene's first algebra.
- `Combinatorics` — Erdős's condition for property B, the two-colourability of
  a family of finite sets.
- `CodeLayer` — what the others stand on: a self-delimiting serialization of
  Mathlib's `Nat.Partrec.Code`, binary Kraft bounds, and a step-counting cost
  model.

## Why it is worth having

Several of these theorems are, as far as a dated search of the Lean 4 libraries
found, proved in Lean here first, in the form stated:

- **Chaitin's incompleteness theorem under consistency alone**, for every
  `Δ₁`-axiomatized consistent extension of `𝗥₀` over Mathlib's universal
  machine, and in Chaitin's additive form, one constant for every theory plus
  the theory's own prefix complexity.
- **The statistical-query model as a model**: the dimension, an oracle
  simulated from samples, the version-space envelope, and parity's lower bound.
- **Learning algorithms verified for correctness and running time in one
  statement**: the conjunctions of Valiant and the decision lists of Rivest,
  on a cost model over Mathlib's codes.
- **Hoeffding's bound for a finite-state Markov chain** under a spectral gap.
- **The category of assemblies** over Kleene's first algebra: Cartesian closed,
  with finite coproducts.
- Time-bounded Kolmogorov complexity, the redundancy bound of a Bayes mixture,
  the columns of a local rule after Jen, and Lucas's criterion at the prime two.

The rest is proved in another Lean library too, and the table below says where;
it is here because other proofs are stated over it, in this repository or in a
library that requires it.

It serves two readers. One needs a result as a dependency: each root imports by
name, and every capstone's axiom set is asserted in the build. The other is
looking for a piece in a shape its natural home could take — Mathlib for
Ville's inequality and the binary Kraft bounds, a computer-science library for
the statistical-query model, a logic library for Chaitin's theorem — and the
labels below say which pieces are new in Lean.

## What is proved here

The short form of each result, grouped by library root. Every module's
docstring carries the full statement and its boundary.

### `AIT` — algorithmic information theory

- **Plain Kolmogorov complexity at two measures**
  (`KolmogorovComplexity.lean`, `KolmogorovBitlen.lean`): the least-index
  measure `K` is uncomputable by the recursion theorem, and so, separately, is
  the **bit-length** measure `Nat.size ∘ encode` (`K_bitlen_not_computable`);
  the second proof runs the argument again because `Nat.size` is not injective
  and the reduction from one measure to the other fails. Boundary: the
  invariance theorem between two machines is not stated at these two measures
  — Mathlib exposes a single fixed universal machine, and the classical bound
  needs two; at the additive measure it is `invariance_general`, additive for
  composition-style interpreters and multiplicative in general.

- **Time-bounded complexity** (`KolmogorovTimeBounded.lean`): `K_t` is at
  least `K`, antitone in the time bound, and equal to `K` from some bound on
  (`K_le_K_t`, `K_t_antitone`, `K_t_eventually`).
- **Levin's coding theorem on a universal prefix machine**
  (`PrefixMachine.lean`, `PrefixMachinePrimrec.lean`, `BitStringPrimrec.lean`,
  `AlgorithmicProbability.lean`, `CodingTheoremWeak.lean`,
  `CodingTheoremBitwise.lean`, `CodingTheoremDecoder.lean`,
  `KraftChaitin.lean`, `CodingTheorem.lean`): a description is a machine
  serialized by the self-delimiting `E` followed by a binary argument, the
  machine made prefix-free by stages (`pfy` — partial recursive uniformly in
  the machine, `pfy_partrec`, over a bit-string layer proved primitive
  recursive); the prefix complexity `KB` is Kraft-summable and below the
  additive `KE` by a constant; its algorithmic probability `QB` is
  lower-semicomputable (`QB_lsc`, a computable dyadic approximation rising to
  it). The theorem comes in two forms. With a logarithmic loss,
  `KB x ≤ k + 2·size k + C` whenever `2^{−k} < μ(x)`, for every
  lower-semicomputable semimeasure `μ` (`coding_theorem_weak`) — a
  self-delimiting header code (`gammaCode`), Markov's bound
  (`card_exceeds_lt`) and a partial recursive decoder with a prefix-free
  domain (`decodeFn`, `prefixFree_decodeFn_dom`), needing no online
  assignment. In Levin's `O(1)` form, `KB x ≤ k + C` (`coding_theorem`), with
  `2^{−KB} ≤ QB ≤ 2^C · 2^{−KB}` (`QB_le_two_pow_mul`): an online
  Kraft–Chaitin assignment carrying its invariant (`kcRun_invariant`) is fed
  the semimeasure's request stream, made total by dummy requests at its
  silent steps at the price of one bit. Each constant is a code's length,
  named rather than computed. Restated multiplicatively at a general
  semimeasure (`coding_theorem_mul`), the theorem makes `QB` a universal
  lower-semicomputable semimeasure — it dominates every one up to a constant
  factor (`QB_universal`), the hypotheses' joint satisfiability witnessed at
  the point mass (`QB_universal_nonvacuous`). Boundary: proved over one fixed
  universal prefix machine, where the classical text fixes its universal
  semimeasure as any maximal one — `QB` is *a* universal semimeasure, not a
  unique object.

- **The prefix machine's two textbook inequalities** (`PrefixPairKB.lean`,
  `PrefixModelCost.lean`): subadditivity, `KB (pair x y) ≤ KB x + KB y + c`
  (`KB_pair_le`) — one machine reads two descriptions back to back, the split
  unique because the universal machine's halting domain is prefix-free, and
  the pairing machine's own domain prefix-free in turn
  (`prefixFree_pairMachine_dom`), so no length header is paid — and the model
  cost, `KB x ≤ K_bitlen x + 2 · size (K_bitlen x) + c`
  (`KB_le_K_bitlen_add_two_mul_size`): a plain description made
  self-delimiting at the price of its own length written in the Elias code.
  Boundary: constants are code lengths, named rather than computed; no
  converse is proved here, and neither additive form between the plain and
  the prefix complexity is settled.

- **Counting bounds, and the prefix machine's own uncomputability**
  (`PrefixCounting.lean`): a description budget of `L` bits buys at most
  `2^L` naturals, in both currencies and for unrelated reasons — on the
  prefix machine `KB` from its Kraft inequality, each member of the budgeted
  set contributing at least `2^{−L}` to a series bounded by one
  (`finset_card_KB_le`, `card_KB_le`), and on the bit-length measure
  `K_bitlen`, where no Kraft inequality holds, from injectivity into the
  indices below `2^L` (`finset_card_K_bitlen_le`, `card_K_bitlen_le`). Each
  count is stated twice: the `Finset` form carries the bound unconditionally,
  the `Set.ncard` form takes its content from the matching finiteness lemma,
  `ncard` reading `0` on an infinite set. The counts quantify both Chaitin
  theorems' "all but finitely many". And `KB` is uncomputable
  (`KB_not_computable`) by Berry's argument through the
  partial-map invariance rather than a Kleene fixed point: the search for an
  `s` of complexity above `n` is a partial computable map, its domain
  populated by `KB_unbounded`, priced by `KB_partial_map_le` and then by the
  Elias bound. Boundary: uncomputable, not un-enumerable — the graph of
  "`KB(s) ≤ n`" is computably enumerable (`rePred_kleB`); `2^L` is the best
  the Kraft hypothesis gives, a flat semimeasure attaining it, and the strict
  count `KB`'s own totality would buy is not stated; the two counts share
  a constant and nothing else.

- **Prefix-complexity minimality** (`KraftMinimality.lean`): an
  upper-semicomputable `f` — `UpperSemicomputable`, a computable non-increasing
  stage sequence attaining `f` — has `KB ≤ f + c` for some `c` exactly when
  `∑ 2^(-f x)` is summable (`KB_le_add_iff_summable`), the coding theorem's
  minimality reading; the plain bit-length is upper-semicomputable
  (`upperSemicomputable_K_bitlen`), so the first additive form between the
  currencies is exactly the plain Kraft weight's summability
  (`KB_le_K_bitlen_add_iff_summable`), decided here in neither direction; the
  computable witness `2 * Nat.size` re-derives the Elias bound
  (`KB_le_two_mul_size'`).

- **The halting probability, and Chaitin's theorem on its approximations**
  (`HaltingProbability.lean`): the total algorithmic probability
  `haltingProb = ∑' x, QB x`, at most one (`haltingProb_le_one`), and the
  theorem stated at a pair rather than a binary expansion — there is a `c`
  such that whenever `m / 2 ^ n` is a lower approximation within `2 ^ (-n)`
  of it, `n ≤ KB (Nat.pair n m) + c`
  (`haltingProb_prefix_incompressible`), both hypotheses met at every `n`
  by the floor (`haltingProb_prefix_incompressible_nonvacuous`). A
  computable stage mass rising to the halting probability and a computable
  list of the values each stage reveals (`stageMass`, `revealedList`) meet
  two specifications (`HaltingMassSpec`, `HaltingRevealedSpec`), and the
  general statement over any pair meeting them (`haltingProb_prefix_incompressible_of`)
  searches for the least stage past the *shifted* threshold
  `m / 2 ^ n − 2 ^ (-n)`, takes the least value not yet revealed, and prices
  it by `KB_partial_map_le`. Boundary: the pair, not a prefix of the
  expansion; the constant existential; no randomness or irrationality
  stated; the proof is Shen, Uspensky and Vereshchagin's Theorem 100.

### `ChaitinIncompleteness` — Chaitin's theorem and a progression of theories

- **Chaitin's incompleteness theorem over bit-length complexity**
  (`ChaitinIncompleteness.lean`): for every `Δ₁`-axiomatized consistent
  extension of `𝗥₀` — consistency alone, no soundness — the theory proves
  "the bit-length complexity of `s` exceeds `n`" for no `n` at or above the
  bit-length of one fixed-point program (`chaitin_theorem`), so all but
  finitely many such true sentences are unprovable in it
  (`chaitin_true_unprovable`), the exceptions counted at `2^n` at the bound
  `n` (`card_K_bitlen_le`, below), and both hold for every recursively
  enumerable such extension by Craig's trick (`chaitin_theorem_of_RE`,
  `chaitin_true_unprovable_of_RE`); the abstract Berry bound (`chaitin_bound`)
  holds for any computably enumerable relation asserting only true lower
  bounds, and the sentences are Foundation's own Σ₁ representation, negated.
  The constant is a Kleene fixed point's length, named rather than computed.
  The additive form is on the prefix machine `KB` (`ChaitinPrefix.lean`,
  `SerializationParse.lean`, `KBEnumerable.lean`): one program `c₀` fixed for
  every theory, and `n < elen c₀ + KB(⌜e⌝)` at any program `e` enumerating
  the theory's provable sentences of this form — Chaitin's own constant, the
  theory's prefix complexity, under consistency alone (`chaitin_theorem_KB`,
  `chaitin_theorem_KB_RE`), with the true-and-unprovable family at that
  constant (`chaitin_true_unprovable_KB`) and an enumerator exhibited for every
  `Δ₁` theory (`exists_enumerator_chaitin_KB`); proved from two facts, each
  in its own module — a primitive-recursive parser of the serialization with
  its two-way specification (`eParserSpec`) and the computable enumeration of
  "`KB(s) ≤ n`" (`rePred_kleB`) — the hypotheses' joint satisfiability
  witnessed at `𝗣𝗔⁻` (`chaitin_theorem_KB_nonvacuous`). The abstract bound is
  also stated uniformly in a parameter (`ChaitinBoundParam.lean`,
  `chaitin_bound_KB_param`): for a program `E` read as a family of
  enumerators, one constant serves every parameter `z`, the family's claims
  at `z`, when all true, lying below the constant plus `KB z`. Boundary: the enumerator is of the
  theorems, not the axioms; the constant is named, not computed.
- **A progression of theories** (`TheoryProgression.lean`,
  `SentenceSelector`, `selectedSentence_true`, `selectedSentence_unprovable`,
  `progressionTheory_lt_succ`): given a rule selecting, at each theory, a
  sentence true in `ℕ` and unprovable in it, the chain that appends the
  selected sentence at every step — each selected sentence true and unprovable
  in the theory it extends, the chain strictly ascending. These are the finite
  stages of the progressions of Turing (1939) and Feferman (1962).

### `Learning` — the statistical-query model and verified learners

- **Statistical-query learning** — to our knowledge the first formalization of
  the model, beyond its dimension's definition, in any proof assistant
  (`SQObjects.lean`, `SQOracle.lean`, `SQEnvelope.lean`, `SQBounds.lean`): the
  statistical-query dimension as the size of a largest separated subfamily, a
  pigeonhole bound on the candidates that survive pruning, a *linear*
  version-space envelope under 2τ-identifiability by Szörényi's maximality
  argument (`subset_card_le_sqDim_of_ident`, `subset_polyBounded_of_ident`),
  that hypothesis shown necessary by a family of counterexamples, an envelope
  by a net that needs no identifiability (`version_space_net_envelope`), and
  parity's `2^n` lower bound on the dimension from the orthogonality of
  characters.

- **Blum's elimination learner over the parities**
  (`ParityElimination.lean`): on `cslib-frontier`'s mistake-bound model, the
  learner that keeps one equation per miss and predicts by a parity
  satisfying them has mistake bound at most `n` over the parities on `n`
  bits (`mistakeBound_learner_le`; Blum 1998,
  §4).

- **The dual Helly lower bound** (`DualHelly.lean`): on `cslib-frontier`'s
  mistake-bound model, a learner whose hypotheses after the realizable
  histories lie in a class `H` makes `m` mistakes on some realizable sequence
  whenever a set of examples that no member of `H` fits has every `m` of its
  examples fitted by one concept (`exists_mistakes_eq`, `le_mistakeBound`),
  and errs at every round against a concept that no member of `H` equals
  (`exists_stream_mistakes_eq`); the `K − 1` bound of Hanneke, Livni and
  Moran (2021, Remark 1), `K` the dual Helly number.

- **A learner verified correct and polynomial-step at once**
  (`DecisionListSolver.lean`): the step model carries a greedy decision-list
  learner verified **both correct and `poly(m,k)`-step** — we believe the
  first learning algorithm mechanically verified for correctness and
  complexity together. Built over it, a **version-space read-off**
  (`DecisionListPredictor.lean`): extending the instance by the query point
  labelled each way and asking the verified solver twice *classifies* the
  surviving candidates — none consistent, all agreeing at the query (the
  answer is forced and returned), or two disagreeing — with its own explicit
  step bound. A **second class** carries both theorems
  (`ConjunctionSolver.lean`, `ConjunctionPredictor.lean`), built in a separate
  module against the solver's public API alone, so the transfer between
  classes is exercised rather than asserted.

- **Bayes-mixture redundancy** (`BayesRedundancy.lean`): a prequential
  mixture's regret is at most the log prior weight of the truth
  (`mixture_regret_log`), and the Hellinger–log inequality turns that into a
  cumulative and an average Hellinger rate (`log_le_hellinger`,
  `cumulative_hellinger`, `average_hellinger_rate`), and into a bound on the
  number of steps at which the one-step error exceeds a tolerance
  (`errorTimes_card_le`).

### `AnytimeValid`, `ErgodicTheory`, `ShannonInfo`, `CodeLayer` — tail bounds, ergodic tools, information and codes

- **Ville's inequality** for non-negative supermartingales (`Ville.lean`) —
  the all-time tail bound anytime-valid inference is built on; absent from
  Mathlib (whose Doob maximal inequality is submartingale-only).
- **Information theory on finite types** (`FiniteInfoTheory.lean`): the
  data-processing inequality and Fano's inequality.
- **Guessing the bits of a string from a short message** (`BitGuessing.lean`):
  for a uniform string of `N` bits and a message about it from an alphabet
  `V`, guessers of each bit that read the message and the earlier bits alone
  (`Causal`) are right on at most `N/2 + √(N ln |V| / 2)` bits on average
  (`sum_hits_le`), by the chain rule for relative entropy, Pinsker's
  inequality at each bit and the Cauchy–Schwarz inequality.
- **Codes and their lengths** (`AdditiveComplexity.lean`,
  `BinaryConstant.lean`, `BinaryKraft.lean`, `PrefixComplexity.lean`): an
  additive self-delimiting program-length measure, a code of logarithmic
  length for a constant, the Kraft–McMillan inequality over binary index
  codes bridged from Mathlib's, and the Kraft inequality of prefix complexity,
  `∑ 2^{−KP} ≤ 1`.
- An integrated port of the **pointwise Birkhoff ergodic theorem** (from
  [lua-vr/pointwise-birkhoff](https://github.com/lua-vr/pointwise-birkhoff),
  Apache-2.0 — see NOTICE).
- A port of **`cslib-frontier`'s probability modules** behind Holenstein's
  Corollary 4.3 (`ShannonInfo/CslibFrontier/`, Apache-2.0 — see NOTICE): the
  frontier's own files with the renames this toolchain needs, kept under the
  frontier's namespaces and dropped for its modules once this package is on
  its toolchain.

- **Hoeffding for finite-state Markov chains under a spectral gap**
  (`MarkovHoeffding.lean`, `MixingHoeffding.lean`): every finite-state chain
  with an operator-norm spectral gap has a machine-checked trajectory law and
  satisfies the `MixingHoeffding` tail at it, at an explicit constant
  (`exists_mixingHoeffding_of_gap`, via the transfer-operator induction
  `transferIter_invariant`).
- **Driven systems** (`DrivenColumns.lean`): a sequence in a finite type whose
  next value is, from some step on, a fixed function of its value and of an
  eventually periodic input is eventually periodic
  (`eventuallyPeriodic_of_driven`).
- **Edge periods** (`EdgePeriods.lean`): a triangular system over the two-element
  field, cell `j` rewritten as itself plus a function of the cells below it,
  has every prefix purely periodic with least period a power of two, the period
  at width `m + 1` the period at `m` or twice it, and the cell `m` complemented
  over one period exactly at a doubling (`prefixPeriod_succ_eq_or_eq_two_mul`,
  `prefixPeriod_eq_two_pow`, `apply_add_prefixPeriod_of_eq_two_mul`): Rowland's
  statement at the right bijective rules (2006, §2, Lemmas 1 and 2) and Gravner
  and Griffeath's at the edge cellular automata (2012, §2.3).
- **Columns of a local rule on the line** (`LocalRuleColumns.lean`): for any
  local rule over a finite alphabet and any configuration of the line, the
  columns between two eventually periodic columns are eventually periodic
  (`eventuallyPeriodic_column_between`); rule `90` after `2^j` steps is the sum
  of the cells `2^j` away (`iterate_two_pow_step90`), and any linear rule after `2^j`
  steps is its own combination of the cells `2^j` away, the Frobenius identity in
  characteristic two (`iterate_two_pow_step_linear`); and from the single seed
  its column at cell `1` is not eventually periodic
  (`not_eventuallyPeriodic_column_step90_single_one`).
- **Pascal's triangle modulo two** (`PascalColumns.lean`): from the single seed,
  rule `90`'s value at cell `a − b` and step `a + b` is `C(a + b, a)` modulo two
  (`step_rule90_single_pascal`), zero at the other cells, and `1` exactly when
  `a` and `b` share no binary digit (`step_rule90_single_eq_one_iff`), by
  Lucas's criterion at the prime two (`choose_add_mod_two_eq_one_iff`). At
  `a = m`, `b = 2m` the criterion says `C(3m, m)` is odd exactly when `m` and
  `2m` share no binary digit (`choose_three_mul_mod_two_eq_one_iff`), which is
  to say when `m` has no two adjacent binary ones (`and_two_mul_eq_zero_iff`):
  the comment of entry A003714 of the OEIS.
- **Rule `22` in the sparse regime** (`Rule22Sparse.lean`): on a configuration
  whose set cells all lie in one coset of `4ℤ` (`SupportInCoset`), one step of
  rule `22` is the sum of the three cells (`step_rule22_eq_of_supportInCoset`),
  two steps are two steps of rule `90` and the image lies in one coset again
  (`iterate_step_rule22_two_eq_rule90`, `supportInCoset_iterate_step_rule90_two`),
  so the two orbits agree at every even time
  (`iterate_step_rule22_two_mul_eq_rule90`); from the single cell the row at
  time `2j` is rule `90`'s (`iterate_step_rule22_two_mul_single`), which is
  rule `90`'s row at time `j` with every distance doubled
  (`iterate_step_rule90_two_mul_single_even`,
  `iterate_step_rule90_two_mul_single_odd`): the closed form
  `Q_{2j} = (x² + x⁻²)^j` of Chan-López and Martín-Ruiz (2026, §3), with its
  induction step stated on every such configuration, and their odd row, the
  row at time `2j + 1` as the even row times `x⁻¹ + 1 + x`, the three-cell sum
  (`iterate_step_rule22_odd_single`). The coset hypothesis is load-bearing at
  the two cells `0` and `2` (`not_iterate_step_rule22_two_eq_rule90_off_coset`).
  On a configuration clear at the odd cells, two steps of rule `22` leave the odd
  cells clear and read at the even ones Jen's rule `146` (`rule146`) on the
  *reduction*, the configuration read at the even cells (`reduction`,
  `iterate_step_rule22_two_reduction`), at every even time
  (`iterate_step_rule22_two_mul_reduction`): Lemma 3.1 of Gravner and Griffeath
  (2010), there on states of isolated set cells with odd clear blocks between
  them. The hypothesis is load-bearing at the cells `0` and `1`
  (`not_iterate_step_rule22_two_reduction_off_even`).
- **Rule `18` creates no kinks** (`Rule18Kinks.lean`): a *kink* of a configuration
  over `ZMod 2` is a set cell whose next set cell lies at odd distance, the word
  `1 0^(2n) 1` (`kinkSet`, `kinks`; `kinkSet_finite` keeps the count honest on a
  finitely supported configuration), and one step of rule `18` never increases
  the number of kinks of a finitely supported configuration
  (`kinks_step_rule18_le`; Sabrié and Törmä 2023, §4, after Kůrka 2003, their
  statement on words and this its instance at the word padded with two clear
  cells on each side), proved for every local rule sending `000` and `010` to
  zero and at most one of `011` and `110` to one (`kinks_step_le`; its instance
  at the rules agreeing with rule `90` on the five neighbourhoods without two
  adjacent set cells is `kinks_step_le_of_agree`), by pairing each set cell
  of the image with a set cell of the configuration at distance one.
- **The parity of the kinks of rule `18`** (`Rule18Annihilation.lean`): on a
  finitely supported configuration the number of kinks has the parity of the
  support's width (`Rule18Kinks.kinks_mod_two_of_extremes`), so one step of rule
  `18`, which widens the support by one cell at each end, keeps it
  (`Rule18Kinks.kinks_step_rule18_mod_two`), and a configuration with no kink is
  of one parity (`Rule18Kinks.even_sub_of_kinks_eq_zero`); the kink
  annihilation that Sabrié and Törmä (2023, §4) state and credit to Jen (1990) is
  stated as `Rule18Kinks.JenAnnihilation` and proved in `Rule18Lift.lean`.
- **Jen's kink annihilation, through a lift to rule `90`**
  (`Rule18Lift.lean`): every finitely supported configuration has, after some
  number of steps of rule `18`, at most one kink (`Rule18Kinks.jenAnnihilation`).
  The lift of a configuration inserts one clear cell into
  the gap of each kink (`kinksBelow`, `lift`; the map Jen (1990) calls `G`), and
  `Rule18Kinks.jenAnnihilation_of_lift` proves `JenAnnihilation` from four
  statements, each proved (`liftConjugacy`, `leftmostKinkStep`,
  `rightmostKinkStep`, `liftKinkCells`): that the lift turns a step of rule `18`
  keeping the kink count into a step of rule `90` (`LiftConjugacy`), how the
  leftmost and the rightmost kink move in one step (`LeftmostKinkStep`,
  `RightmostKinkStep`, over `IsLeftmostKink` and `IsRightmostKink`), and where
  the lift puts those kinks and the configuration (`LiftKinkCells`). Were the
  count `c ≥ 2` kept for a power of two `T ≥ D (D + 1)` steps, `D` the lift's
  width, rule `90`'s doubling would split the lift into two copies, while the
  outermost kinks lie at least `D` inside the support's ends, which the order
  of the two kinks forbids. No published proof of the annihilation was found,
  and this proof is not Sabrié and Törmä's or Jen's.
- **The classes of the elementary rules** (`ElementaryRuleClasses.lean`): the
  elementary rule of a Wolfram number (`elementaryRule`), the numbers of the
  rule read right to left and of its conjugate under the exchange of `0` and
  `1` (`reflectNum`, `complementNum`, `elementaryRule_reflectNum`,
  `elementaryRule_complementNum`), two commuting involutions
  (`reflectNum_involutive`, `complementNum_involutive`,
  `reflectNum_complementNum_comm`) whose classes, counted by their least
  members, number 88 (`card_classes`),
  eight of size one, 36 of size two and 44 of size four (`card_classes_one`,
  `card_classes_two`, `card_classes_four`, `sum_classSize`): the count of Li
  and Packard (1990), by kernel decision.
- **Number conservation** (`NumberConservation.lean`): a local rule with a
  flux — an integer `J a b` for each pair of adjacent cells, zero at the empty
  pair, with `f a b c = b + J a b − J b c` (`IsFlux`) — keeps the number of
  ones of every finitely supported configuration of the line, whose image is
  again finitely supported (`ones_step_of_isFlux`, both hypotheses met at once
  in `ones_step_of_isFlux_nonvacuous`); rules 170, 184, 204, 226 and 240 have
  a flux (`exists_isFlux_of_mem`); and among the quiescent elementary rules
  those five are exactly the ones that conserve, and exactly the ones with a
  flux (`conserves_iff`, `exists_isFlux_iff`), the other 123 failing at one of
  four configurations of at most three cells (`counts_iff_mem`). The list is
  Boccara and Fukś's (1998), stated there on cyclic configurations; their
  later characterization by a sum of the rule's values (2002, Theorem 2.1),
  which they credit in general to Hattori and Takesue (1991), is equivalent
  to the flux form at three inputs and is not formalized here.
- **Cheng's necessity bound** (`ChengCCC.lean`): the misidentification and
  forgetting lower bounds of Cheng (2026), Theorem 4
  (`misid_lower_bound`, `forgetting_lower_bound`).

### `Realizability` — assemblies over Kleene's first algebra

- **The assembly category** (`Realizability.lean`, `RealizabilityCCC.lean`,
  `RealizabilityCoproduct.lean`, `RealizabilitySubobject.lean`): Cartesian
  closed (`exp_universal`), with finite coproducts and an initial object
  (`coprod_universal`, `initialAsm_isInitial`), and on the finite fragment a
  subobject classifier and equalizers (`classifier_universal`, `chi_unique`,
  `equalizer_universal`).

### `Combinatorics` — property B and binomial sums

- **Erdős's count of two-colourings** (`PropertyB.lean`): a family of finite
  sets of at least two points each, the sum of `2^(−|A_i|)` over which is at
  most one half, has property B, some set meeting every member and containing
  none (`PropertyB.of_sum_le`, Erdős 1963, Theorem 1); so at most `2^(p − 1)`
  sets of at least `p ≥ 2` points have it (`PropertyB.of_card_le_two_pow`).
  The three pairs of three points, at sum three quarters, and a single point
  have no property B (`PropertyB.not_three_pairs`, `PropertyB.not_singleton`).
- **The binomial sum bound** (`BinomialSum.lean`): for `1 ≤ k ≤ n`, the sum of
  the binomial coefficients `n choose i` over `i ≤ k` is at most `(e n / k)^k`
  (`Nat.sum_range_succ_choose_le_exp_mul_div_pow`), from each term's bound by
  `n^i / i!` and the exponential series.

## The labels, and where each result stands in Lean

Each module carries one of three labels.

- **Formalized** — first proved in Lean here in the form stated, as far as a
  search of the Lean 4 libraries we know found (the search is dated and scoped
  below); where another library proves a related form, the table names it and
  the next section says what differs.
- **Ported** — proved in Lean by someone else in a form that could not be used
  here, so proved again or re-fitted.
- **Duplicated** — proved in Lean by someone else in a form usable in
  principle, and proved here before we knew of it. A duplicated module is a
  candidate for removal in favour of the original once a bridge to it exists.

Helper modules — lemmas no one wrote down that a classical proof needs — carry
no label: they travel with the theorems whose proofs use them.

The algorithmic-information modules labelled duplicated stay, and why:
Milovanov's library, their original, builds with this package's toolchain but
is not on Lean's module system, and a module file cannot import a file that is
not a module; its theorems are also stated over every optimal prefix machine,
so ours would reach them only through bridge lemmas not yet written. They are
removed in its favour once both obstacles are gone.

The prior-art column was read at the sources on 2026-10-08: Milovanov's
[`kolmogorov-complexity-lean`](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean),
[`algorithmic-randomness`](https://github.com/cameronfreer/algorithmic-randomness) of Freer,
the Ville proofs in `athanor-ai/pythia`, `RemyDegenne/entropy-mdp` and
`Jiyuan-Tan/CausalSmith`, `Vilin97/lean-pool`, `leanprover/cslib`, and the
pinned Mathlib; Holden's [timed-kt](https://github.com/nickroci/timed-kt),
found later, was read on 2026-10-13, and the `Combinatorics` row's search for property B in Lean and Isabelle was made on 2026-11-08.
The whole column was read again on 2026-11-17, adding
[`cslib-frontier`](https://github.com/cslib-community/cslib-frontier),
Facebook Research's `atlas-lean`, `LeanMachineLearning/LMLExplore`,
`marcmorningstar/lean4-ergodic-theory`, `TOTBWF/lean-rz`, Wolfram Institute's
Rule30PrizeKit, `lhallee/rule30-open`, `DigitalEuan/GLM` and Mathlib's master;
a library dated after the module it names is marked "later than this module".
A label is a claim about that search, not about every Lean file
in existence; corrections are welcome as issues.

| Root | Module | Label | Statement, and its source | In Lean elsewhere |
|---|---|---|---|---|
| `CodeLayer` | `AdditiveComplexity`, `SerializationParse`, `PrefixInvariance` | helper | a self-delimiting serialization of `Nat.Partrec.Code` (a prefix code in Łukasiewicz's sense), its parser, and the invariance of its length | — |
| `CodeLayer` | `BinaryConstant` | helper | a code of length `O(log n)` for the constant `n` | — |
| `CodeLayer` | `BinaryKraft`, `PriorNormalization` | helper | Kraft–McMillan over binary index codes (Kraft 1949; McMillan 1956), bridged from Mathlib's | Mathlib's `InformationTheory/Coding` |
| `CodeLayer` | `Code.EvalLaws`, `BitStringPrimrec`, `Code.BitGates`, `Code.SizeArith`, `TimeCost`, `PolyTime` | helper | evaluation laws of Mathlib's codes at every constructor but the search, bit-string computability, Boolean gates as codes with their cores' certificates and costs public, bit-length arithmetic of pairing and successor, and a step-counting cost model over `Nat.Partrec.Code` with its polynomial-bound predicate and that predicate's normal form | — |
| `AIT` | `KolmogorovComplexity`, `KolmogorovBitlen` | duplicated | plain complexity on `Nat.Partrec.Code` and its uncomputability (Kolmogorov 1965; Shen, Uspensky and Vereshchagin, ch. 1) | Milovanov; `cslib-frontier`, over its own description methods, with the symmetry of information; `atlas-lean` |
| `AIT` | `KolmogorovTimeBounded` | formalized | time-bounded complexity, equal to plain complexity eventually (Li and Vitányi §7.1) | Levin's `Kt`, another time-bounded measure, in timed-kt, later than this module; the same eventual equality for any description method in `cslib-frontier`, later than this module |
| `AIT` | `PrefixMachine`, `PrefixMachinePrimrec`, `PrefixInvarianceKB`, `AlgorithmicProbability`, `CodingTheoremWeak`, `CodingTheoremBitwise`, `CodingTheoremDecoder`, `CodingTheorem`, `KraftChaitin`, `KraftMinimality`, `EliasBound`, `PrefixComplexity`, `PrefixCounting`, `PrefixPairKB`, `PrefixModelCost`, `HaltingProbability` | duplicated | prefix complexity, algorithmic probability, Levin's coding theorem, the Kraft–Chaitin assignment, the textbook inequalities and Chaitin's Ω (Chaitin 1975; Levin 1974; Shen, Uspensky and Vereshchagin, ch. 4 and Thm 100) | Milovanov, over an abstract optimal machine; Freer, a constructed prefix-free machine |
| `AIT` | `StructureFunction` | ported | the 45° slice `α + h_x(α) ≥ K(x) − O(1)` of the structure function (Vereshchagin and Vitányi 2004) | Milovanov, the same inequality with a logarithmic slack and slope one, incomparable with the constant slack here |
| `ChaitinIncompleteness` | `ChaitinIncompleteness`, `ChaitinPrefix`, `KBEnumerable`, `ChaitinBoundParam` | formalized | Chaitin's theorem for `Δ₁` consistent extensions of `𝗥₀`, in the plain and the additive form (Chaitin 1974) | Milovanov, for abstract sound systems; `cslib-frontier`, for computably enumerable sets of sentences, later than this module; Coquand, in Agda |
| `ChaitinIncompleteness` | `TheoryProgression` | formalized | finite stages of a progression of theories, each appending a true unprovable sentence (Turing 1939; Feferman 1962) | — |
| `Learning` | `SQObjects`, `SQOracle`, `SQEnvelope`, `SQBounds` | formalized | the statistical-query model: dimension, oracle simulated from samples, version-space envelope (Kearns 1998; Blum et al. 1994; Szörényi 2009) | `cslib-frontier`, the model with a correlational dimension, Szörényi's lower bound and the simulation by samples, later than this module; lean-pool, the dimension's definition |
| `Learning` | `ConjunctionSolver`, `ConjunctionPredictor`, `DecisionListData`, `DecisionListSolver`, `DecisionListPredictor` | formalized | the conjunctions of Valiant and the decision lists of Rivest, correct and polynomial-step (Valiant 1984; Rivest 1987) | — |
| `Learning` | `ParityElimination` | formalized | the elimination learner misses at most `n` times over the parities on `n` bits (Blum 1998, §4) | `cslib-frontier`, the halving learner's `log₂` bound, which gives the same count for a learner of another kind |
| `Learning` | `DualHelly` | formalized | a learner whose hypotheses lie in a class `H` misses at least `K − 1` times, `K` the dual Helly number of the concept class relative to `H` (Hanneke, Livni and Moran 2021, Remark 1, from the equivalence-query literature and Littlestone 1988) | — |
| `Learning` | `BayesRedundancy` | formalized | the Bayes-mixture redundancy bound and the Hellinger–log inequality | — |
| `AnytimeValid` | `Ville` | duplicated | Ville's inequality for non-negative supermartingales (Ville 1939) | `athanor-ai/pythia`, `RemyDegenne/entropy-mdp`, `Jiyuan-Tan/CausalSmith`, `atlas-lean`, `LMLExplore`; Freer for tree martingales; not in Mathlib |
| `ErgodicTheory` | `ErgodicTheory.Birkhoff.PointwiseBirkhoff` | ported | the pointwise ergodic theorem (Birkhoff 1931), vendored from [lua-vr/pointwise-birkhoff](https://github.com/lua-vr/pointwise-birkhoff) | that repository, `atlas-lean` and `marcmorningstar/lean4-ergodic-theory`; not in Mathlib, whose master has the maximal ergodic theorem |
| `ErgodicTheory` | `MarkovHoeffding`, `MixingHoeffding` | formalized | Hoeffding's bound for a finite-state Markov chain under a spectral gap (Fan, Jiang and Sun 2021) | — |
| `ErgodicTheory` | `DrivenColumns` | formalized | a finite system driven by an eventually periodic input is eventually periodic (Endrullis, Hendriks and Klop 2011) | — |
| `ErgodicTheory` | `EdgePeriods` | formalized | the prefix periods of a triangular system over the two-element field are powers of two, staying or doubling with the width, the doubled half the complement (Rowland 2006, §2, at every right bijective rule; Gravner and Griffeath 2012, §2.3, at the edge automata, crediting their 2010 paper) | rule `30`'s edge in Rule30PrizeKit, later than this module |
| `ErgodicTheory` | `LocalRuleColumns` | formalized | a local rule on the line: the columns between two eventually periodic columns are eventually periodic (Jen 1990, §3); rule `90` after `2^j` steps is the sum of the cells `2^j` away (Wolfram 1983), and any linear rule its own combination of the cells `2^j` away, the Frobenius identity in characteristic two (Martin, Odlyzko & Wolfram 1984, Eq. (A.4)), under which rule `60` reproduces every finite pattern (Amoroso & Cooper 1971); its column beside the single seed's center is not eventually periodic (Jen 1990, Proposition 2) | instances at rule `30` in Rule30PrizeKit and at rule `90`, from the single cell, in `lhallee/rule30-open`, both later than this module |
| `ErgodicTheory` | `Rule22Sparse` | formalized | rule `22` on a configuration supported in one coset of `4ℤ` is rule `90` at every even time, and from a single cell its row at time `2j` is `(x² + x⁻²)^j`, rule `90`'s row `j` with every distance doubled, and its row at time `2j + 1` is that row times `x⁻¹ + 1 + x` (Chan-López and Martín-Ruiz 2026, a preprint, whose induction step on the single-seed orbit is stated here on every such configuration); on a configuration clear at the odd cells two steps of rule `22` are rule `146` on the configuration read at the even cells (Gravner and Griffeath 2010, Lemma 3.1, proved there by a direct verification) | — |
| `ErgodicTheory` | `Rule18Kinks` | formalized | one step of rule `18` never increases the number of kinks, the words `1 0^(2n) 1`, of a finitely supported configuration (Sabrié and Törmä 2023, §4, after Kůrka 2003; stated there on words, with the proof read off a figure, and proved here through an anchor of each image cell for every rule agreeing with rule `90` off adjacent cells that sends at most one of `011` and `110` to one) | — |
| `ErgodicTheory` | `Rule18Annihilation` | formalized | the kinks of a finitely supported configuration have the parity of its support's width, kept by a step of rule `18`, and a configuration with no kink is of one parity; Jen's annihilation stated as a proposition, proved in `Rule18Lift` | Sabrié and Törmä (2023, §4) state the parity for stable words; no Lean statement was found |
| `ErgodicTheory` | `Rule18Lift` | formalized | Jen's kink annihilation for rule `18` (Sabrié and Törmä 2023, §4, crediting Jen 1990), proved through the lift that inserts a clear cell into each kink, the map Jen (1990) calls `G`, which turns a step keeping the kink count into a step of rule `90`; the proof is not theirs | no published proof of the annihilation was found |
| `ErgodicTheory` | `ElementaryRuleClasses` | formalized | the 256 elementary rules fall into 88 classes under reflection and complementation, of sizes one, two and four numbering 8, 36 and 44 (Li and Packard 1990; the numbering is Wolfram's, 1983) | the count of 88 in Rule30PrizeKit and `DigitalEuan/GLM`, later than this module, without the class sizes |
| `ErgodicTheory` | `NumberConservation` | formalized | among the quiescent elementary rules exactly rules 170, 184, 204, 226 and 240 conserve the number of ones, and a rule with a flux conserves it (Boccara and Fukś 1998, 2002, there on cyclic configurations; here on finitely supported ones) | — |
| `ErgodicTheory` | `PascalColumns` | formalized | rule `90` from a single cell is Pascal's triangle modulo two (Wolfram 1983), `C(a + b, a)` is odd exactly when `a` and `b` share no binary digit (Lucas 1878, at the prime two), and `C(3m, m)` is odd exactly when `m` has no two adjacent binary ones (a comment of entry A003714 of the OEIS) | Mathlib has Lucas's congruence and no statement at the prime two, nor the parity of `C(3m, m)`; Rule30PrizeKit has the prime-two criterion as digit inclusion, later than this module; Rocq has the rule-`60` form |
| `Realizability` | `Realizability`, `RealizabilityCCC`, `RealizabilityCoproduct`, `RealizabilitySubobject` | formalized | assemblies over Kleene's first algebra: Cartesian closed, finite coproducts, the finite fragment's subobject classifier (van Oosten 2008; Longley 1995) | lean-pool and Bauer: partial combinatory algebras; `TOTBWF/lean-rz`: an assembly class with identity and composition, no closure |
| `ShannonInfo` | `FiniteInfoTheory` | duplicated | finite entropy, mutual and conditional mutual information, data processing, Fano (Shannon 1948; Cover and Thomas) | the PFR project's entropy API; `cslib-frontier`, over probability mass functions in bits, with the tight Fano bound; `atlas-lean`; not in Mathlib, which has Kullback–Leibler divergence |
| `ShannonInfo` | `BitGuessing` | formalized | a message of `ln \|V\|` nats about `N` uniform bits lets guessers that read it and the earlier bits be right on at most `N/2 + √(N ln \|V\| / 2)` bits on average, by the chain rule for relative entropy and Pinsker's inequality; the bound for indexing with the string's other bits on one side as side information (Nayak 1999, Theorem 2.3, at every position; Bar-Yossef, Jayram, Krauthgamer and Kumar 2004, Lemma 2, at a uniform position with a window of preceding bits), here averaged over the positions with every earlier bit read, a form neither states | — |
| `ShannonInfo` | `ChengCCC` | formalized | the necessity bound of Cheng (2026), Theorem 4 | — |
| `ShannonInfo` | the modules under `ShannonInfo/CslibFrontier/` | ported | probability mass functions on finite types: conditioning, products, entropy, divergence with Pinsker's inequality, statistical distance, and Holenstein's Corollary 4.3 on a product conditioned on an event with side information (Holenstein 2009), vendored from [`cslib-frontier`](https://github.com/cslib-community/cslib-frontier) with the renames this toolchain needs | that library, on a newer Lean; the modules here are dropped for its own once this package is on its toolchain |
| `Combinatorics` | `PropertyB` | formalized | a family of sets of at least two points, the sum of `2^(−n)` over their sizes `n` at most one half, has property B (Erdős 1963, Theorem 1) | not in Mathlib; Isabelle's Archive of Formal Proofs has the uniform form, for families of sets of one size |
| `Combinatorics` | `BinomialSum` | formalized | the sum of the binomial coefficients `n choose i` over `i ≤ k` is at most `(e n / k)^k` for `1 ≤ k ≤ n`, a textbook bound | no statement of it was found in Mathlib at the pinned revision, by a search of its binomial bounds |

## Where the proofs here differ from the literature's

- **Chaitin's theorem under consistency alone, for first-order theories of a
  concrete arithmetic.** The prior Lean treatment states it for abstract formal
  systems under soundness, and the Agda one for a purpose-built machine. Here
  it is over Mathlib's universal machine, for every `Δ₁`-axiomatized
  consistent extension of `𝗥₀`, and in Chaitin's additive form — one constant
  for every theory plus the theory's own prefix complexity — which we have not
  found machine-checked elsewhere.
- **Levin's coding theorem over one fixed machine.** Milovanov proves it over
  an abstract optimal prefix machine; here the machine is built from the
  serialized codes and the theorem is proved over it, on an online
  Kraft–Chaitin assignment verified with its invariant.
- **The statistical-query model as a model.** When this module was written
  only the dimension's definition existed in Lean, and `cslib-frontier` has
  formalized the model since; here the oracle, the envelope and the learners are proved,
  and the cost model lets a learner be verified correct and polynomial-step in
  one statement rather than in a program logic beside the mathematics.
- **Assemblies.** Partial combinatory algebras exist in Lean; the category of
  assemblies over one does not, as far as we found.

## Verification standard

- No `sorry`, `admit`, or `native_decide`; standard axioms only
  (`propext`, `Classical.choice`, `Quot.sound`).
- **Build-enforced axiom hygiene**: 328 `#guard_msgs in #print axioms` guards
  assert each capstone's exact axiom set — most in an audit module per library
  root and the Birkhoff port's own, the rest in-file in the modules they
  certify; `lake build` fails on any drift.
- **CI-enforced whole-library audit**: every declaration of every library root
  is checked against the checked-in `forgive.yml` by
  [`forgive`](https://github.com/FormalizedFormalLogic/forgive) on each CI run.
  Reproduce it locally with `lake exe forgive <Root>` after a build.
- **Targeted imports and module-system code**: every module names exactly the
  Mathlib files it uses, the vendored Birkhoff port excepted, and every file is
  a Lean `module`.

## Building

Pinned toolchain (`lean-toolchain`, `lake-manifest.json`):

```bash
lake exe cache get
lake build CodeLayer AIT ChaitinIncompleteness Learning AnytimeValid ErgodicTheory Realizability ShannonInfo Combinatorics
```

As a dependency, with its nine library roots by field:

```toml
[[require]]
name = "classical_upstream"
git = "https://github.com/lividgreen/lean-classical-upstream"
rev = "<tag>"  -- pin to a tagged release
```

What a root costs to import: `CodeLayer`, `AnytimeValid`, `ErgodicTheory`,
`Realizability`, `ShannonInfo` and `Combinatorics` import no other root;
`Learning` and `AIT` import `CodeLayer`, and `Learning` and `ShannonInfo` import
[`cslib-frontier`](https://github.com/cslib-community/cslib-frontier) as well,
the only roots that need it; and `ChaitinIncompleteness` imports `AIT` and `CodeLayer`
with [Foundation](https://github.com/FormalizedFormalLogic/Foundation), the
only root that needs it.

## How this repository is maintained

This is a **curated snapshot** of a private development. Issues are welcome —
above all a prior formalization we missed, which changes a label. A module
labelled duplicated or ported is a standing invitation to bridge it to the
original and delete ours.

## Citation and license

See `CITATION.cff` — concept DOI
[10.5281/zenodo.23257423](https://doi.org/10.5281/zenodo.23257423)
always resolves to the latest archived version. For a specific tagged
version and its own version DOI, see the
[GitHub Releases page](https://github.com/lividgreen/lean-classical-upstream/releases)
and `CITATION.cff`. Code is Apache-2.0 (`LICENSE`); third-party attribution
in `NOTICE`. Developed by Mykola Palamarchuk (independent researcher), with
substantial AI assistance (Claude Code, Anthropic) under the author's direction
and review — every result is machine-checked by Lean.

The program these libraries belong to is described at
[www.livid.work/projects/reflective-subsystems](https://www.livid.work/projects/reflective-subsystems/).
