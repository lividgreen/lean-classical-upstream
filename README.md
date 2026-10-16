# lean-classical-upstream

[![CI](https://github.com/lividgreen/lean-classical-upstream/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/lividgreen/lean-classical-upstream/actions/workflows/lean_action_ci.yml)
[![API docs](https://img.shields.io/badge/docs-API%20reference-4c1)](https://lividgreen.github.io/lean-classical-upstream/)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.23257423-blue)](https://doi.org/10.5281/zenodo.23257423)
[![Lean](https://img.shields.io/badge/Lean%204-Mathlib-black)](https://leanprover-community.github.io/)
[![License](https://img.shields.io/badge/license-Apache--2.0-lightgrey)](LICENSE)

**Classical theorems of algorithmic information theory, learning theory,
information theory, ergodic theory and realizability, machine-checked in Lean 4
with Mathlib.** Every statement here is one the literature already makes; what
this repository adds is its proof in Lean, under an axiom audit that the build
enforces.

## What it holds

Eight library roots, one per field, each built and imported on its own name:

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
  witnessed at `𝗣𝗔⁻` (`chaitin_theorem_KB_nonvacuous`). Boundary: the enumerator is of the
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
- **Codes and their lengths** (`AdditiveComplexity.lean`,
  `BinaryConstant.lean`, `BinaryKraft.lean`, `PrefixComplexity.lean`): an
  additive self-delimiting program-length measure, a code of logarithmic
  length for a constant, the Kraft–McMillan inequality over binary index
  codes bridged from Mathlib's, and the Kraft inequality of prefix complexity,
  `∑ 2^{−KP} ≤ 1`.
- An integrated port of the **pointwise Birkhoff ergodic theorem** (from
  [lua-vr/pointwise-birkhoff](https://github.com/lua-vr/pointwise-birkhoff),
  Apache-2.0 — see NOTICE).

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
- **Columns of a local rule on the line** (`LocalRuleColumns.lean`): for any
  local rule over a finite alphabet and any configuration of the line, the
  columns between two eventually periodic columns are eventually periodic
  (`eventuallyPeriodic_column_between`); rule `90` after `2^j` steps is the sum
  of the cells `2^j` away (`iterate_two_pow_step90`); and from the single seed
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

The prior-art column was read at the sources on 2026-10-08: Milovanov's
[`kolmogorov-complexity-lean`](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean),
[`algorithmic-randomness`](https://github.com/cameronfreer/algorithmic-randomness) of Freer,
the Ville proofs in `athanor-ai/pythia`, `RemyDegenne/entropy-mdp` and
`Jiyuan-Tan/CausalSmith`, `Vilin97/lean-pool`, `leanprover/cslib`, and the
pinned Mathlib; Holden's [timed-kt](https://github.com/nickroci/timed-kt),
found later, was read on 2026-10-13. A label is a claim about that search, not about every Lean file
in existence; corrections are welcome as issues.

| Root | Module | Label | Statement, and its source | In Lean elsewhere |
|---|---|---|---|---|
| `CodeLayer` | `AdditiveComplexity`, `SerializationParse`, `PrefixInvariance` | helper | a self-delimiting serialization of `Nat.Partrec.Code` (a prefix code in Łukasiewicz's sense), its parser, and the invariance of its length | — |
| `CodeLayer` | `BinaryConstant` | helper | a code of length `O(log n)` for the constant `n` | — |
| `CodeLayer` | `BinaryKraft`, `PriorNormalization` | helper | Kraft–McMillan over binary index codes (Kraft 1949; McMillan 1956), bridged from Mathlib's | Mathlib's `InformationTheory/Coding` |
| `CodeLayer` | `Code.EvalLaws`, `BitStringPrimrec`, `Code.BitGates`, `Code.SizeArith`, `TimeCost`, `PolyTime` | helper | evaluation laws of Mathlib's codes, bit-string computability, Boolean gates as codes, and a step-counting cost model over `Nat.Partrec.Code` | — |
| `AIT` | `KolmogorovComplexity`, `KolmogorovBitlen` | duplicated | plain complexity on `Nat.Partrec.Code` and its uncomputability (Kolmogorov 1965; Shen, Uspensky and Vereshchagin, ch. 1) | Milovanov |
| `AIT` | `KolmogorovTimeBounded` | formalized | time-bounded complexity, equal to plain complexity eventually (Li and Vitányi §7.1) | Levin's `Kt`, another time-bounded measure, in timed-kt, later than this module |
| `AIT` | `PrefixMachine`, `PrefixMachinePrimrec`, `PrefixInvarianceKB`, `AlgorithmicProbability`, `CodingTheoremWeak`, `CodingTheoremBitwise`, `CodingTheoremDecoder`, `CodingTheorem`, `KraftChaitin`, `KraftMinimality`, `EliasBound`, `PrefixComplexity`, `PrefixCounting`, `PrefixPairKB`, `PrefixModelCost`, `HaltingProbability` | duplicated | prefix complexity, algorithmic probability, Levin's coding theorem, the Kraft–Chaitin assignment, the textbook inequalities and Chaitin's Ω (Chaitin 1975; Levin 1974; Shen, Uspensky and Vereshchagin, ch. 4 and Thm 100) | Milovanov, over an abstract optimal machine; Freer, a constructed prefix-free machine |
| `AIT` | `StructureFunction` | ported | the 45° slice `α + h_x(α) ≥ K(x) − O(1)` of the structure function (Vereshchagin and Vitányi 2004) | Milovanov, in the deficiency form with a logarithmic slack, a different statement of the same theory |
| `ChaitinIncompleteness` | `ChaitinIncompleteness`, `ChaitinPrefix`, `KBEnumerable` | formalized | Chaitin's theorem for `Δ₁` consistent extensions of `𝗥₀`, in the plain and the additive form (Chaitin 1974) | Milovanov, for abstract sound systems; Coquand, in Agda |
| `ChaitinIncompleteness` | `TheoryProgression` | formalized | finite stages of a progression of theories, each appending a true unprovable sentence (Turing 1939; Feferman 1962) | — |
| `Learning` | `SQObjects`, `SQOracle`, `SQEnvelope`, `SQBounds` | formalized | the statistical-query model: dimension, oracle simulated from samples, version-space envelope (Kearns 1998; Blum et al. 1994; Szörényi 2009) | lean-pool, the dimension's definition only |
| `Learning` | `ConjunctionSolver`, `ConjunctionPredictor`, `DecisionListData`, `DecisionListSolver`, `DecisionListPredictor` | formalized | the conjunctions of Valiant and the decision lists of Rivest, correct and polynomial-step (Valiant 1984; Rivest 1987) | — |
| `Learning` | `BayesRedundancy` | formalized | the Bayes-mixture redundancy bound and the Hellinger–log inequality | — |
| `AnytimeValid` | `Ville` | duplicated | Ville's inequality for non-negative supermartingales (Ville 1939) | `athanor-ai/pythia`, `RemyDegenne/entropy-mdp`, `Jiyuan-Tan/CausalSmith`; Freer for tree martingales; not in Mathlib |
| `ErgodicTheory` | `ErgodicTheory.Birkhoff.PointwiseBirkhoff` | ported | the pointwise ergodic theorem (Birkhoff 1931), vendored from [lua-vr/pointwise-birkhoff](https://github.com/lua-vr/pointwise-birkhoff) | that repository; not in Mathlib |
| `ErgodicTheory` | `MarkovHoeffding`, `MixingHoeffding` | formalized | Hoeffding's bound for a finite-state Markov chain under a spectral gap (Fan, Jiang and Sun 2021) | — |
| `ErgodicTheory` | `DrivenColumns` | formalized | a finite system driven by an eventually periodic input is eventually periodic (Endrullis, Hendriks and Klop 2011) | — |
| `ErgodicTheory` | `LocalRuleColumns` | formalized | a local rule on the line: the columns between two eventually periodic columns are eventually periodic (Jen 1990, §3); rule `90` after `2^j` steps is the sum of the cells `2^j` away (Wolfram 1983); its column beside the single seed's center is not eventually periodic (Jen 1990, Proposition 2) | — |
| `ErgodicTheory` | `ElementaryRuleClasses` | formalized | the 256 elementary rules fall into 88 classes under reflection and complementation, of sizes one, two and four numbering 8, 36 and 44 (Li and Packard 1990; the numbering is Wolfram's, 1983) | — |
| `ErgodicTheory` | `NumberConservation` | formalized | among the quiescent elementary rules exactly rules 170, 184, 204, 226 and 240 conserve the number of ones, and a rule with a flux conserves it (Boccara and Fukś 1998, 2002, there on cyclic configurations; here on finitely supported ones) | — |
| `ErgodicTheory` | `PascalColumns` | formalized | rule `90` from a single cell is Pascal's triangle modulo two (Wolfram 1983), `C(a + b, a)` is odd exactly when `a` and `b` share no binary digit (Lucas 1878, at the prime two), and `C(3m, m)` is odd exactly when `m` has no two adjacent binary ones (a comment of entry A003714 of the OEIS) | Mathlib has Lucas's congruence and no statement at the prime two, nor the parity of `C(3m, m)`; Rocq has the rule-`60` form |
| `Realizability` | `Realizability`, `RealizabilityCCC`, `RealizabilityCoproduct`, `RealizabilitySubobject` | formalized | assemblies over Kleene's first algebra: Cartesian closed, finite coproducts, the finite fragment's subobject classifier (van Oosten 2008; Longley 1995) | lean-pool and Bauer: partial combinatory algebras, no assemblies |
| `ShannonInfo` | `FiniteInfoTheory` | duplicated | finite entropy, mutual and conditional mutual information, data processing, Fano (Shannon 1948; Cover and Thomas) | the PFR project's entropy API, outside Mathlib |
| `ShannonInfo` | `ChengCCC` | formalized | the necessity bound of Cheng (2026), Theorem 4 | — |

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
- **The statistical-query model as a model.** Only the dimension's definition
  existed in Lean; here the oracle, the envelope and the learners are proved,
  and the cost model lets a learner be verified correct and polynomial-step in
  one statement rather than in a program logic beside the mathematics.
- **Assemblies.** Partial combinatory algebras exist in Lean; the category of
  assemblies over one does not, as far as we found.

## Verification standard

- No `sorry`, `admit`, or `native_decide`; standard axioms only
  (`propext`, `Classical.choice`, `Quot.sound`).
- **Build-enforced axiom hygiene**: 253 `#guard_msgs in #print axioms` guards
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
lake build CodeLayer AIT ChaitinIncompleteness Learning AnytimeValid ErgodicTheory Realizability ShannonInfo
```

As a dependency, with its eight library roots by field:

```toml
[[require]]
name = "classical_upstream"
git = "https://github.com/lividgreen/lean-classical-upstream"
rev = "<tag>"  -- pin to a tagged release
```

What a root costs to import: `CodeLayer`, `AnytimeValid`, `ErgodicTheory`,
`Realizability` and `ShannonInfo` import no other root; `Learning` and `AIT`
import `CodeLayer`; and `ChaitinIncompleteness` imports `AIT` and `CodeLayer`
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
