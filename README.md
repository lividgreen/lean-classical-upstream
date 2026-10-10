# lean-classical-upstream

[![CI](https://github.com/lividgreen/lean-classical-upstream/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/lividgreen/lean-classical-upstream/actions/workflows/lean_action_ci.yml)
[![API docs](https://img.shields.io/badge/docs-API%20reference-4c1)](https://lividgreen.github.io/lean-classical-upstream/)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.23257423-blue)](https://doi.org/10.5281/zenodo.23257423)
[![Lean](https://img.shields.io/badge/Lean%204-Mathlib-black)](https://leanprover-community.github.io/)
[![License](https://img.shields.io/badge/license-Apache--2.0-lightgrey)](LICENSE)

**Classical results, machine-checked in Lean 4 with their proofs: theorems the
literature already states, formalized here because a research library needed
them and found them missing, re-implemented, or stated in a form it could not
use.**

Everything in this repository has prior art — a paper or book that states it,
or another Lean library that proves it. What is new here is at most the
formalization, and the README says which: each module carries one of three
labels.

- **Formalized** — first proved in Lean here in the form stated, as far as a
  search of the Lean 4 libraries we know found (the search is dated and scoped
  in the table); where another library proves a related form, the table names
  it and the section on where the proofs differ says what is new.
  These are the pieces most worth upstreaming.
- **Ported** — proved in Lean by someone else in a form we could not use, so
  proved again or re-fitted here; the upstream question is open.
- **Duplicated** — proved in Lean by someone else in a form we could use in
  principle, re-implemented here before we knew of it. A duplicated module is a
  candidate for removal in favour of the original once a bridge exists, and it
  is kept only because a downstream proof is stated over it.

Helper modules — lemmas no one wrote down that a classical proof needs — carry
no label: they travel with the sentences whose proofs use them.

The research library this repository was split from is
[lean-algorithmic-learning-theory](https://github.com/lividgreen/lean-algorithmic-learning-theory),
which requires this package and holds the rest of the research beside the
radius-one rule space, which `lean-elementary-cellular-automata` holds and which
requires this package too. Nothing here imports either.

## Verification standard

- No `sorry`, `admit`, or `native_decide`; standard axioms only
  (`propext`, `Classical.choice`, `Quot.sound`).
- **Build-enforced axiom hygiene**: 249 `#guard_msgs in #print axioms` guards
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

## The modules, by library root

The prior-art column was read at the sources on 2026-10-08: Milovanov's
[kolmogorov-complexity-lean](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean),
Freer's [algorithmic-randomness](https://github.com/cameronfreer/algorithmic-randomness),
the Ville proofs in `athanor-ai/pythia`, `RemyDegenne/entropy-mdp` and
`Jiyuan-Tan/CausalSmith`, `Vilin97/lean-pool`, `leanprover/cslib`, and the
pinned Mathlib. A label is a claim about that search, not about every Lean file
in existence; corrections are welcome as issues.

| Root | Module | Label | Statement, and its source | In Lean elsewhere |
|---|---|---|---|---|
| `CodeLayer` | `AdditiveComplexity`, `SerializationParse`, `PrefixInvariance` | helper | a self-delimiting serialization of `Nat.Partrec.Code` (a prefix code in Łukasiewicz's sense), its parser, and the invariance of its length | — |
| `CodeLayer` | `BinaryConstant` | helper | a code of length `O(log n)` for the constant `n` | — |
| `CodeLayer` | `BinaryKraft`, `PriorNormalization` | helper | Kraft–McMillan over binary index codes (Kraft 1949; McMillan 1956), bridged from Mathlib's | Mathlib's `InformationTheory/Coding` |
| `CodeLayer` | `Code.EvalLaws`, `BitStringPrimrec`, `Code.BitGates`, `Code.SizeArith`, `TimeCost`, `PolyTime` | helper | evaluation laws of Mathlib's codes, bit-string computability, Boolean gates as codes, and a step-counting cost model over `Nat.Partrec.Code` | — |
| `AIT` | `KolmogorovComplexity`, `KolmogorovBitlen` | duplicated | plain complexity on `Nat.Partrec.Code` and its uncomputability (Kolmogorov 1965; Shen, Uspensky and Vereshchagin, ch. 1) | Milovanov |
| `AIT` | `KolmogorovTimeBounded` | formalized | time-bounded complexity, equal to plain complexity eventually (Li and Vitányi §7.1) | — |
| `AIT` | `PrefixMachine`, `PrefixInvarianceKB`, `AlgorithmicProbability`, `CodingTheoremWeak`, `CodingTheoremBitwise`, `CodingTheoremDecoder`, `CodingTheorem`, `KraftChaitin`, `KraftMinimality`, `EliasBound`, `PrefixComplexity`, `PrefixCounting`, `PrefixPairKB`, `PrefixModelCost`, `HaltingProbability` | duplicated | prefix complexity, algorithmic probability, Levin's coding theorem, the Kraft–Chaitin assignment, the textbook inequalities and Chaitin's Ω (Chaitin 1975; Levin 1974; Shen, Uspensky and Vereshchagin, ch. 4 and Thm 100) | Milovanov, over an abstract optimal machine; Freer, a constructed prefix-free machine |
| `AIT` | `StructureFunction` | duplicated, flagged | the 45° slice `α + h_x(α) ≥ K(x) − O(1)` (Vereshchagin and Vitányi 2004) | Milovanov, in the deficiency form with a logarithmic slack — not the same statement |
| `ChaitinIncompleteness` | `ChaitinIncompleteness`, `ChaitinPrefix`, `KBEnumerable` | formalized | Chaitin's theorem for `Δ₁` consistent extensions of `𝗥₀`, in the plain and the additive form (Chaitin 1974) | Milovanov, for abstract sound systems; Coquand, in Agda |
| `ChaitinIncompleteness` | `SelectorLadder` | formalized | finite stages of a progression of theories, each appending a true unprovable sentence (Turing 1939; Feferman 1962) | — |
| `Learning` | `SQObjects`, `SQOracle`, `SQEnvelope`, `SQBounds` | formalized | the statistical-query model: dimension, oracle simulated from samples, version-space envelope (Kearns 1998; Blum et al. 1994; Szörényi 2009) | lean-pool, the dimension's definition only |
| `Learning` | `ConjunctionSolver`, `ConjunctionPredictor`, `DecisionListData`, `DecisionListSolver`, `DecisionListPredictor` | formalized | Valiant's conjunctions and Rivest's decision lists, correct and polynomial-step (Valiant 1984; Rivest 1987) | — |
| `Learning` | `BayesRedundancy` | formalized | the Bayes-mixture redundancy bound and the Hellinger–log inequality | — |
| `AnytimeValid` | `Ville` | duplicated | Ville's inequality for non-negative supermartingales (Ville 1939) | pythia, entropy-mdp, CausalSmith; Freer for tree martingales; not in Mathlib |
| `ErgodicTheory` | `Birkhoff.PointwiseBirkhoff` | ported | the pointwise ergodic theorem (Birkhoff 1931), vendored from [lua-vr/pointwise-birkhoff](https://github.com/lua-vr/pointwise-birkhoff) | that repository; not in Mathlib |
| `ErgodicTheory` | `MarkovHoeffding`, `MixingHoeffding` | formalized | Hoeffding's bound for a finite-state Markov chain under a spectral gap (Fan, Jiang and Sun 2021) | — |
| `ErgodicTheory` | `DrivenColumns` | formalized | a finite system driven by an eventually periodic input is eventually periodic (Endrullis, Hendriks and Klop 2011) | — |
| `ErgodicTheory` | `LocalRuleColumns` | formalized | a local rule on the line: the columns between two eventually periodic columns are eventually periodic (Jen 1990, §3); rule `90` after `2^j` steps is the sum of the cells `2^j` away (Wolfram 1983); its column beside the single seed's center is not eventually periodic (Jen 1990, Proposition 2) | — |
| `ErgodicTheory` | `PascalColumns` | formalized | rule `90` from a single cell is Pascal's triangle modulo two (Wolfram 1983), and `C(a + b, a)` is odd exactly when `a` and `b` share no binary digit (Lucas 1878, at the prime two) | Mathlib has Lucas's congruence and no statement at the prime two; Rocq has the rule-`60` form |
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

## What is proved here

The short form of each result, grouped by library root. Every module's
docstring carries the full statement and its boundary.

### `AIT` — algorithmic information theory

- **Kolmogorov complexity at two measures, and the load-bearing one is bits**
  (`KolmogorovComplexity.lean`, `KolmogorovBitlen.lean`): the least-index measure `K` is uncomputable by the
  recursion theorem — and so, separately, is the **bit-length** measure
  `Nat.size ∘ encode`, the one the description-length results are stated at
  (`K_bitlen_not_computable`); the second proof re-runs the argument from
  scratch because `Nat.size` is not injective and the reduction genuinely
  fails. Boundary: two-machine
  invariance at these two measures is deferred with a documented obstruction
  — Mathlib exposes a single fixed universal machine, and the classical bound
  needs two; at the additive measure it is `invariance_general`, additive for
  composition-style interpreters and κ-multiplicative in general.

- **Time-bounded complexity** (`KolmogorovTimeBounded.lean`): `K_t` is at
  least `K`, antitone in the time bound, and equal to `K` from some bound on
  (`K_le_K_t`, `K_t_antitone`, `K_t_eventually`).
- **Levin's coding theorem on a universal prefix machine**
  (`PrefixMachine.lean`, `BitStringPrimrec.lean`,
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
  self-delimiting at the price of its own length written in the Elias code,
  which is *Discovery* §1.1's model-cost term read on the machine that section
  names. Boundary: constants are code lengths, named rather than computed; the
  converse at a constant factor is `IndexCost.lean` in the companion library,
  and neither
  additive form between the two currencies is settled.

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
  (`KB_not_computable`) by Berry's argument through the already-landed
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
  parent over any pair meeting them (`haltingProb_prefix_incompressible_of`)
  searches for the least stage past the *shifted* threshold
  `m / 2 ^ n − 2 ^ (-n)`, takes the least value not yet revealed, and prices
  it by `KB_partial_map_le`. Boundary: the pair, not a prefix of the
  expansion; the constant existential; no randomness or irrationality
  stated; the proof is Shen, Uspensky and Vereshchagin's Theorem 100, and no
  first-ness is claimed.

### `ChaitinIncompleteness` — Chaitin's theorem and the chain builder

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
  The additive form lands on the prefix machine `KB` (`ChaitinPrefix.lean`,
  `SerializationParse.lean`, `KBEnumerable.lean`): one program `c₀` fixed for
  every theory, and `n < elen c₀ + KB(⌜e⌝)` at any program `e` enumerating
  the theory's provable sentences of this form — Chaitin's own constant, the
  theory's prefix complexity, under consistency alone (`chaitin_theoremB`,
  `chaitin_theoremB_RE`), with the true-and-unprovable family at that
  constant (`chaitin_true_unprovableB`) and an enumerator exhibited for every
  `Δ₁` theory (`exists_enumerator_chaitinB`); proved from two leaf
  propositions, each in its own module — a primitive-recursive parser of the
  serialization with its two-way specification (`eParserSpec`) and the
  computable enumeration of "`KB(s) ≤ n`" (`rePred_kleB`) — and assembled
  once both were proved, the hypotheses' joint satisfiability witnessed at
  `𝗣𝗔⁻` (`chaitin_theoremB_nonvacuous`). Boundary: the enumerator is of the
  theorems, not the axioms; the constant is named, not computed.
  The chain builder the companion library's deep ladder runs on is here too
  (`SelectorLadder.lean`, `RungSelector`, `rung_true`, `rung_unprovable`,
  `ladderTheory_lt_succ`): parametric in a rung selector picking, at each
  theory, a sentence true in `ℕ` and unprovable in it, every rung true and
  unprovable in the theory it extends and the chain strictly ascending — the
  finite stages of Turing's and Feferman's progressions.

### `Learning` — the statistical-query model and verified learners

- **Statistical-query learning** — to our knowledge the first formalization of
  the SQ model in any proof assistant (`SQObjects.lean`, `SQEnvelope.lean`, …): the
  statistical query dimension with its separated-subfamily characterization
  definitional, a survivor pigeonhole, a *linear* version-space envelope under
  2τ-identifiability (Szörényi's maximality argument) with that hypothesis
  proved load-bearing by a near-duplicate guard family, an identifiability-free
  net envelope (`versionSpace_net_envelope`), and parity's `2^n` SQ-dimension
  lower bound derived from character orthogonality.

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
  `cumulative_hellinger`, `average_hellinger_rate`).

### `AnytimeValid`, `ErgodicTheory`, `ShannonInfo` — tail bounds, ergodic tools and information

- **Ville's inequality** for non-negative supermartingales (`Ville.lean`) —
  the all-time tail bound anytime-valid inference is built on; absent from
  Mathlib (whose Doob maximal inequality is submartingale-only).
- **Finite-case information theory and coding bounds**: the data-processing
  inequality and Fano's inequality on finite types (`FiniteInfoTheory.lean`),
  a prefix-complexity semimeasure (`∑ 2^{−KP} ≤ 1`), an additive
  self-delimiting program-length measure with a length-efficient binary
  constant, and binary index-form Kraft–McMillan bridges (`BinaryKraft.lean`).
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
  Lucas's criterion at the prime two (`choose_add_mod_two_eq_one_iff`).
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

## Relation to lean-algorithmic-learning-theory

That library requires this package by tag and holds the research the classical
results serve: persistence capacity, the reflection chain and the growing
worlds' theory, with the companion papers that state them. The radius-one rule
space and the growing world's basic objects are in
`lean-elementary-cellular-automata`, which requires this package as well. Some
docstrings here say where a downstream result lives there; they are pointers,
never imports.

## How this repository is maintained

This is a **curated snapshot** of a private development, released together with
the research library that requires it. Issues are welcome — above all a prior
formalization we missed, which changes a label. A module labelled duplicated or
ported is a standing invitation to bridge it to the original and delete ours.

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
