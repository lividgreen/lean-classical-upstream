/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Learning.BayesRedundancy
public import Learning.DecisionListData
public import Learning.DecisionListSolver
public import Learning.SQBounds
public import Learning.SQEnvelope
public import Learning.SQObjects
public import Learning.SQOracle

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Axiom audit for the `Learning` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

-- [Discovery] §3 Sub-problem B (Bayes-mixture redundancy, realizable-deterministic route toward dropping
-- `hrate`): the step-(3) calculus inequality (`log_le_hellinger`) + point-mass identity
-- (`hellinger_point_mass`), and the step-(1) mixture regret (`mixture_regret_log`). All elementary.
/-- info: 'BayesRedundancy.log_le_hellinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.log_le_hellinger

/-- info: 'BayesRedundancy.hellinger_point_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.hellinger_point_mass

/-- info: 'BayesRedundancy.mixture_regret_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.mixture_regret_log

-- §3 Sub-problem B (cont.): the prequential telescope (step 2) and the assembled rate (step 4) —
-- `−log P̄(n) = ∑ₜ −log condₜ`, then `∑ₜ D_H²ₜ ≤ K(R)·ln2/2` and the per-step average ≤ K(R)·ln2/(2n).
-- This is the Bayes-mixture redundancy rate (eq. 3) PROVED (realizable-deterministic), not assumed via `hrate`.
/-- info: 'BayesRedundancy.telescope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.telescope

/-- info: 'BayesRedundancy.cumulative_hellinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.cumulative_hellinger

/-- info: 'BayesRedundancy.average_hellinger_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.average_hellinger_rate

-- [Discovery] §3.3 Proposition 3.3 (bounded surprise): pigeonhole on the cumulative bound — the steps
-- whose one-step squared Hellinger error exceeds ε number fewer than K(R)·ln2/(2ε), uniformly in n.
-- Carries no separation hypothesis: the surprises are budgeted, but not scheduled.
/-- info: 'BayesRedundancy.sqHellinger_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.sqHellinger_nonneg

/-- info: 'BayesRedundancy.surprise_card_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.surprise_card_mul_le

/-- info: 'BayesRedundancy.surprise_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.surprise_card_le

/-- info: 'BayesRedundancy.surprise_card_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.surprise_card_lt

-- [SQ] §4 / App. A SQ version-space pruning (FV-A4): the candidate set stays poly-bounded under a
-- poly-bounded `d_SQ` (`candidates_polyBounded`), the truth is never pruned (`truth_survives_pruning`),
-- and a `> 3τ`-separated impostor IS pruned (`separated_impostor_pruned`) — soundness of SQ pruning.
/-- info: 'SQVersionSpace.candidates_polyBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQVersionSpace.candidates_polyBounded

/-- info: 'SQVersionSpace.truth_survives_pruning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQVersionSpace.truth_survives_pruning

-- [SQ] §3.1 window-noise refinement of the FV-A4 pruning geometry: window sufficiency (W) is the
-- DETERMINISM of the one-step predictor `f_R`; it weakens to the window-noise rate
-- `η := μ(o_{t+1} ≠ f_R(w_t))` (W is `η = 0`). The truth survives the UNCHANGED `2τ`-rule when the
-- budget `2η ≤ τ` holds (`truth_survives_pruning_noisy`), and a `> 3τ + 2η`-separated impostor is
-- still pruned (`separated_impostor_pruned_noisy`) — both recovering the noiseless siblings at `η = 0`.
/-- info: 'SQVersionSpace.truth_survives_pruning_noisy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQVersionSpace.truth_survives_pruning_noisy

-- [SQ] §3 ensemble SQ oracle, Tool (ii) (FV-E): Hoeffding concentration of the empirical SQ
-- answer (`sq_oracle_concentration`), the `n ≥ (2/τ²)·log(2/δ)` sample complexity
-- (`sq_oracle_sample_complexity`), and the §3→FV-A4 wiring that discharges the truth-survives
-- hypothesis with probability `≥ 1−δ` (`sq_oracle_truth_survives`).
/-- info: 'SQOracle.sq_oracle_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_concentration

/-- info: 'SQOracle.sq_oracle_sample_complexity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_sample_complexity

/-- info: 'SQOracle.sq_oracle_truth_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_truth_survives

-- [SQ] §3.1 the window-noise budget half, genuine content + wiring. A1 (`noise_gap_integral`): two
-- `[−1,1]`-valued measurable observables agreeing off a measurable event `E` differ in integral by
-- `≤ 2·μ(E)`, so a query answer is distorted by at most `2η`, `η := μ(E)` (integrability discharged
-- from boundedness on the probability measure). A3 (`sq_oracle_truth_survives_noisy`): threading the
-- gap through the arithmetic siblings and the `n ≥ (2/τ²)·log(2/δ)` sample complexity, the
-- deterministic truth `predR` survives the `2τ`-rule w.p. `≥ 1−δ` when `2η ≤ τ` — the empirical
-- mean's target `a = 𝔼φ` kept distinct from the truth `predR`.
/-- info: 'SQOracle.noise_gap_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.noise_gap_integral

/-- info: 'SQOracle.sq_oracle_truth_survives_noisy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_truth_survives_noisy

-- FV-E → FV-J glue: the finite-query union bound carrying per-query concentration to FV-J's
-- oracle object. `sq_oracle_uniform_tail` — if each of `Qs` fails tolerance `τ` w.p. `≤ δ`, then SOME
-- query fails w.p. `≤ |Qs|·δ` (`measure_biUnion_finset_le`). `empirical_isSQOracle` — off that event
-- (w.p. `≥ 1 − |Qs|·δ`) the `Qs`-restricted empirical answers satisfy `SQObjects.IsSQOracle`.
/-- info: 'SQOracle.sq_oracle_uniform_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_uniform_tail

/-- info: 'SQOracle.empirical_isSQOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.empirical_isSQOracle

-- The per-query i.i.d. instantiation discharging the union bound's
-- `htail` from `sq_oracle_concentration` — `n ≥ (2/τ²)·log(2|Qs|/δ)` samples per query ⇒ the
-- empirical answers fail `IsSQOracle` on `↥Qs` w.p. `≤ δ`.
/-- info: 'SQOracle.empirical_isSQOracle_of_iid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.empirical_isSQOracle_of_iid

-- FV-J: the SQ objects made GENUINE (`Learning/SQObjects.lean`). The statistical
-- dimension `sqDim = (M.powerset.filter (SepFam …)).sup card` (§3.4) with its DEFINITIONAL
-- characterization `sepFam_card_le_sqDim` (every τ-separated subfamily has card ≤ sqDim) and survivor
-- pigeonhole `survivors_card_le_sqDim`; BQ1 distribution-specificity `sqDim_mono_queries` (fewer
-- separating queries ⇒ smaller-or-equal dimension); the poly-bound reuse of FV-A4's envelope
-- `survivors_polyBounded_of_separated`. The parity headline: exact character orthogonality
-- `ansPar_eq` (`= 1` iff `S = φ`, else `0`), the dimension theorem `sqDim_parity_ge : 2^n ≤ sqDim`
-- for `τ < 1`, and the FV-A3 bridge `parity_dSQ_ge_exp` promoting the previously-MODELED
-- `d_SQ = 2^Ω(n)` premise to a proof (`dSQ (log 2) n = 2^n ≤ sqDim`).
/-- info: 'SQObjects.sepFam_card_le_sqDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.sepFam_card_le_sqDim

/-- info: 'SQObjects.survivors_card_le_sqDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.survivors_card_le_sqDim

/-- info: 'SQObjects.sqDim_mono_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.sqDim_mono_queries

/-- info: 'SQObjects.survivors_polyBounded_of_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.survivors_polyBounded_of_separated

/-- info: 'SQObjects.ansPar_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.ansPar_eq

/-- info: 'SQObjects.sqDim_parity_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.sqDim_parity_ge

/-- info: 'SQObjects.parity_dSQ_ge_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.parity_dSQ_ge_exp

-- FV-L, identifiability-free: the version-space envelope WITHOUT the `2τ`-identifiability hypothesis
-- (the BFJKMR clustering argument), on the FV-J layer (`Learning/SQObjects.lean`). `sqDim_antitone_tol`
-- (antitone in the tolerance) + `exists_maximal_sepFam` (a maximal `2τ`-net exists) + `sepNet_covers`
-- (maximality ⇒ every survivor is `2τ`-close to a net point) + `merge_answer_close` (the mass-merge
-- averaging bound) assemble into `versionSpace_net_envelope`: for ANY version space `V ⊆ M`, a net of
-- card ≤ sqDim with a `2τ`-close retraction — no pairwise-separation hypothesis on the survivors.
/-- info: 'SQObjects.merge_answer_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.merge_answer_close

/-- info: 'SQObjects.versionSpace_net_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.versionSpace_net_envelope

-- FV-L: the BFJKMR version-space envelope over FV-J's
-- GENUINE `sqDim`, via Szörényi's elementary maximality + packing (`Learning/SQEnvelope.lean`).
-- `close_on_of_prune` (App-A Prop-1 analogue) — survivors of the `2τ`-pruning rule are pairwise
-- `4τ`-close on the schedule (triangle inequality; the version space need NOT be pairwise separated).
-- `exists_sqNet` (Szörényi maximality) — every finite class has a MAXIMAL `τ`-separated subfamily
-- with `card = sqDim` that COVERS `M` (the "query schedule exists" residue FV-J/FV-K left open).
-- `subset_card_le_sqDim_of_ident` (the envelope) — under class-level identifiability at scale `2τ`,
-- the covering map is injective, so ANY subfamily (the version space) has `card ≤ sqDim M τ ans`.
-- `version_space_card_le` — the assembled App-A bound. `fvA4_envelope_discharged` — discharges FV-A4's
-- modeled premise `candidates ≤ A·d_SQ^m` with `A = m = 1`, the literal `PolyBounded` chain, closing
-- the residue with class-level identifiability replacing FV-J's survivor-set separation hypothesis.
/-- info: 'SQEnvelope.pairwise_close_on_of_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.pairwise_close_on_of_oracle

/-- info: 'SQEnvelope.close_on_of_prune' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.close_on_of_prune

/-- info: 'SQEnvelope.exists_sqNet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.exists_sqNet

/-- info: 'SQEnvelope.subset_card_le_sqDim_of_ident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.subset_card_le_sqDim_of_ident

/-- info: 'SQEnvelope.version_space_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.version_space_card_le

/-- info: 'SQEnvelope.fvA4_envelope_discharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.fvA4_envelope_discharged

-- `hident_load_bearing` — the negative-results-as-guards practice: a near-duplicate witness
-- (a constant answer functional over `Fin N`) proving `subset_card_le_sqDim_of_ident`'s `hident`
-- load-bearing, per `/design` §4.172's finding that the direct `|V|` bound is FALSE without it.
/-- info: 'SQEnvelope.hident_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.hident_load_bearing

-- The data layer for the 1-DL consistency solver (`Learning/DecisionListData.lean`).
-- `polyTime_readK`/`polyTime_readM` — the flat `#features`/`#examples` accessors (`left`,
-- `comp left right`) are `PolyTime` with `tc = O(1)`. `readM_le_size`/`readK_le_size` — THE
-- load-bearing size bound (I2): on a well-formed instance (`WF`: the stored counts are backed by
-- genuine length-`m`/length-`k` flag-cons lists) the counts are poly-bit VALUES,
-- `readM/readK inst ≤ Nat.size inst`, discharging `polyTime_loop`'s `hCval` for the solver's
-- scan/peel loops. Proof route: each flag-cons cell strictly grows `Nat.size` (`size_cons_gt`), so
-- a length-`m` list has `Nat.size ≥ m` (`isList_len_le_size`), and the list is a sub-term of `inst`.
/-- info: 'OneDL.polyTime_readK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_readK

/-- info: 'OneDL.polyTime_readM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_readM

/-- info: 'OneDL.readM_le_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.readM_le_size

/-- info: 'OneDL.readK_le_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.readK_le_size

-- The decode-cost verdict, the flag-cons pivot, and the indexed accessors.
-- `cPred_tc_not_polyBounded` — the smallest rfind'-free predecessor is value-linear (`n ≤ tc cPred n`),
-- NOT poly-bounded, so an offset-cons (predecessor-based) decode fails; hence the flag-cons pivot
-- (`cons e r = Nat.pair 1 (Nat.pair e r)`, decoded by pure `unpair`, `tc = O(1)`). `polyTime_peel` —
-- the peel loop `n ↦ peel (A n) (C n)` is `PolyTime` given a poly-bit index `C` (a `polyTime_loop`
-- instance: `hCval` from `C`, `hacc` from the suffix `≤ A n`, constant step cost via `tc_prec_le'`).
-- `polyTime_getExample` — the `i`-th example accessor, `headL ∘ peel`. `getExample_encode` — List-model
-- correctness: `headL (peel (encodeList xs) i) = xs[i]` (via `peel`-is-`drop`).
/-- info: 'OneDL.cPred_tc_not_polyBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.cPred_tc_not_polyBounded

/-- info: 'OneDL.polyTime_peel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_peel

/-- info: 'OneDL.polyTime_getExample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_getExample

/-- info: 'OneDL.getExample_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.getExample_encode

/-- info: 'OneDL.val_cPurity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.val_cPurity

/-- info: 'OneDL.purity_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.purity_correct

/-- info: 'OneDL.purity_isPure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.purity_isPure_iff

/-- info: 'OneDL.polyTime_cScan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_cScan

-- The per-step cost bound is discharged, so purity is a self-contained
-- `PolyTime` on an honest well-formed domain. `WFBits inst` — the binary well-formedness (WF plus every
-- feature bit and label `≤ 1`); `MaskValid mask m` — the working set is a length-`m` flag-cons list of
-- bits. `visited_bits` — over the visited states `i < readM inst`, the three operands the step reads
-- (mask head, feature at `j`, label) are all `≤ 1` (features/labels from `WFBits`, mask bit from
-- `MaskValid`, the `sawZero`/`sawOne` accumulators from the flag invariants), so `tc cStep ≤ 16·jOf n +
-- 5700`. `polyTime_purity` — packaged as `PolyTimeOn PurityWF purityVal`: the raw `(Bstep+1)·m` cost is
-- poly-bit via `jOf n ≤ readK ≤ size n` and `readM ≤ size n`, and the verdict is three bits. The ONLY
-- residual hypotheses are the WF-conditional ones (the `PurityWF` domain); no `PolyBounded` premises.
/-- info: 'OneDL.polyTime_purity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_purity

-- The greedy outer loop `solve` (`readM inst` rounds of covering-pure-literal
-- selection + mask refinement, output built by prepend then one final `cReverse`). `polyTime_solve` —
-- packaged as `PolyTimeOn SolveWF solveVal`: `O(m²·k²)` native cost (`k` rounds × one `findLit` `O(m·k²)`
-- + one `maskUpdate` `O(m·k)`), and — the crux — the exponential flag-cons OUTPUT stays poly-bit because
-- the instance already pays (exponentially) for its `m` examples: `two_pow_readM_le` gives
-- `2^(readM) ≤ size n + 1`, so `svCnt ≤ readM` rules cost `≤ (size n+1)²·O(size n)` bits (cubic).
-- `maskValid_solve` — the working mask stays a valid length-`m` bit-list every round (`maskValid_svAcc`
-- invariant); `dlModel_svAcc` — the output `svDL` is the flag-`cons` encoding of a genuine `List` of
-- `svCnt` rule-triples (the `List` model that lets `cReverse`/`size_encodeList_le` bound the output).
-- Greedy CORRECTNESS (finalMask all-zero iff a consistent 1-DL exists) is guarded below.
/-- info: 'OneDL.polyTime_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_solve

/-- info: 'OneDL.maskValid_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.maskValid_solve

/-- info: 'OneDL.findLit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.findLit_sound

-- Greedy CORRECTNESS. `progress` (Engine Lemma 1: a consistent 1-DL forces a covering-pure literal
-- while any example is active — default-monochromatic vs first-firing-rule cases); `output_consistent`
-- (Engine Lemma 2: an emptied mask means the emitted forward DL is consistent for ALL examples); and the
-- capstone `solve_decides` — finalMask all-zero **iff** a consistent 1-DL over valid literals exists (⇐ by
-- the `activeCount` monovariant, ⇒ by Engine Lemma 2).
/-- info: 'OneDL.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.progress

/-- info: 'OneDL.output_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.output_consistent

/-- info: 'OneDL.solve_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.solve_decides
