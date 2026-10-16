module

public import Learning.BayesRedundancy
public import Learning.DecisionListData
public import Learning.DecisionListSolver
public import Learning.SQBounds
public import Learning.SQEnvelope
public import Learning.SQObjects
public import Learning.SQOracle


/-!
# Axiom audit for the `Learning` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

-- Bayes-mixture redundancy, realizable-deterministic route: the step-(3) calculus
-- inequality (`log_le_hellinger`) + point-mass identity
-- (`hellinger_point_mass`), and the step-(1) mixture regret (`mixture_regret_log`). All elementary.
set_option linter.style.longLine false in
/-- info: 'BayesRedundancy.log_le_hellinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.log_le_hellinger

set_option linter.style.longLine false in
/-- info: 'BayesRedundancy.hellinger_point_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.hellinger_point_mass

set_option linter.style.longLine false in
/-- info: 'BayesRedundancy.mixture_regret_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.mixture_regret_log

-- Bayes-mixture redundancy (cont.): the prequential telescope (step 2) and the assembled rate (step
-- 4) — `−log P̄(n) = ∑ₜ −log condₜ`, then `∑ₜ D_H²ₜ ≤ K(R)·ln2/2` and the per-step average ≤
-- K(R)·ln2/(2n). This is the Bayes-mixture redundancy rate PROVED (realizable-deterministic).
/-- info: 'BayesRedundancy.telescope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.telescope

set_option linter.style.longLine false in
/-- info: 'BayesRedundancy.cumulative_hellinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.cumulative_hellinger

set_option linter.style.longLine false in
/-- info: 'BayesRedundancy.average_hellinger_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.average_hellinger_rate

-- Bounded number of large errors: pigeonhole on the cumulative bound — the steps whose one-step
-- squared Hellinger error exceeds ε number fewer than K(R)·ln2/(2ε), uniformly in n. Carries no
-- separation hypothesis: the large errors are budgeted, but not scheduled.
set_option linter.style.longLine false in
/-- info: 'BayesRedundancy.sqHellinger_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.sqHellinger_nonneg

set_option linter.style.longLine false in
/-- info: 'BayesRedundancy.errorTimes_card_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.errorTimes_card_mul_le

set_option linter.style.longLine false in
/-- info: 'BayesRedundancy.errorTimes_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.errorTimes_card_le

set_option linter.style.longLine false in
/-- info: 'BayesRedundancy.errorTimes_card_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.errorTimes_card_lt

-- SQ version-space pruning: the candidate set stays poly-bounded under a poly-bounded `d_SQ`
-- (`candidates_polyBounded`), the truth is never pruned (`truth_survives_pruning`), and a `>
-- 3τ`-separated impostor IS pruned (`separated_impostor_pruned`) — soundness of SQ pruning.
set_option linter.style.longLine false in
/-- info: 'SQBounds.candidates_polyBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQBounds.candidates_polyBounded

set_option linter.style.longLine false in
/-- info: 'SQBounds.truth_survives_pruning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQBounds.truth_survives_pruning

-- Window-noise refinement of the pruning geometry: window sufficiency (W) is the DETERMINISM of the
-- one-step predictor `f_R`; it weakens to the window-noise rate `η := μ(o_{t+1} ≠ f_R(w_t))` (W is
-- `η = 0`). The truth survives the UNCHANGED `2τ`-rule when the budget `2η ≤ τ` holds
-- (`truth_survives_pruning_noisy`), and a `> 3τ + 2η`-separated impostor is still pruned
-- (`separated_impostor_pruned_noisy`) — both recovering the noiseless siblings at `η = 0`.
set_option linter.style.longLine false in
/-- info: 'SQBounds.truth_survives_pruning_noisy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQBounds.truth_survives_pruning_noisy

-- Ensemble SQ oracle: Hoeffding concentration of the empirical SQ answer
-- (`sq_oracle_concentration`), the `n ≥ (2/τ²)·log(2/δ)` sample complexity
-- (`sq_oracle_sample_complexity`), and the wiring into the pruning lemmas that discharges the
-- truth-survives hypothesis with probability `≥ 1−δ` (`sq_oracle_truth_survives`).
set_option linter.style.longLine false in
/-- info: 'SQOracle.sq_oracle_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_concentration

set_option linter.style.longLine false in
/-- info: 'SQOracle.sq_oracle_sample_complexity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_sample_complexity

set_option linter.style.longLine false in
/-- info: 'SQOracle.sq_oracle_truth_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_truth_survives

-- The window-noise budget half, genuine content + wiring. A1 (`noise_gap_integral`): two
-- `[−1,1]`-valued measurable observables agreeing off a measurable event `E` differ in integral by
-- `≤ 2·μ(E)`, so a query answer is distorted by at most `2η`, `η := μ(E)` (integrability discharged
-- from boundedness on the probability measure). A3 (`sq_oracle_truth_survives_noisy`): threading
-- the gap through the arithmetic siblings and the `n ≥ (2/τ²)·log(2/δ)` sample complexity, the
-- deterministic truth `predR` survives the `2τ`-rule w.p. `≥ 1−δ` when `2η ≤ τ` — the empirical
-- mean's target `a = 𝔼φ` kept distinct from the truth `predR`.
set_option linter.style.longLine false in
/-- info: 'SQOracle.noise_gap_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.noise_gap_integral

set_option linter.style.longLine false in
/-- info: 'SQOracle.sq_oracle_truth_survives_noisy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_truth_survives_noisy

-- Glue: the finite-query union bound carrying per-query concentration to the SQ oracle object.
-- `sq_oracle_uniform_tail` — if each of `Qs` fails tolerance `τ` w.p. `≤ δ`, then SOME query fails
-- w.p. `≤ |Qs|·δ` (`measure_biUnion_finset_le`). `empirical_isSQOracle` — off that event (w.p. `≥ 1
-- − |Qs|·δ`) the `Qs`-restricted empirical answers satisfy `SQObjects.IsSQOracle`.
set_option linter.style.longLine false in
/-- info: 'SQOracle.sq_oracle_uniform_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_uniform_tail

set_option linter.style.longLine false in
/-- info: 'SQOracle.empirical_isSQOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.empirical_isSQOracle

-- The per-query i.i.d. instantiation discharging the union bound's `htail` from
-- `sq_oracle_concentration` — `n ≥ (2/τ²)·log(2|Qs|/δ)` samples per query ⇒ the empirical answers
-- fail `IsSQOracle` on `↥Qs` w.p. `≤ δ`.
set_option linter.style.longLine false in
/-- info: 'SQOracle.empirical_isSQOracle_of_iid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.empirical_isSQOracle_of_iid

-- The SQ objects made GENUINE (`Learning/SQObjects.lean`). The statistical dimension `sqDim =
-- (M.powerset.filter (SepFam …)).sup card` with its DEFINITIONAL characterization
-- `sepFam_card_le_sqDim` (every τ-separated subfamily has card ≤ sqDim) and survivor pigeonhole
-- `survivors_card_le_sqDim`; distribution-specificity `sqDim_mono_queries` (fewer separating
-- queries ⇒ smaller-or-equal dimension); the poly-bound reuse of the envelope
-- `survivors_polyBounded_of_separated`. The parity headline: exact character orthogonality
-- `ansPar_eq` (`= 1` iff `S = φ`, else `0`), the dimension theorem `sqDim_parity_ge : 2^n ≤ sqDim`
-- for `τ < 1`, and the bridge `parity_dSQ_ge_exp` promoting the previously-MODELED `d_SQ = 2^Ω(n)`
-- premise to a proof (`dSQ (log 2) n = 2^n ≤ sqDim`).
set_option linter.style.longLine false in
/-- info: 'SQObjects.sepFam_card_le_sqDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.sepFam_card_le_sqDim

set_option linter.style.longLine false in
/-- info: 'SQObjects.survivors_card_le_sqDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.survivors_card_le_sqDim

set_option linter.style.longLine false in
/-- info: 'SQObjects.sqDim_mono_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.sqDim_mono_queries

set_option linter.style.longLine false in
/-- info: 'SQObjects.survivors_polyBounded_of_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.survivors_polyBounded_of_separated

/-- info: 'SQObjects.ansPar_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.ansPar_eq

/-- info: 'SQObjects.sqDim_parity_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.sqDim_parity_ge

set_option linter.style.longLine false in
/-- info: 'SQObjects.parity_dSQ_ge_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.parity_dSQ_ge_exp

-- Identifiability-free: the version-space envelope WITHOUT the `2τ`-identifiability hypothesis (the
-- BFJKMR clustering argument), on the SQ-objects layer (`Learning/SQObjects.lean`).
-- `sqDim_antitone_tol` (antitone in the tolerance) + `exists_maximal_sepFam` (a maximal `2τ`-net
-- exists) + `sep_net_covers` (maximality ⇒ every survivor is `2τ`-close to a net point) +
-- `merge_answer_close` (the mass-merge averaging bound) assemble into `version_space_net_envelope`:
-- for ANY version space `V ⊆ M`, a net of card ≤ sqDim with a `2τ`-close retraction — no
-- pairwise-separation hypothesis on the survivors.
set_option linter.style.longLine false in
/-- info: 'SQObjects.merge_answer_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.merge_answer_close

set_option linter.style.longLine false in
/-- info: 'SQObjects.version_space_net_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.version_space_net_envelope

-- The BFJKMR version-space envelope over the GENUINE `sqDim`, via Szörényi's elementary maximality
-- + packing (`Learning/SQEnvelope.lean`). `close_on_of_prune` (Prop-1 analogue) — survivors of the
-- `2τ`-pruning rule are pairwise `4τ`-close on the schedule (triangle inequality; the version space
-- need NOT be pairwise separated). `exists_sq_net` (Szörényi maximality) — every finite class has a
-- MAXIMAL `τ`-separated subfamily with `card = sqDim` that COVERS `M` (the "query schedule exists"
-- statement). `subset_card_le_sqDim_of_ident` (the envelope) — under class-level identifiability at
-- scale `2τ`, the covering map is injective, so ANY subfamily (the version space) has `card ≤ sqDim
-- M τ ans`. `version_space_card_le` — the assembled bound. `subset_polyBounded_of_ident` —
-- discharges the modeled premise `candidates ≤ A·d_SQ^m` with `A = m = 1`, the literal
-- `PolyBounded` chain, closing the loop with class-level identifiability replacing the survivor-set
-- separation hypothesis.
set_option linter.style.longLine false in
/-- info: 'SQEnvelope.pairwise_close_on_of_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.pairwise_close_on_of_oracle

set_option linter.style.longLine false in
/-- info: 'SQEnvelope.close_on_of_prune' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.close_on_of_prune

/-- info: 'SQEnvelope.exists_sq_net' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.exists_sq_net

set_option linter.style.longLine false in
/-- info: 'SQEnvelope.subset_card_le_sqDim_of_ident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.subset_card_le_sqDim_of_ident

set_option linter.style.longLine false in
/-- info: 'SQEnvelope.version_space_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.version_space_card_le

set_option linter.style.longLine false in
/-- info: 'SQEnvelope.subset_polyBounded_of_ident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.subset_polyBounded_of_ident

-- `hident_load_bearing` — a guard: a near-duplicate witness
-- (a constant answer functional over `Fin N`) proving `subset_card_le_sqDim_of_ident`'s `hident`
-- load-bearing: the direct `|V|` bound is FALSE without it.
set_option linter.style.longLine false in
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
-- a length-`m` list has `Nat.size ≥ m` (`isList_len_le_size`), and the list is a sub-term of
-- `inst`.
set_option linter.style.longLine false in
/-- info: 'DecisionList.polyTime_readK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.polyTime_readK

set_option linter.style.longLine false in
/-- info: 'DecisionList.polyTime_readM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.polyTime_readM

/-- info: 'DecisionList.readM_le_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.readM_le_size

/-- info: 'DecisionList.readK_le_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.readK_le_size

-- The decode-cost verdict, the flag-cons pivot, and the indexed accessors.
-- `cPred_tc_not_polyBounded` — the smallest rfind'-free predecessor is value-linear
-- (`n ≤ tc cPred n`), NOT poly-bounded, so an offset-cons (predecessor-based) decode fails; hence
-- the flag-cons pivot (`cons e r = Nat.pair 1 (Nat.pair e r)`, decoded by pure `unpair`,
-- `tc = O(1)`). `polyTime_peel` — the peel loop `n ↦ peel (A n) (C n)` is `PolyTime` given a
-- poly-bit index `C` (a `polyTime_loop` instance: `hCval` from `C`, `hacc` from the suffix `≤ A n`,
-- constant step cost via `tc_prec_le'`). `polyTime_get_example` — the `i`-th example accessor,
-- `headL ∘ peel`. `get_example_encode` — List-model correctness:
-- `headL (peel (encodeList xs) i) = xs[i]` (via `peel`-is-`drop`).
set_option linter.style.longLine false in
/-- info: 'DecisionList.cPred_tc_not_polyBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.cPred_tc_not_polyBounded

/-- info: 'DecisionList.polyTime_peel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.polyTime_peel

set_option linter.style.longLine false in
/-- info: 'DecisionList.polyTime_get_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.polyTime_get_example

set_option linter.style.longLine false in
/-- info: 'DecisionList.get_example_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.get_example_encode

/-- info: 'DecisionList.val_cPurity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.val_cPurity

set_option linter.style.longLine false in
/-- info: 'DecisionList.purity_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.purity_correct

set_option linter.style.longLine false in
/-- info: 'DecisionList.purity_is_pure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.purity_is_pure_iff

set_option linter.style.longLine false in
/-- info: 'DecisionList.polyTime_c_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.polyTime_c_scan

-- The per-step cost bound is discharged, so purity is a self-contained
-- `PolyTime` on an honest well-formed domain. `WFBits inst` — the binary well-formedness (WF plus
-- every feature bit and label `≤ 1`); `MaskValid mask m` — the working set is a length-`m`
-- flag-cons list of bits. `visited_bits` — over the visited states `i < readM inst`, the three
-- operands the step reads (mask head, feature at `j`, label) are all `≤ 1` (features/labels from
-- `WFBits`, mask bit from `MaskValid`, the `sawZero`/`sawOne` accumulators from the flag
-- invariants), so `tc cStep ≤ 16·jOf n + 5700`. `polyTime_purity` — packaged as
-- `PolyTimeOn PurityWF purityVal`: the raw `(Bstep+1)·m` cost is poly-bit via
-- `jOf n ≤ readK ≤ size n` and `readM ≤ size n`, and the verdict is three bits. The ONLY residual
-- hypotheses are the WF-conditional ones (the `PurityWF` domain); no `PolyBounded` premises.
set_option linter.style.longLine false in
/-- info: 'DecisionList.polyTime_purity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.polyTime_purity

-- The greedy outer loop `solve` (`readM inst` rounds of covering-pure-literal
-- selection + mask refinement, output built by prepend then one final `cReverse`). `polyTime_solve`
-- — packaged as `PolyTimeOn SolveWF solveVal`: `O(m²·k²)` native cost (`k` rounds × one `findLit`
-- `O(m·k²)`
-- + one `maskUpdate` `O(m·k)`), and — the crux — the exponential flag-cons OUTPUT stays poly-bit
-- because the instance already pays (exponentially) for its `m` examples: `two_pow_readM_le` gives
-- `2^(readM) ≤ size n + 1`, so `svCnt ≤ readM` rules cost `≤ (size n+1)²·O(size n)` bits (cubic).
-- `maskValid_solve` — the working mask stays a valid length-`m` bit-list every round
-- (`maskValid_svAcc` invariant); `dl_model_svAcc` — the output `svDL` is the flag-`cons` encoding
-- of a genuine `List` of `svCnt` rule-triples (the `List` model that lets
-- `cReverse`/`size_encodeList_le` bound the output). Greedy CORRECTNESS (finalMask all-zero iff a
-- consistent 1-DL exists) is guarded below.
set_option linter.style.longLine false in
/-- info: 'DecisionList.polyTime_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.polyTime_solve

set_option linter.style.longLine false in
/-- info: 'DecisionList.maskValid_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.maskValid_solve

/-- info: 'DecisionList.find_lit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.find_lit_sound

-- Greedy CORRECTNESS. `progress` (Engine Lemma 1: a consistent 1-DL forces a covering-pure literal
-- while any example is active — default-monochromatic vs first-firing-rule cases);
-- `output_consistent` (Engine Lemma 2: an emptied mask means the emitted forward DL is consistent
-- for ALL examples); and the capstone `solve_decides` — finalMask all-zero **iff** a consistent
-- 1-DL over valid literals exists (⇐ by the `activeCount` monovariant, ⇒ by Engine Lemma 2).
/-- info: 'DecisionList.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.progress

set_option linter.style.longLine false in
/-- info: 'DecisionList.output_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.output_consistent

/-- info: 'DecisionList.solve_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecisionList.solve_decides
