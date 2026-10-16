module

public import ShannonInfo.ChengCCC
public import ShannonInfo.FiniteInfoTheory


/-!
# Axiom audit for the `ShannonInfo` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

-- Cheng (2026) Theorem 4 re-checked: necessity core + the necessary-not-sufficient
-- point, and the finite info-theory foundation.
/-- info: 'ChengCCC.cccLower_vacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.cccLower_vacuous

/-- info: 'ChengCCC.misid_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.misid_lower_bound

set_option linter.style.longLine false in
/-- info: 'ChengCCC.forgetting_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.forgetting_lower_bound

set_option linter.style.longLine false in
/-- info: 'FiniteInfoTheory.entropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.entropy_nonneg

-- Mutual information of a joint pmf and its nonnegativity (finite Gibbs) — the first
-- discharged brick of the DPI/Fano interface that `ChengCCC` still carries as named hypotheses.
set_option linter.style.longLine false in
/-- info: 'FiniteInfoTheory.mutualInfo_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.mutualInfo_nonneg

-- Entropy form of MI `I(X;Y) = H(X) − H(X|Y)` — discharges the `hCond` identity.
set_option linter.style.longLine false in
/-- info: 'FiniteInfoTheory.mutualInfo_eq_sub_condEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.mutualInfo_eq_sub_condEntropy

-- Conditional mutual information nonnegativity `I(X;Z|Y) ≥ 0` (per-slice finite Gibbs).
set_option linter.style.longLine false in
/-- info: 'FiniteInfoTheory.condMutualInfo_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.condMutualInfo_nonneg

-- The data-processing inequality `I(X;Z) ≤ I(X;Y)` for a Markov chain `X → Y → Z` —
-- the rigorous content discharging `hDPI` at the chain `T → c → θ`.
set_option linter.style.longLine false in
/-- info: 'FiniteInfoTheory.data_processing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.data_processing

-- Fano's inequality `(condEntropy μ − 1)/log(K−1) ≤ Pe` — discharges `hFano`.
/-- info: 'FiniteInfoTheory.fano'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.fano'

-- The other DPI direction `I(X;Z) ≤ I(Y;Z)` — gives `I(T;θ) ≤ I(c;θ) ≤ C_ctx`.
set_option linter.style.longLine false in
/-- info: 'FiniteInfoTheory.data_processing'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.data_processing'

-- Capstone: Cheng's misidentification bound with DPI / identity / Fano all DISCHARGED —
-- only the modelling setup (joint ν + MarkovCI, decoder g, capacity bound, K ≥ 3) remains.
set_option linter.style.longLine false in
/-- info: 'ChengCCC.cheng_misid_bound_discharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.cheng_misid_bound_discharged

-- Capstone (cont.): the forgetting lower bound with DPI / identity / Fano all DISCHARGED —
-- only the modelling setup plus Cheng's informal Step-4 link `hConn` remain.
set_option linter.style.longLine false in
/-- info: 'ChengCCC.cheng_forgetting_bound_discharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.cheng_forgetting_bound_discharged
