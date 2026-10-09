/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ShannonInfo.ChengCCC
public import ShannonInfo.FiniteInfoTheory

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Axiom audit for the `ShannonInfo` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

-- [Discovery] §4 — Cheng (2026) Theorem 4 re-checked: necessity core + the necessary-not-sufficient
-- point (refuting Prop 4.2's earlier misuse), and the finite info-theory foundation (FV-9).
/-- info: 'ChengCCC.cccLower_vacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.cccLower_vacuous

/-- info: 'ChengCCC.misid_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.misid_lower_bound

/-- info: 'ChengCCC.forgetting_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.forgetting_lower_bound

/-- info: 'FiniteInfoTheory.entropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.entropy_nonneg

-- FV-9 (cont.): mutual information of a joint pmf and its nonnegativity (finite Gibbs) — the first
-- discharged brick of the DPI/Fano interface that `ChengCCC` still carries as named hypotheses.
/-- info: 'FiniteInfoTheory.mutualInfo_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.mutualInfo_nonneg

-- FV-9 (cont.): entropy form of MI `I(X;Y) = H(X) − H(X|Y)` — discharges the `hCond` identity.
/-- info: 'FiniteInfoTheory.mutualInfo_eq_sub_condEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.mutualInfo_eq_sub_condEntropy

-- FV-9 (cont.): conditional mutual information nonnegativity `I(X;Z|Y) ≥ 0` (per-slice finite Gibbs).
/-- info: 'FiniteInfoTheory.condMutualInfo_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.condMutualInfo_nonneg

-- FV-9 (cont.): the data-processing inequality `I(X;Z) ≤ I(X;Y)` for a Markov chain `X → Y → Z` —
-- the rigorous content discharging `hDPI` at the chain `T → c → θ`.
/-- info: 'FiniteInfoTheory.dataProcessing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.dataProcessing

-- FV-9 (cont.): Fano's inequality `(condEntropy μ − 1)/log(K−1) ≤ Pe` — discharges `hFano`.
/-- info: 'FiniteInfoTheory.fano'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.fano'

-- FV-9 (cont.): the other DPI direction `I(X;Z) ≤ I(Y;Z)` — gives `I(T;θ) ≤ I(c;θ) ≤ C_ctx`.
/-- info: 'FiniteInfoTheory.dataProcessing'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.dataProcessing'

-- FV-9 capstone: Cheng's misidentification bound with DPI / identity / Fano all DISCHARGED —
-- only the modelling setup (joint ν + MarkovCI, decoder g, capacity bound, K ≥ 3) remains.
/-- info: 'ChengCCC.cheng_misid_bound_discharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.cheng_misid_bound_discharged

-- FV-9 capstone (cont.): the forgetting lower bound with DPI / identity / Fano all DISCHARGED —
-- only the modelling setup plus Cheng's informal Step-4 link `hConn` remain.
/-- info: 'ChengCCC.cheng_forgetting_bound_discharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.cheng_forgetting_bound_discharged
