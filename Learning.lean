/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Learning.AxiomAudit
public import Learning.BayesRedundancy
public import Learning.ConjunctionPredictor
public import Learning.ConjunctionSolver
public import Learning.DecisionListData
public import Learning.DecisionListPredictor
public import Learning.DecisionListSolver
public import Learning.SQBounds
public import Learning.SQEnvelope
public import Learning.SQObjects
public import Learning.SQOracle

/-!
# `Learning`

Learning theory.

Statistical-query learning (the statistical dimension, oracles, objects and the version-space
envelope), polynomial-time solvers and predictors for conjunctions and one-decision lists, and
the redundancy of Bayes mixtures.

This root module imports every module of the library root, including its axiom audit.
-/
