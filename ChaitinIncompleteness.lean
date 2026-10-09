/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ChaitinIncompleteness.AxiomAudit
public import ChaitinIncompleteness.ChaitinIncompleteness
public import ChaitinIncompleteness.ChaitinPrefix
public import ChaitinIncompleteness.KBEnumerable
public import ChaitinIncompleteness.SelectorLadder

/-!
# `ChaitinIncompleteness`

Chaitin's incompleteness theorem for Kolmogorov complexity.

The theorem over the bit-length complexity and, additively, over the prefix complexity, against a
formal arithmetic taken from `FormalizedFormalLogic/Foundation`, together with the
enumerability of the prefix complexity's bound predicate and the rung-chain builder that
appends an unprovable truth at every stage of a chain of theories.

This root module imports every module of the library root, including its axiom audit.
-/
