module

public import ChaitinIncompleteness.AxiomAudit
public import ChaitinIncompleteness.ChaitinIncompleteness
public import ChaitinIncompleteness.ChaitinPrefix
public import ChaitinIncompleteness.KBEnumerable
public import ChaitinIncompleteness.TheoryProgression

/-!
# `ChaitinIncompleteness`

Chaitin's incompleteness theorem for Kolmogorov complexity.

The theorem over the bit-length complexity and, additively, over the prefix complexity, against a
formal arithmetic taken from `FormalizedFormalLogic/Foundation`, together with the
enumerability of the prefix complexity's bound predicate and the progression of theories that
appends an unprovable truth at every stage of a chain of theories.

This root module imports every module of the library root, including its axiom audit.
-/
