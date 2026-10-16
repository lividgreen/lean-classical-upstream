module

public import ErgodicTheory.AxiomAudit
public import ErgodicTheory.Birkhoff.AxiomAudit
public import ErgodicTheory.Birkhoff.PointwiseBirkhoff
public import ErgodicTheory.DrivenColumns
public import ErgodicTheory.ElementaryRuleClasses
public import ErgodicTheory.LocalRuleColumns
public import ErgodicTheory.MarkovHoeffding
public import ErgodicTheory.MixingHoeffding
public import ErgodicTheory.NumberConservation
public import ErgodicTheory.PascalColumns

/-!
# `ErgodicTheory`

Ergodic theory and concentration along orbits.

The pointwise Birkhoff ergodic theorem (a vendored, attributed port), Hoeffding-type
concentration for finite-state Markov chains under a spectral gap, the mixing form of the
Hoeffding hypothesis, and finite systems driven by an eventually periodic input.

This root module imports every module of the library root, including its axiom audit.
-/
