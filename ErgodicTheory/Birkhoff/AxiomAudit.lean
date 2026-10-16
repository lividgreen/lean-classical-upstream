/-
# Axiom audit for the pointwise Birkhoff integration

CI guard: every `#guard_msgs in #print axioms …` below **fails `lake build`** if the theorem's
axiom set ever drifts from the standard `[propext, Classical.choice, Quot.sound]` triple.  This
pins down that the vendored pointwise ergodic theorem carries NO `sorryAx` and NO custom axiom —
the vendored dependency's footprint is clean; its corollaries are audited in `AxiomAuditMathlib`.
-/
module

public import ErgodicTheory.Birkhoff.PointwiseBirkhoff


/-! ## Vendored pointwise Birkhoff ergodic theorem
(`ErgodicTheory/Birkhoff/PointwiseBirkhoff.lean`) -/


@[expose] public section

set_option linter.style.longLine false in
/-- info: 'Birkhoff.birkhoff_ergodic_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Birkhoff.birkhoff_ergodic_theorem

set_option linter.style.longLine false in
/-- info: 'Birkhoff.birkhoff_ergodic_theorem'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Birkhoff.birkhoff_ergodic_theorem'
