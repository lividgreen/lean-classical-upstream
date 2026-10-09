/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ErgodicTheory.MixingHoeffding

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Axiom audit for the `ErgodicTheory` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

/-- info: 'BirkhoffTool.mixingHoeffdingTo_of_mixingHoeffding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixingHoeffdingTo_of_mixingHoeffding

/-- info: 'BirkhoffTool.mixingHoeffding_iff_forall_mixingHoeffdingTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixingHoeffding_iff_forall_mixingHoeffdingTo
