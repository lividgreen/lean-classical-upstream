/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Realizability.Realizability
public import Realizability.RealizabilityCCC
public import Realizability.RealizabilityCoproduct
public import Realizability.RealizabilitySubobject

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Axiom audit for the `Realizability` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

-- §4.1 realizability category (FV-11)
/-- info: 'Realizability.universal_evaluator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.universal_evaluator

/-- info: 'Realizability.counter_step_realizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.counter_step_realizes

-- §4.1 / §4.5: every function between FINITE assemblies is a morphism (so `Prf`/`Decide` are
-- morphisms of Rep(S), not merely total Boolean functions).
/-- info: 'Realizability.realizes_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.realizes_of_finite

-- §4.3 realizability CCC (FV-12)
/-- info: 'RealizabilityCCC.exp_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCCC.exp_universal

-- §4 FINITE COPRODUCTS in the realizability category `Asm` (upstreamable):
-- the initial object (`initialAsm_isInitial`) and the binary coproduct's copairing universal property
-- (`coprod_universal` — existence AND uniqueness of the mediating realized morphism), plus the
-- finite-domain trackability lemma (`trackable_of_finDom`) that makes maps out of a finite assembly
-- genuine morphisms. New realizability infrastructure, absent from Mathlib.
/-- info: 'RealizabilityCoproduct.initialAsm_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCoproduct.initialAsm_isInitial

/-- info: 'RealizabilityCoproduct.coprod_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCoproduct.coprod_universal

/-- info: 'RealizabilityCoproduct.trackable_of_finDom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCoproduct.trackable_of_finDom

-- §4.2 THE SUBOBJECT CLASSIFIER OF THE FINITE FRAGMENT (FV-21): the comprehension subobject
-- `subAsm A P`, the one-bit classifier `Bool = 𝟙 ⊕ 𝟙`, and its pullback universal property.
-- `classifier_universal` — the classifying square is a pullback: `u` factors through the
-- comprehension subobject iff `χ_P ∘ u` is constantly `true` (no finiteness on the domain `C`);
-- `chi_unique` — `χ_P` is the unique classifying map, global elements separating the finite carrier.
-- The classification is of comprehension subobjects (the finite fragment); every function out of the
-- classified object being a morphism is the §4.1 property `AllTrackable`, which `finAsm` witnesses.
/-- info: 'RealizabilitySubobject.classifier_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilitySubobject.classifier_universal

/-- info: 'RealizabilitySubobject.chi_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilitySubobject.chi_unique

-- §4.2 equalizers as comprehension subobjects, with their fork universal property.
/-- info: 'RealizabilitySubobject.equalizer_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilitySubobject.equalizer_universal
