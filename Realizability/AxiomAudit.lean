module

public import Realizability.Realizability
public import Realizability.RealizabilityCCC
public import Realizability.RealizabilityCoproduct
public import Realizability.RealizabilitySubobject


/-!
# Axiom audit for the `Realizability` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

-- The realizability category
set_option linter.style.longLine false in
/-- info: 'Realizability.universal_evaluator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.universal_evaluator

set_option linter.style.longLine false in
/-- info: 'Realizability.counter_step_realizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.counter_step_realizes

-- Every function between FINITE assemblies is a morphism (not merely a total function).
set_option linter.style.longLine false in
/-- info: 'Realizability.realizes_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.realizes_of_finite

-- The realizability CCC
set_option linter.style.longLine false in
/-- info: 'RealizabilityCCC.exp_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCCC.exp_universal

-- FINITE COPRODUCTS in the realizability category `Asm` (upstreamable):
-- the initial object (`initialAsm_isInitial`) and the binary coproduct's copairing universal
-- property (`coprod_universal` — existence AND uniqueness of the mediating realized morphism), plus
-- the finite-domain trackability lemma (`trackable_of_fin_dom`) that makes maps out of a finite
-- assembly genuine morphisms. New realizability infrastructure, absent from Mathlib.
set_option linter.style.longLine false in
/-- info: 'RealizabilityCoproduct.initialAsm_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCoproduct.initialAsm_isInitial

set_option linter.style.longLine false in
/-- info: 'RealizabilityCoproduct.coprod_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCoproduct.coprod_universal

set_option linter.style.longLine false in
/-- info: 'RealizabilityCoproduct.trackable_of_fin_dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCoproduct.trackable_of_fin_dom

-- THE SUBOBJECT CLASSIFIER OF THE FINITE FRAGMENT: the comprehension subobject
-- `subAsm A P`, the one-bit classifier `Bool = 𝟙 ⊕ 𝟙`, and its pullback universal property.
-- `classifier_universal` — the classifying square is a pullback: `u` factors through the
-- comprehension subobject iff `χ_P ∘ u` is constantly `true` (no finiteness on the domain `C`);
-- `chi_unique` — `χ_P` is the unique classifying map, global elements separating the finite
-- carrier. The classification is of comprehension subobjects (the finite fragment); every function
-- out of the classified object being a morphism is the property `AllTrackable`, which `finAsm`
-- witnesses.
set_option linter.style.longLine false in
/-- info: 'RealizabilitySubobject.classifier_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilitySubobject.classifier_universal

set_option linter.style.longLine false in
/-- info: 'RealizabilitySubobject.chi_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilitySubobject.chi_unique

-- Equalizers as comprehension subobjects, with their fork universal property.
set_option linter.style.longLine false in
/-- info: 'RealizabilitySubobject.equalizer_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilitySubobject.equalizer_universal
