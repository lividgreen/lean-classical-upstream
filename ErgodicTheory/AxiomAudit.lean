module

public import ErgodicTheory.ElementaryRuleClasses
public import ErgodicTheory.LocalRuleColumns
public import ErgodicTheory.NumberConservation
public import ErgodicTheory.MixingHoeffding
public import ErgodicTheory.PascalColumns


/-!
# Axiom audit for the `ErgodicTheory` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

set_option linter.style.longLine false in
/-- info: 'MixingHoeffding.mixingHoeffdingTo_of_mixingHoeffding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MixingHoeffding.mixingHoeffdingTo_of_mixingHoeffding

set_option linter.style.longLine false in
/-- info: 'MixingHoeffding.mixingHoeffding_iff_forall_mixingHoeffdingTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MixingHoeffding.mixingHoeffding_iff_forall_mixingHoeffdingTo

set_option linter.style.longLine false in
/-- info: 'LocalRuleColumns.eventuallyPeriodic_window_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.eventuallyPeriodic_window_iff

set_option linter.style.longLine false in
/-- info: 'LocalRuleColumns.eventuallyPeriodic_column_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.eventuallyPeriodic_column_between

set_option linter.style.longLine false in
/-- info: 'LocalRuleColumns.eventuallyPeriodic_column_between_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.eventuallyPeriodic_column_between_nonvacuous

set_option linter.style.longLine false in
/-- info: 'LocalRuleColumns.iterate_two_pow_step90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.iterate_two_pow_step90

/-- info: 'LocalRuleColumns.iterate_step_eq_zero_of_gt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.iterate_step_eq_zero_of_gt

/-- info: 'LocalRuleColumns.iterate_step_eq_zero_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.iterate_step_eq_zero_of_lt

set_option linter.style.longLine false in
/-- info: 'LocalRuleColumns.column_step90_single_one_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.column_step90_single_one_live

set_option linter.style.longLine false in
/-- info: 'LocalRuleColumns.column_step90_single_one_dead_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.column_step90_single_one_dead_between

set_option linter.style.longLine false in
/-- info: 'LocalRuleColumns.not_eventuallyPeriodic_column_step90_single_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.not_eventuallyPeriodic_column_step90_single_one

set_option linter.style.longLine false in
/-- info: 'PascalColumns.step_rule90_single_pascal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PascalColumns.step_rule90_single_pascal

set_option linter.style.longLine false in
/-- info: 'PascalColumns.step_rule90_single_eq_zero_of_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PascalColumns.step_rule90_single_eq_zero_of_odd

set_option linter.style.longLine false in
/-- info: 'PascalColumns.step_rule90_single_eq_zero_of_lt_abs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PascalColumns.step_rule90_single_eq_zero_of_lt_abs

set_option linter.style.longLine false in
/-- info: 'PascalColumns.choose_add_mod_two_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PascalColumns.choose_add_mod_two_eq_one_iff

set_option linter.style.longLine false in
/-- info: 'PascalColumns.choose_three_mul_mod_two_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PascalColumns.choose_three_mul_mod_two_eq_one_iff

set_option linter.style.longLine false in
/-- info: 'PascalColumns.step_rule90_single_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PascalColumns.step_rule90_single_eq_one_iff

set_option linter.style.longLine false in
/-- info: 'ElementaryRuleClasses.card_classes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ElementaryRuleClasses.card_classes

set_option linter.style.longLine false in
/-- info: 'NumberConservation.ones_step_of_isFlux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NumberConservation.ones_step_of_isFlux

set_option linter.style.longLine false in
/-- info: 'NumberConservation.conserves_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NumberConservation.conserves_iff
