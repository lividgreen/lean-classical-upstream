module

public import ErgodicTheory.EdgePeriods
public import ErgodicTheory.ElementaryRuleClasses
public import ErgodicTheory.LocalRuleColumns
public import ErgodicTheory.NumberConservation
public import ErgodicTheory.MixingHoeffding
public import ErgodicTheory.PascalColumns
public import ErgodicTheory.Rule18Annihilation
public import ErgodicTheory.Rule18Kinks
public import ErgodicTheory.Rule18Lift
public import ErgodicTheory.Rule22Sparse


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
/-- info: 'LocalRuleColumns.iterate_two_pow_step_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.iterate_two_pow_step_linear

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

set_option linter.style.longLine false in
/-- info: 'Rule22Sparse.step_rule22_eq_of_supportInCoset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule22Sparse.step_rule22_eq_of_supportInCoset

set_option linter.style.longLine false in
/-- info: 'Rule22Sparse.iterate_step_rule22_two_eq_rule90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule22Sparse.iterate_step_rule22_two_eq_rule90

set_option linter.style.longLine false in
/-- info: 'Rule22Sparse.supportInCoset_iterate_step_rule90_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule22Sparse.supportInCoset_iterate_step_rule90_two

set_option linter.style.longLine false in
/-- info: 'Rule22Sparse.iterate_step_rule22_two_mul_eq_rule90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule22Sparse.iterate_step_rule22_two_mul_eq_rule90

set_option linter.style.longLine false in
/-- info: 'Rule22Sparse.supportInCoset_iterate_step_rule22_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule22Sparse.supportInCoset_iterate_step_rule22_two_mul

set_option linter.style.longLine false in
/-- info: 'Rule22Sparse.iterate_step_rule22_two_mul_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule22Sparse.iterate_step_rule22_two_mul_single

set_option linter.style.longLine false in
/-- info: 'Rule22Sparse.iterate_step_rule90_two_mul_single_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule22Sparse.iterate_step_rule90_two_mul_single_even

set_option linter.style.longLine false in
/-- info: 'Rule22Sparse.iterate_step_rule90_two_mul_single_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule22Sparse.iterate_step_rule90_two_mul_single_odd

set_option linter.style.longLine false in
/-- info: 'Rule22Sparse.iterate_step_rule22_odd_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule22Sparse.iterate_step_rule22_odd_single

set_option linter.style.longLine false in
/-- info: 'Rule22Sparse.not_iterate_step_rule22_two_eq_rule90_off_coset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule22Sparse.not_iterate_step_rule22_two_eq_rule90_off_coset

set_option linter.style.longLine false in
/-- info: 'Rule22Sparse.iterate_step_rule22_two_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule22Sparse.iterate_step_rule22_two_reduction

set_option linter.style.longLine false in
/-- info: 'Rule22Sparse.iterate_step_rule22_two_mul_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule22Sparse.iterate_step_rule22_two_mul_reduction

set_option linter.style.longLine false in
/-- info: 'Rule22Sparse.not_iterate_step_rule22_two_reduction_off_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule22Sparse.not_iterate_step_rule22_two_reduction_off_even

set_option linter.style.longLine false in
/-- info: 'Rule18Kinks.kinkSet_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule18Kinks.kinkSet_finite

set_option linter.style.longLine false in
/-- info: 'Rule18Kinks.kinks_step_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule18Kinks.kinks_step_le

set_option linter.style.longLine false in
/-- info: 'Rule18Kinks.kinks_step_le_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule18Kinks.kinks_step_le_of_agree

set_option linter.style.longLine false in
/-- info: 'Rule18Kinks.kinks_step_rule18_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule18Kinks.kinks_step_rule18_le

set_option linter.style.longLine false in
/-- info: 'Rule18Kinks.kinks_mod_two_of_extremes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule18Kinks.kinks_mod_two_of_extremes

set_option linter.style.longLine false in
/-- info: 'Rule18Kinks.kinks_step_rule18_mod_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule18Kinks.kinks_step_rule18_mod_two

set_option linter.style.longLine false in
/-- info: 'Rule18Kinks.even_sub_of_kinks_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule18Kinks.even_sub_of_kinks_eq_zero

set_option linter.style.longLine false in
/-- info: 'Rule18Kinks.jenAnnihilation_of_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule18Kinks.jenAnnihilation_of_lift

set_option linter.style.longLine false in
/-- info: 'Rule18Kinks.leftmostKinkStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule18Kinks.leftmostKinkStep

set_option linter.style.longLine false in
/-- info: 'Rule18Kinks.rightmostKinkStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule18Kinks.rightmostKinkStep

set_option linter.style.longLine false in
/-- info: 'Rule18Kinks.liftKinkCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule18Kinks.liftKinkCells

set_option linter.style.longLine false in
/-- info: 'Rule18Kinks.liftConjugacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule18Kinks.liftConjugacy

set_option linter.style.longLine false in
/-- info: 'Rule18Kinks.jenAnnihilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Rule18Kinks.jenAnnihilation

/-- info: 'EdgePeriods.iterate_eq_of_eq_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EdgePeriods.iterate_eq_of_eq_below

set_option linter.style.longLine false in
/-- info: 'EdgePeriods.exists_prefix_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EdgePeriods.exists_prefix_return

set_option linter.style.longLine false in
/-- info: 'EdgePeriods.prefixPeriod_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EdgePeriods.prefixPeriod_pos

set_option linter.style.longLine false in
/-- info: 'EdgePeriods.iterate_eq_of_add_prefixPeriod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EdgePeriods.iterate_eq_of_add_prefixPeriod

set_option linter.style.longLine false in
/-- info: 'EdgePeriods.prefixPeriod_dvd_of_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EdgePeriods.prefixPeriod_dvd_of_return

set_option linter.style.longLine false in
/-- info: 'EdgePeriods.prefixPeriod_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EdgePeriods.prefixPeriod_zero

set_option linter.style.longLine false in
/-- info: 'EdgePeriods.prefixPeriod_succ_eq_or_eq_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EdgePeriods.prefixPeriod_succ_eq_or_eq_two_mul

set_option linter.style.longLine false in
/-- info: 'EdgePeriods.prefixPeriod_eq_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EdgePeriods.prefixPeriod_eq_two_pow

set_option linter.style.longLine false in
/-- info: 'EdgePeriods.apply_add_prefixPeriod_of_eq_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EdgePeriods.apply_add_prefixPeriod_of_eq_two_mul

set_option linter.style.longLine false in
/-- info: 'EdgePeriods.apply_add_prefixPeriod_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EdgePeriods.apply_add_prefixPeriod_of_eq

set_option linter.style.longLine false in
/-- info: 'EdgePeriods.prefixPeriod_succ_eq_or_eq_two_mul_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EdgePeriods.prefixPeriod_succ_eq_or_eq_two_mul_nonvacuous
