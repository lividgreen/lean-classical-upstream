/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ErgodicTheory.LocalRuleColumns
public import ErgodicTheory.MixingHoeffding
public import ErgodicTheory.PascalColumns

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

/-- info: 'LocalRuleColumns.eventuallyPeriodic_window_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.eventuallyPeriodic_window_iff

/-- info: 'LocalRuleColumns.eventuallyPeriodic_column_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.eventuallyPeriodic_column_between

/-- info: 'LocalRuleColumns.eventuallyPeriodic_column_between_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.eventuallyPeriodic_column_between_nonvacuous

/-- info: 'LocalRuleColumns.iterate_two_pow_step90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.iterate_two_pow_step90

/-- info: 'LocalRuleColumns.iterate_step_eq_zero_of_gt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.iterate_step_eq_zero_of_gt

/-- info: 'LocalRuleColumns.iterate_step_eq_zero_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.iterate_step_eq_zero_of_lt

/-- info: 'LocalRuleColumns.column_step90_single_one_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.column_step90_single_one_live

/-- info: 'LocalRuleColumns.column_step90_single_one_dead_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.column_step90_single_one_dead_between

/-- info: 'LocalRuleColumns.not_eventuallyPeriodic_column_step90_single_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalRuleColumns.not_eventuallyPeriodic_column_step90_single_one

/-- info: 'PascalColumns.step_rule90_single_pascal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PascalColumns.step_rule90_single_pascal

/-- info: 'PascalColumns.step_rule90_single_eq_zero_of_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PascalColumns.step_rule90_single_eq_zero_of_odd

/-- info: 'PascalColumns.step_rule90_single_eq_zero_of_lt_abs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PascalColumns.step_rule90_single_eq_zero_of_lt_abs

/-- info: 'PascalColumns.choose_add_mod_two_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PascalColumns.choose_add_mod_two_eq_one_iff

/-- info: 'PascalColumns.step_rule90_single_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PascalColumns.step_rule90_single_eq_one_iff
