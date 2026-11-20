module

public import Combinatorics.BinomialSum
public import Combinatorics.PropertyB

/-!
# Axiom audit for the `Combinatorics` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

-- Property B: Erdős (1963, Theorem 1), its corollary, the witnesses and the guard family.
set_option linter.style.longLine false in
/-- info: 'PropertyB.of_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PropertyB.of_sum_le

set_option linter.style.longLine false in
/-- info: 'PropertyB.of_card_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PropertyB.of_card_le_two_pow

set_option linter.style.longLine false in
/-- info: 'PropertyB.of_sum_le_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PropertyB.of_sum_le_nonvacuous

set_option linter.style.longLine false in
/-- info: 'PropertyB.of_card_le_two_pow_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PropertyB.of_card_le_two_pow_nonvacuous

set_option linter.style.longLine false in
/-- info: 'PropertyB.not_three_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PropertyB.not_three_pairs

set_option linter.style.longLine false in
/-- info: 'PropertyB.not_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PropertyB.not_singleton

-- The sum of the binomial coefficients up to `k` against `(e n / k) ^ k`.
set_option linter.style.longLine false in
/-- info: 'Nat.sum_range_succ_choose_le_exp_mul_div_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Nat.sum_range_succ_choose_le_exp_mul_div_pow
