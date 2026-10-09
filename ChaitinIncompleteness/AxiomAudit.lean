/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ChaitinIncompleteness.ChaitinIncompleteness
public import ChaitinIncompleteness.ChaitinPrefix
public import ChaitinIncompleteness.KBEnumerable

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Axiom audit for the `ChaitinIncompleteness` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

/-! ## Chaitin's incompleteness theorem over `K_bitlen` (`ChaitinIncompleteness/ChaitinIncompleteness.lean`)

The generic adapter (`Δ₁`-axiomatized consistent extensions of `𝗥₀`) is axiom-clean: the hypotheses
`[T.Δ₁] [𝗥₀ ⪯ T] [FFL.Entailment.Consistent T]` are typeclass premises, nothing concrete is
synthesized. -/

/-- info: 'KolmogorovComplexity.chaitin_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theorem

-- The transport to recursively enumerable theories, via Craig's trick — axiom-clean, same reason.
/-- info: 'KolmogorovComplexity.chaitin_theorem_of_RE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theorem_of_RE

/-- info: 'KolmogorovComplexity.chaitin_true_unprovable_of_RE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_true_unprovable_of_RE

/-! ## Chaitin's incompleteness theorem, additive form on `KB` (`ChaitinIncompleteness/ChaitinPrefix.lean`)

The two leaf propositions `EParserSpec` and `REPred kleB` are explicit hypotheses of each
theorem below, so these guards pin the proofs FROM those hypotheses; the axioms of the leaves'
own proofs are audited where they are proved. -/

/-- info: 'KolmogorovComplexity.chaitin_bound_KB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_bound_KB_of

/-- info: 'KolmogorovComplexity.chaitin_bound_KB_of_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_bound_KB_of_min

/-- info: 'KolmogorovComplexity.chaitin_theoremB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theoremB_of

-- The transport to recursively enumerable theories, via Craig's trick — same reason.
/-- info: 'KolmogorovComplexity.chaitin_theoremB_of_RE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theoremB_of_RE

/-! ## The assembly, both leaves proved (`ChaitinIncompleteness/KBEnumerable.lean`)

`EParserSpec` and `REPred kleB` are proved, not hypotheses, from here on: the guards below pin
the UNCONDITIONAL forms of the bounds above, applied to those proofs. -/

/-- info: 'KolmogorovComplexity.chaitin_bound_KB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_bound_KB

/-- info: 'KolmogorovComplexity.chaitin_bound_KB_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_bound_KB_min

/-- info: 'KolmogorovComplexity.chaitin_theoremB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theoremB

/-- info: 'KolmogorovComplexity.chaitin_theoremB_RE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theoremB_RE

-- The enumerator is exhibited, not merely asserted to exist — `rePred_provable_chaitinB` unpacked
-- through `REPred.iff'` and `Nat.Partrec.Code.exists_code`.
/-- info: 'KolmogorovComplexity.exists_enumerator_chaitinB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.exists_enumerator_chaitinB

-- Non-vacuity: `𝗣𝗔⁻` meets every instance binder `chaitin_theoremB` asks for, at once.
/-- info: 'KolmogorovComplexity.chaitin_theoremB_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theoremB_nonvacuous

-- `KB`'s counting bound and its true-and-unprovable family, at the additive constant.
/-- info: 'KolmogorovComplexity.setOf_KB_le_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.setOf_KB_le_finite

/-- info: 'KolmogorovComplexity.chaitin_true_unprovableB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_true_unprovableB
