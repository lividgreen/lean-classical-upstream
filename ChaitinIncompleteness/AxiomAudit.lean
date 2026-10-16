module

public import ChaitinIncompleteness.ChaitinIncompleteness
public import ChaitinIncompleteness.ChaitinPrefix
public import ChaitinIncompleteness.KBEnumerable


/-!
# Axiom audit for the `ChaitinIncompleteness` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

/-! ## Chaitin's incompleteness theorem over `K_bitlen`
(`ChaitinIncompleteness/ChaitinIncompleteness.lean`)

The generic adapter (`Δ₁`-axiomatized consistent extensions of `𝗥₀`) is axiom-clean: the hypotheses
`[T.Δ₁] [𝗥₀ ⪯ T] [FFL.Entailment.Consistent T]` are typeclass premises, nothing concrete is
synthesized. -/

set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.chaitin_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theorem

-- The transport to recursively enumerable theories, via Craig's trick — axiom-clean, same reason.
set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.chaitin_theorem_of_RE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theorem_of_RE

set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.chaitin_true_unprovable_of_RE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_true_unprovable_of_RE

/-! ## Chaitin's incompleteness theorem, additive form on `KB`
(`ChaitinIncompleteness/ChaitinPrefix.lean`)

The two premises `EParserSpec` and `REPred kleB` are explicit hypotheses of each
theorem below, so these guards pin the proofs FROM those hypotheses; the axioms of the premises'
own proofs are audited where they are proved. -/

set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.chaitin_bound_KB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_bound_KB_of

set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.chaitin_bound_KB_of_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_bound_KB_of_min

set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.chaitin_theorem_KB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theorem_KB_of

-- The transport to recursively enumerable theories, via Craig's trick — same reason.
set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.chaitin_theorem_KB_of_RE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theorem_KB_of_RE

/-! ## The assembly, both leaves proved (`ChaitinIncompleteness/KBEnumerable.lean`)

`EParserSpec` and `REPred kleB` are proved, not hypotheses, from here on: the guards below pin
the UNCONDITIONAL forms of the bounds above, applied to those proofs. -/

set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.chaitin_bound_KB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_bound_KB

set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.chaitin_bound_KB_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_bound_KB_min

set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.chaitin_theorem_KB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theorem_KB

set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.chaitin_theorem_KB_RE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theorem_KB_RE

-- The enumerator is exhibited, not merely asserted to exist — `rePred_provable_chaitin_KB` unpacked
-- through `REPred.iff'` and `Nat.Partrec.Code.exists_code`.
set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.exists_enumerator_chaitin_KB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.exists_enumerator_chaitin_KB

-- Non-vacuity: `𝗣𝗔⁻` meets every instance binder `chaitin_theorem_KB` asks for, at once.
set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.chaitin_theorem_KB_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theorem_KB_nonvacuous

-- `KB`'s true-and-unprovable family, at the additive constant.
set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.chaitin_true_unprovable_KB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_true_unprovable_KB
