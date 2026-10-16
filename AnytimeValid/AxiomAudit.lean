module

public import AnytimeValid.Ville


/-!
# Axiom audit for the `AnytimeValid` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

-- Ville's inequality (`AnytimeValid/Ville.lean`). `ville_inequality` — Ville's inequality for a
-- non-negative supermartingale `Z` (`𝔼[Z 0] < ∞`): `μ{∃ n, λ ≤ Z_n} ≤ 𝔼[Z 0]/λ`, proved via
-- optional stopping on `-Z` (`Submartingale.expected_stoppedValue_mono`) + the hitting lower bound
-- + continuity from below — NOT via `maximal_ineq` (submartingale-locked). `ville_potential_budget`
-- — the `λ = 1/δ` corollary `μ{∃ n, 1/δ ≤ Z_n} ≤ δ` under `𝔼[Z 0] ≤ 1`.
/-- info: 'Ville.ville_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ville.ville_inequality

set_option linter.style.longLine false in
/-- info: 'Ville.ville_potential_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ville.ville_potential_budget
