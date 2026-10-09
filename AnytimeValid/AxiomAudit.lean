/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import AnytimeValid.Ville

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Axiom audit for the `AnytimeValid` library root

Each `#guard_msgs in #print axioms …` below fails the build if the axiom set of the named
declaration drifts from the asserted one.
-/

@[expose] public section

-- FV-G hardening (`AnytimeValid/Ville.lean`): the excursion control `hcharge` used to import is now a
-- PROVED theorem. `ville_inequality` — Ville's inequality for a non-negative supermartingale `Z`
-- (`𝔼[Z 0] < ∞`): `μ{∃ n, λ ≤ Z_n} ≤ 𝔼[Z 0]/λ`, proved via optional stopping on `-Z`
-- (`Submartingale.expected_stoppedValue_mono`) + the hitting lower bound + continuity from below —
-- NOT via `maximal_ineq` (submartingale-locked). `ville_potential_budget` — the `λ = 1/δ` corollary
-- `μ{∃ n, 1/δ ≤ Z_n} ≤ δ` under `𝔼[Z 0] ≤ 1`, the search-phase excursion budget of Appendix A Claim 2.
/-- info: 'Ville.ville_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ville.ville_inequality

/-- info: 'Ville.ville_potential_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ville.ville_potential_budget
