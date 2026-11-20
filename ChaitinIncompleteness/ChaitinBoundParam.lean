module

public import ChaitinIncompleteness.KBEnumerable
public import AIT.PrefixInvarianceKB

/-!
# Chaitin's bound, uniform in a parameter

Chaitin's bound on the claims "`KB s > n`" that a computably enumerable family can show, in the
form "a system described by `z` proves no bound beyond `KB z` plus a constant", the constant
being one for the whole family.

## What this establishes
* `chaitin_bound_KB_param`: for a code `E` read as a parameterized enumerator, the claim set
  `{(s, n) | (E.eval (Nat.pair z (Nat.pair s n))).Dom}` at the parameter `z`, if it asserts only
  true lower bounds `n < KB s`, asserts none at or above `C + KB z`, with `C` depending on `E`
  alone. The proof curries `E` at `z`, whose code has prefix complexity at most `KB z` plus a
  constant by `KB_map_le`, and applies `chaitin_bound_KB_min` at that code.

## What this does NOT establish (flagged)
* The constant `C` is not uniform in `E`: it contains the code of `E` itself, as the bound for a
  single enumerator does.
-/


@[expose] public section

namespace KolmogorovComplexity

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity PrefixMachine

/-- **Chaitin's bound, uniform in the parameter.** For each code `E`, one constant `C` serves
every parameter `z`: if the claims `(s, n)` with `(E.eval (Nat.pair z (Nat.pair s n))).Dom` are
all true lower bounds `n < KB s`, then each such `n` is below `C + KB z`. -/
theorem chaitin_bound_KB_param (E : Code) : ∃ C : ℕ, ∀ z : ℕ,
    (∀ s n, (E.eval (Nat.pair z (Nat.pair s n))).Dom → n < KB s) →
    ∀ s n, (E.eval (Nat.pair z (Nat.pair s n))).Dom → n < C + KB z := by
  obtain ⟨c₀, hc₀⟩ := chaitin_bound_KB_min
  have hcurry : Computable fun z : ℕ => Encodable.encode (Code.curry E z) :=
    (Primrec.encode.comp
      (primrec₂_curry.comp (Primrec.const E) Primrec.id)).to_comp
  obtain ⟨c, hc⟩ := KB_map_le _ hcurry
  refine ⟨elen c₀ + c, fun z hsound s n hdom => ?_⟩
  have hsound' : ∀ s n, ((Code.curry E z).eval (Nat.pair s n)).Dom → n < KB s := by
    intro s n h
    rw [eval_curry] at h
    exact hsound s n h
  have hdom' : ((Code.curry E z).eval (Nat.pair s n)).Dom := by
    rw [eval_curry]
    exact hdom
  have := hc₀ (Code.curry E z) hsound' s n hdom'
  have := hc z
  omega

-- `chaitin_bound_KB_param`'s axiom guard is kept in `ChaitinIncompleteness/AxiomAudit.lean`.

end KolmogorovComplexity
