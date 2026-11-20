module

public import Mathlib.Computability.PartrecCode

/-!
# Structural evaluation laws for `Nat.Partrec.Code`

Upstream states `Nat.Partrec.Code.eval` at the recursion constructor (`eval_prec_zero`,
`eval_prec_succ`) and at the derived codes (`eval_const`, `eval_id`, `eval_curry`), but not at
`zero`, `succ`, `comp`, `left`, `right` or `pair`, whose clauses are left to unfold definitionally
at each use. This module states those six, once.

* `eval_zero`, `eval_succ` — the two base codes output `0` and the successor of the input.
* `eval_comp` — composition in `bind` form: `comp a b` runs `b` and then `a` on its output.
* `eval_comp_some` — composition in the common case where the inner code converges: once `b`
  outputs `v` on `j`, running `comp a b` on `j` is running `a` on `v`.
* `eval_left'`, `eval_right'` — the two projections are the halves of `Nat.unpair`.
* `eval_pair_bind` — pairing in `bind`/`map` form. Upstream's clause is written with `<*>`, which
  does not meet a `bind`-shaped goal.

It also holds the output-from-nothing convention shared by the complexity measures built on codes:
`KolmogorovComplexity.Computes` (a code computes `x` when it outputs `x` on input `0`),
`KolmogorovComplexity.const_computes` and `KolmogorovComplexity.Computes.unique` (a code computes
at most one value).

The module stays deliberately light: it knows codes and their evaluation, and nothing about the
step-counting cost model built on top of them.
-/

-- "deliberately light: … nothing about the step-counting cost model"

@[expose] public section

assert_not_exists TimeCost.tc

namespace CodeEvalLaws

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- Base eval law: `zero` outputs `0` on every input. -/
theorem eval_zero (n : ℕ) : eval zero n = Part.some 0 := rfl

/-- Base eval law: `succ` outputs the successor of its input. -/
theorem eval_succ (n : ℕ) : eval succ n = Part.some (n + 1) := rfl

/-- `eval`'s `comp` clause in `bind` form: `comp a b` runs `b` on `j` and then `a` on whatever `b`
outputs. -/
theorem eval_comp (a b : Code) (j : ℕ) : eval (comp a b) j = (eval b j).bind (eval a) := rfl

/-- If `b` outputs `v` on input `j`, then `comp a b` runs `a` on `v` (the `comp` eval law is
definitional, then `Part.bind_some`). -/
theorem eval_comp_some {a b : Code} {j v : ℕ} (hv : eval b j = Part.some v) :
    eval (comp a b) j = eval a v := by
  change eval b j >>= eval a = eval a v
  rw [hv]
  exact Part.bind_some v (eval a)

/-- Base eval law: `left` is left unpairing. -/
theorem eval_left' (x : ℕ) : eval left x = Part.some x.unpair.1 := rfl

/-- Base eval law: `right` is right unpairing. -/
theorem eval_right' (x : ℕ) : eval right x = Part.some x.unpair.2 := rfl

/-- `eval`'s `pair` clause in bind/map form (upstream states it with `<*>`). -/
theorem eval_pair_bind (cf cg : Code) (n : ℕ) :
    eval (pair cf cg) n = (eval cf n).bind fun u => (eval cg n).map (Nat.pair u) := by
  ext x
  simp [eval, Seq.seq]

end CodeEvalLaws

namespace KolmogorovComplexity

open Nat.Partrec Nat.Partrec.Code

/-- `c` computes `x`, output-from-nothing convention: run on input `0`. -/
def Computes (c : Code) (x : ℕ) : Prop := c.eval 0 = Part.some x

/-- A code computes at most one value: its output on input `0` is a single `Part.some`. -/
theorem Computes.unique {c : Code} {x y : ℕ} (hx : Computes c x) (hy : Computes c y) : x = y := by
  unfold Computes at hx hy
  exact Part.some_injective (hx.symm.trans hy)

/-- The constant code outputs `x` from any input. -/
theorem const_computes (x : ℕ) : Computes (Code.const x) x := by
  simp [Computes, eval_const]

end KolmogorovComplexity
