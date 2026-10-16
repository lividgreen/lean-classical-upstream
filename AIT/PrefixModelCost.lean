module

public import AIT.EliasBound
public import AIT.PrefixComplexity
public import AIT.KolmogorovTimeBounded

/-!
# The model cost on the prefix machine: `KB` at `K_bitlen` and `KP`

Relates the plain bit-length complexity `K_bitlen` (`AIT/KolmogorovTimeBounded.lean`) and the
prefix complexity `KP` (`AIT/PrefixComplexity.lean`) to the universal prefix machine `KB`
(`AIT/PrefixMachine.lean`), which no other statement in the package connects.

## What this establishes

Four theorems relating `KB` to `K_bitlen` and `KP` — two of them over
hypotheses this module takes as given rather than proves, two unconditional corollaries
discharging every one of those hypotheses at a proved statement:

* `KB_le_K_bitlen_add_two_mul_size_of` — `KB x ≤ K_bitlen x + 2 * Nat.size (K_bitlen x) + c`, from
  a partial-map invariance for `KB` (`hinv`, stronger than the proved `PrefixMachine.KB_map_le`,
  which covers only total computable maps) and an unabsorbed Elias bound for `KB` (`helias`,
  distinct from the proved `PrefixMachine.KB_le_two_mul_size`). The route: the map
  `n ↦ (Denumerable.ofNat Code n).eval 0` is partial recursive (Mathlib's `Code.eval_part`
  composed with `Computable.ofNat` and a constant); `KolmogorovComplexity.exists_min_code` gives,
  for `x`, a code whose index is `K x` and which evaluates to `x` at that map, via
  `Denumerable.ofNat_encode`; `hinv` at that map gives `KB x ≤ KB (K x) + c₁`; `helias` at `K x`,
  rewritten along `KolmogorovComplexity.K_bitlen_eq`, gives the rest.
* `KB_le_K_bitlen_add_two_mul_size` — the first theorem's `hinv` and `helias` discharged at the
  proved `PrefixMachine.KB_partial_map_le` and `PrefixMachine.KB_le_size_add_two_mul_size_size`
  (`AIT/PrefixInvarianceKB.lean`, `AIT/EliasBound.lean`): unconditional.
* `KB_le_KP_of` — `KB x ≤ KP x + c`, from `hinv` alone (no `helias`): the same route to
  `KB x ≤ KB (K x) + c₁`, then the proved `PrefixMachine.KB_le_two_mul_size` at `K x` and
  `PrefixComplexity.KP_eq` with `Nat.size`'s monotonicity.
* `KB_le_KP` — `KB_le_KP_of`'s `hinv` discharged at the proved `PrefixMachine.KB_partial_map_le`
  (`AIT/PrefixInvarianceKB.lean`): `∃ c, ∀ x, KB x ≤ KP x + c`, unconditionally, needing no Elias
  bound at all.

## What this does NOT establish (flagged)

* `hinv` and `helias` are hypotheses of the two `_of` theorems only, not proved here — this
  module states what follows from them, nothing about their own status. Each of the two
  unconditional corollaries discharges every hypothesis it needs at a proved statement instead.
* This is not a sharpening of `PrefixMachine.KB_le_two_mul_size`: that bound and
  `KB_le_K_bitlen_add_two_mul_size_of`'s price `x` in different currencies (bit-length of `x`
  against bit-length of `x`'s own complexity), and neither dominates the other everywhere.
* No constant here is computed: every hypothesis's own constant is existential, and every combined
  constant, the unconditional corollaries' included, is a sum of those.
-/


@[expose] public section

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code KolmogorovComplexity PrefixComplexity

/-- **`KB` at `K_bitlen`.** From a partial-map invariance for `KB` and an unabsorbed Elias bound
for `KB` (both hypotheses; see the module docstring), `KB x ≤ K_bitlen x + 2 * Nat.size (K_bitlen x)
+ c`. -/
theorem KB_le_K_bitlen_add_two_mul_size_of
    (hinv : ∀ f : ℕ →. ℕ, Partrec f → ∃ c, ∀ x y, y ∈ f x → KB y ≤ KB x + c)
    (helias : ∃ c, ∀ n, KB n ≤ Nat.size n + 2 * Nat.size (Nat.size n) + c) :
    ∃ c, ∀ x, KB x ≤ K_bitlen x + 2 * Nat.size (K_bitlen x) + c := by
  have hfpartrec :
      Partrec (fun n : ℕ => Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) 0) :=
    Nat.Partrec.Code.eval_part.comp (Computable.ofNat Nat.Partrec.Code) (Computable.const 0)
  obtain ⟨c₁, hc₁⟩ := hinv _ hfpartrec
  obtain ⟨c₂, hc₂⟩ := helias
  refine ⟨c₁ + c₂, fun x => ?_⟩
  obtain ⟨cc, hcomp, hlen⟩ := exists_min_code x
  have hspec : Denumerable.ofNat Nat.Partrec.Code (K x) = cc := by
    rw [← hlen]; exact Denumerable.ofNat_encode cc
  have hmem : x ∈ Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code (K x)) 0 := by
    rw [hspec]; exact Part.eq_some_iff.mp hcomp
  have hstep1 : KB x ≤ KB (K x) + c₁ := hc₁ (K x) x hmem
  have hstep2 : KB (K x) ≤ Nat.size (K x) + 2 * Nat.size (Nat.size (K x)) + c₂ := hc₂ (K x)
  rw [← K_bitlen_eq x] at hstep2
  omega

/-- **`KB` at `K_bitlen`, unconditionally.** `KB_le_K_bitlen_add_two_mul_size_of`'s `hinv` and
`helias` discharged at the proved `PrefixMachine.KB_partial_map_le` and
`PrefixMachine.KB_le_size_add_two_mul_size_size`. -/
theorem KB_le_K_bitlen_add_two_mul_size :
    ∃ c, ∀ x, KB x ≤ K_bitlen x + 2 * Nat.size (K_bitlen x) + c :=
  KB_le_K_bitlen_add_two_mul_size_of (fun f hf => KB_partial_map_le f hf)
    KB_le_size_add_two_mul_size_size

/-- **`KB` at `KP`.** From a partial-map invariance for `KB` alone (no unabsorbed Elias bound
needed — that independence is the point of stating this separately), `KB x ≤ KP x + c`. -/
theorem KB_le_KP_of
    (hinv : ∀ f : ℕ →. ℕ, Partrec f → ∃ c, ∀ x y, y ∈ f x → KB y ≤ KB x + c) :
    ∃ c, ∀ x, KB x ≤ KP x + c := by
  have hfpartrec :
      Partrec (fun n : ℕ => Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) 0) :=
    Nat.Partrec.Code.eval_part.comp (Computable.ofNat Nat.Partrec.Code) (Computable.const 0)
  obtain ⟨c₁, hc₁⟩ := hinv _ hfpartrec
  obtain ⟨c₃, hc₃⟩ := KB_le_two_mul_size
  refine ⟨c₁ + c₃, fun x => ?_⟩
  obtain ⟨cc, hcomp, hlen⟩ := exists_min_code x
  have hspec : Denumerable.ofNat Nat.Partrec.Code (K x) = cc := by
    rw [← hlen]; exact Denumerable.ofNat_encode cc
  have hmem : x ∈ Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code (K x)) 0 := by
    rw [hspec]; exact Part.eq_some_iff.mp hcomp
  have hstep1 : KB x ≤ KB (K x) + c₁ := hc₁ (K x) x hmem
  have hstep2 : KB (K x) ≤ 2 * Nat.size (K x) + c₃ := hc₃ (K x)
  have hmono : Nat.size (K x) ≤ Nat.size (K x + 1) := Nat.size_le_size (by omega)
  have hKP : KP x = 2 * Nat.size (K x + 1) := KP_eq x
  omega

/-- **`KB` at `KP`, unconditionally.** `KB_le_KP_of`'s `hinv` discharged at the proved
`PrefixMachine.KB_partial_map_le` — the partial-map invariance is exactly what this particular
corollary needs, and nothing else. -/
theorem KB_le_KP : ∃ c, ∀ x, KB x ≤ KP x + c := KB_le_KP_of fun f hf => KB_partial_map_le f hf

end PrefixMachine
