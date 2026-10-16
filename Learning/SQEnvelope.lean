module

public import Learning.SQObjects
public import Learning.SQBounds

/-!
# The SQ version-space envelope via Szörényi's maximality + packing

The statistical dimension `d_SQ` with Assumption A, and the SQ-based enumeration of a version
space. Mathematical route: Szörényi,
"Characterizing Statistical Query Learning: Simplified Notions and Proofs" (ALT 2009) — the
elementary maximality/packing argument (Def 2, §3, Prop 1), NOT the Fourier route.

This builds the BFJKMR-style version-space envelope
directly over the GENUINE statistical dimension (`SQObjects.sqDim`), discharging the MODELED
envelope premise `candidates r ≤ A · (d_SQ r)^m` that `SQBounds.candidates_polyBounded` takes as a
hypothesis. Two pieces of added content over `SQObjects.survivors_card_le_sqDim` (which
already handles the pairwise-SEPARATED survivor case):
  (a) the query schedule / covering family EXISTS — Szörényi's maximality (`exists_sq_net`);
  (b) a version-space size bound WITHOUT assuming the survivors are pairwise separated
      (`subset_card_le_sqDim_of_ident`), gated on a clean CLASS-LEVEL identifiability hypothesis
      instead of a survivor-set-level separation hypothesis.

## The constant chain (the `τ / 2τ / 3τ` bookkeeping)
* pruning tolerance `2τ` (a survivor obeys `|ans φ i − o φ| ≤ 2τ` on every scheduled query);
* two survivors are therefore pairwise `4τ`-close on the schedule (`close_on_of_prune`, the abstract
  triangle-inequality analogue of Szörényi's Proposition 1 — see the "Departures" note below on the
  `6ε` correlational constant);
* the covering family (`exists_sq_net`) is a MAXIMAL `τ`-separated subfamily, so two candidates
  assigned to the same covering point are `2τ`-close on EVERY query (global triangle);
* identifiability `hident` at scale `2τ` (distinct candidates differ by `> 2τ` on some query) makes
  the covering-point assignment injective, so the version space embeds into the covering family and
  `V.card ≤ sqDim M τ ans`.

## What this DOES establish
* `close_on_of_prune` (Prop 1 analogue): survivors of the `2τ`-pruning rule against a
  τ-good oracle are pairwise `4τ`-close on the scheduled queries — they need NOT be pairwise
  separated, so the pigeonhole of `SQObjects.survivors_card_le_sqDim` does not apply directly.
* `exists_sq_net` (Szörényi's maximality, §3): every finite class `M` has a MAXIMAL `τ`-separated
  subfamily `S` with `S.card = sqDim M τ ans` that COVERS `M` — every candidate is `τ`-close (on
  every query) to some member of `S`.
* `subset_card_le_sqDim_of_ident` (the envelope proper): under class-level identifiability at scale
  `2τ`, ANY subfamily `V ⊆ M` — in particular the version space — has `V.card ≤ sqDim M τ ans`. The
  covering map `V → S` is injective by identifiability, so `V` embeds into a `τ`-separated family.
* `version_space_card_le` (the "version-space bound", assembled): the `2τ`-pruning survivor
  set is pairwise `4τ`-close on the schedule AND has `card ≤ sqDim M τ ans`.
* `subset_polyBounded_of_ident`: instantiates the modeled envelope premise
  (`SQBounds.candidates_polyBounded`'s `candidates ≤ A · d_SQ^m`) from the linear envelope
  with `A = m = 1` — closing the loop with the literal `PolyBounded` chain, exactly as
  `SQObjects.survivors_polyBounded_of_separated` does, but with class-level identifiability
  replacing the survivor-set separation hypothesis.
* `hident_load_bearing` (a guard): a near-duplicate witness
  proving `hident` load-bearing for `subset_card_le_sqDim_of_ident` — over `Fin N` (`N ≥ 2`) with a
  constant answer functional, `sqDim = 1` while `V.card = N`, so the envelope's conclusion is FALSE
  without identifiability, for every `N`.

## The identifiability hypothesis (named, flagged prominently)
`subset_card_le_sqDim_of_ident` / `subset_polyBounded_of_ident` assume
`hident : ∀ i ∈ M, ∀ j ∈ M, (∀ φ, |ans φ i − ans φ j| ≤ 2τ) → i = j` — "distinct candidate rules are
`2τ`-distinguishable on some query". It is a real hypothesis: with it, the covering map is
injective and the version space collapses onto a separated family. WITHOUT it, `|V|` is
UNBOUNDED by `sqDim` and the
query count — distinct candidates can share one answer functional (a near-duplicate cluster), so no
direct bound on `|V|` exists to prove (the `[−1,1]` per-query packing bounds only
the distinct `τ`-rounded answer-VECTORS on the schedule — the net — not the survivor count, and even
that count is exponential in the query number, not `poly`). Flagged, not hidden;
`hident_load_bearing` below guards the hypothesis with the near-duplicate witness.
The identifiability-FREE maintained-net envelope is already machine-checked, in the sibling module
this file imports: `SQObjects.version_space_net_envelope`. It is the FORCED object without `hident`,
not a sidestep of a harder-but-available direct `|V|` bound — no such bound exists.

## What this does NOT establish (out of scope / stays in prose; no overclaiming)
* Not a direct bound on `|V|` WITHOUT identifiability — none exists (a near-duplicate class makes
  `|V|` unbounded while `sqDim` stays `1`; witnessed below by `hident_load_bearing`). We deliver the
  LINEAR envelope `≤ sqDim` under identifiability; the identifiability-free case rides the net
  (`version_space_net_envelope`).
* Not Szörényi's Theorem 2 query lower bound `(dτ²−1)/2` (a nice-to-have companion needing the
  correlation/ℓ² geometry) — de-scoped.
* Not the concrete schedule for a named class (the `ans`, oracle `o`, and schedule `Qs` are abstract
  data), nor the single-trajectory → SQ-oracle reduction.
-/


@[expose] public section

namespace SQEnvelope

open SQObjects Filter

variable {ι Q : Type*}

/-- Triangle helper: two reals each within `d` of a common `c` are within `2d` of each other. -/
private lemma abs_sub_le_two_mul (a b c d : ℝ) (h1 : |a - c| ≤ d) (h2 : |b - c| ≤ d) :
    |a - b| ≤ 2 * d := by
  have h3 : |a - b| ≤ |a - c| + |c - b| := abs_sub_le a c b
  have h4 : |c - b| = |b - c| := abs_sub_comm c b
  rw [h4] at h3
  linarith

/-- **Closeness transitivity — general constant** (Szörényi Prop 1, abstract form): if `i` and `j`
each answer within `c` of the same oracle answers on every scheduled query `φ ∈ Qs`, then `i` and
`j` are pairwise `2c`-close on `Qs`. Pure triangle inequality (the abstract analogue of the `⟨·,·⟩`
inner-product bound; see the module docstring on the `6ε` correlational constant). -/
theorem pairwise_close_on_of_oracle (c : ℝ) (ans : Q → ι → ℝ) (o : Q → ℝ) (Qs : Finset Q)
    {i j : ι}
    (hi : ∀ φ ∈ Qs, |ans φ i - o φ| ≤ c) (hj : ∀ φ ∈ Qs, |ans φ j - o φ| ≤ c) :
    ∀ φ ∈ Qs, |ans φ i - ans φ j| ≤ 2 * c := fun φ hφ =>
  abs_sub_le_two_mul (ans φ i) (ans φ j) (o φ) c (hi φ hφ) (hj φ hφ)

/-- **The version space is a close cluster on the schedule**: survivors of the
`2τ`-pruning rule (`|ans φ i − o φ| ≤ 2τ` on every scheduled query) are pairwise `4τ`-close on the
schedule. So the version space need NOT be pairwise separated — the survivor pigeonhole of
`SQObjects.survivors_card_le_sqDim` does not apply directly, and the envelope needs the covering
argument below. -/
theorem close_on_of_prune (τ : ℝ) (ans : Q → ι → ℝ) (o : Q → ℝ) (Qs : Finset Q) {i j : ι}
    (hi : ∀ φ ∈ Qs, |ans φ i - o φ| ≤ 2 * τ) (hj : ∀ φ ∈ Qs, |ans φ j - o φ| ≤ 2 * τ) :
    ∀ φ ∈ Qs, |ans φ i - ans φ j| ≤ 4 * τ := by
  intro φ hφ
  have h := pairwise_close_on_of_oracle (2 * τ) ans o Qs hi hj φ hφ
  linarith

open scoped Classical in
/-- **Szörényi's maximality (the covering family exists).** Every finite class `M` has a
MAXIMAL `τ`-separated subfamily `S`: `S` is itself a `SepFam` with `S.card = sqDim M τ ans`, and by
maximality it COVERS `M` — every candidate `i ∈ M` is `τ`-close on EVERY query to some `j ∈ S`
(otherwise `i` could be added to `S`, contradicting maximum cardinality). -/
theorem exists_sq_net (M : Finset ι) (τ : ℝ) (hτ : 0 ≤ τ) (ans : Q → ι → ℝ) :
    ∃ S : Finset ι, S ⊆ M ∧ SepFam M τ ans S ∧ S.card = sqDim M τ ans ∧
      ∀ i ∈ M, ∃ j ∈ S, ∀ φ, |ans φ i - ans φ j| ≤ τ := by
  have hPne : (M.powerset.filter (SepFam M τ ans)).Nonempty := by
    refine ⟨∅, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset M, Finset.empty_subset M,
      fun i hi => absurd hi (Finset.notMem_empty i)⟩
  obtain ⟨S, hSmem, hSsup⟩ := Finset.exists_mem_eq_sup _ hPne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hSmem
  obtain ⟨hSM, hSsep⟩ := hSmem
  have hScard : S.card = sqDim M τ ans := hSsup.symm
  refine ⟨S, hSM, hSsep, hScard, ?_⟩
  intro i hiM
  by_cases hiS : i ∈ S
  · exact ⟨i, hiS, fun φ => by rw [sub_self, abs_zero]; exact hτ⟩
  · by_contra hcon
    simp only [not_exists, not_and, not_forall, not_le] at hcon
    -- hcon : ∀ j ∈ S, ∃ φ, τ < |ans φ i - ans φ j|  (i is separated from every net member)
    have hins : SepFam M τ ans (insert i S) := by
      refine ⟨Finset.insert_subset hiM hSM, ?_⟩
      intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨φ, hφ⟩ := hcon b hb
        exact ⟨φ, hφ⟩
      · obtain ⟨φ, hφ⟩ := hcon a ha
        refine ⟨φ, ?_⟩
        change τ < |ans φ a - ans φ b|
        rw [abs_sub_comm]
        exact hφ
      · exact hSsep.2 a ha b hb hab
    have hmem : insert i S ∈ M.powerset.filter (SepFam M τ ans) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hins.1, hins⟩
    have hle := Finset.le_sup (f := Finset.card) hmem
    rw [Finset.card_insert_of_notMem hiS, hSsup] at hle
    omega

open scoped Classical in
/-- **The version-space envelope proper.** Under class-level identifiability at scale `2τ`
(`hident`: distinct candidates differ by `> 2τ` on some query), ANY subfamily `V ⊆ M` — in
particular the `2τ`-pruning version space — satisfies `V.card ≤ sqDim M τ ans`.

Proof (Szörényi packing): take the maximal `τ`-separated covering family `S` (`exists_sq_net`), with
`S.card = sqDim`. Assign each `v ∈ V` a covering point `f v ∈ S` that it is `τ`-close to. If
`f a = f b`, then `a` and `b` are both `τ`-close to that point, hence `2τ`-close on every query, so
`hident` forces `a = b`: the assignment is injective on `V`, and `V` embeds into `S`.

The identifiability hypothesis is where "distinct rules are distinguishable" lives; removing it and
bounding the covering-ball clusters by an extra `poly(k)` factor is the harder BFJKMR clustering
argument (module docstring). -/
theorem subset_card_le_sqDim_of_ident (M : Finset ι) (τ : ℝ) (hτ : 0 ≤ τ) (ans : Q → ι → ℝ)
    (V : Finset ι) (hVM : V ⊆ M)
    (hident : ∀ i ∈ M, ∀ j ∈ M, (∀ φ, |ans φ i - ans φ j| ≤ 2 * τ) → i = j) :
    V.card ≤ sqDim M τ ans := by
  obtain ⟨S, _hSM, _hSsep, hScard, hcover⟩ := exists_sq_net M τ hτ ans
  -- covering-point assignment
  set f : ι → ι := fun i => if h : i ∈ V then Classical.choose (hcover i (hVM h)) else i with hfdef
  have hfmem : ∀ i ∈ V, f i ∈ S := by
    intro i hi
    have hspec := Classical.choose_spec (hcover i (hVM hi))
    simp only [hfdef, dite_eq_left hi]
    exact hspec.1
  have hfclose : ∀ i ∈ V, ∀ φ, |ans φ i - ans φ (f i)| ≤ τ := by
    intro i hi φ
    have hspec := Classical.choose_spec (hcover i (hVM hi))
    simp only [hfdef, dite_eq_left hi]
    exact hspec.2 φ
  have hmaps : Set.MapsTo f ↑V ↑S := by
    intro i hi
    rw [Finset.mem_coe] at hi ⊢
    exact hfmem i hi
  have hinj : Set.InjOn f ↑V := by
    intro a ha b hb hfab
    rw [Finset.mem_coe] at ha hb
    have hca := hfclose a ha
    have hcb := hfclose b hb
    have hclose2 : ∀ φ, |ans φ a - ans φ b| ≤ 2 * τ := by
      intro φ
      have h2 := hcb φ
      rw [← hfab] at h2
      exact abs_sub_le_two_mul (ans φ a) (ans φ b) (ans φ (f a)) τ (hca φ) h2
    exact hident a (hVM ha) b (hVM hb) hclose2
  calc V.card ≤ S.card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = sqDim M τ ans := hScard

/-- **The version-space bound, assembled.** The `2τ`-pruning survivor set `V` (against a
τ-good oracle `o` over schedule `Qs`) is (i) pairwise `4τ`-close on the schedule and (ii) has
`V.card ≤ sqDim M τ ans`, under class-level identifiability at scale `2τ`. Part (i) is
`close_on_of_prune`; part (ii) is `subset_card_le_sqDim_of_ident`. -/
theorem version_space_card_le (M : Finset ι) (τ : ℝ) (hτ : 0 ≤ τ) (ans : Q → ι → ℝ)
    (o : Q → ℝ) (Qs : Finset Q) (V : Finset ι) (hVM : V ⊆ M)
    (hsurv : ∀ i ∈ V, ∀ φ ∈ Qs, |ans φ i - o φ| ≤ 2 * τ)
    (hident : ∀ i ∈ M, ∀ j ∈ M, (∀ φ, |ans φ i - ans φ j| ≤ 2 * τ) → i = j) :
    (∀ i ∈ V, ∀ j ∈ V, ∀ φ ∈ Qs, |ans φ i - ans φ j| ≤ 4 * τ)
      ∧ V.card ≤ sqDim M τ ans :=
  ⟨fun i hi j hj => close_on_of_prune τ ans o Qs (hsurv i hi) (hsurv j hj),
    subset_card_le_sqDim_of_ident M τ hτ ans V hVM hident⟩

/-- **The modeled envelope premise, discharged.** Reusing
`SQBounds.candidates_polyBounded` verbatim with the `A = m = 1` envelope supplied by
`subset_card_le_sqDim_of_ident`: if the GENUINE statistical dimension `sqDim (Mfam r) τ (ansfam r)`
is polynomially bounded (Assumption A) and each class `Mfam r` is `2τ`-identifiable, then the
version space `Vfam r ⊆ Mfam r` is `poly(r)`. This is exactly
`SQObjects.survivors_polyBounded_of_separated` with class-level identifiability `hident` in place of
the survivor-set separation hypothesis `hsep`, closing the loop with the literal `PolyBounded`
chain. -/
theorem subset_polyBounded_of_ident (τ : ℝ) (hτ : 0 ≤ τ)
    (Mfam Vfam : ℝ → Finset ι) (ansfam : ℝ → Q → ι → ℝ)
    (hVM : ∀ r, Vfam r ⊆ Mfam r)
    (hident : ∀ r, ∀ i ∈ Mfam r, ∀ j ∈ Mfam r,
      (∀ φ, |ansfam r φ i - ansfam r φ j| ≤ 2 * τ) → i = j)
    (hpoly : SQBounds.PolyBounded (fun r => (sqDim (Mfam r) τ (ansfam r) : ℝ))) :
    SQBounds.PolyBounded (fun r => ((Vfam r).card : ℝ)) := by
  refine SQBounds.candidates_polyBounded _ _ hpoly 1 1 (by norm_num) ?_ ?_
  · filter_upwards with r
    have hle := subset_card_le_sqDim_of_ident (Mfam r) τ hτ (ansfam r) (Vfam r) (hVM r) (hident r)
    have hcast : ((Vfam r).card : ℝ) ≤ (sqDim (Mfam r) τ (ansfam r) : ℝ) := by exact_mod_cast hle
    simpa using hcast
  · filter_upwards with r
    positivity

open scoped Classical in
/-- **Guard: `hident` in `subset_card_le_sqDim_of_ident` is load-bearing** (the near-duplicate
witness). Over `Fin N` (`N ≥ 2`) with a CONSTANT answer functional (`ans _ i = 0`
for every query and every candidate — the generic case for distinct programs computing the same
function, which is exactly why identifiability is a real hypothesis rather than a formality), no
query separates any two candidates, so `sqDim univ 1 ans = 1`; but the whole class is its own
`2τ`-survivor set, so `V.card = N`. `hident` fails here (every pair shares an identical answer, so
`2τ`-closeness never forces equality), and the envelope's conclusion is FALSE for every `N ≥ 2`:
`|V|` is unbounded while `sqDim` stays `1`: without
identifiability the direct `|V|` bound does not merely stay unproved, it fails, and the maintained
net (`SQObjects.version_space_net_envelope`) is the forced object. -/
theorem hident_load_bearing (N : ℕ) (hN : 2 ≤ N) :
    ∃ (M V : Finset (Fin N)) (τ : ℝ) (ans : Unit → Fin N → ℝ),
      0 ≤ τ ∧ V ⊆ M ∧ ¬ V.card ≤ sqDim M τ ans ∧
      ¬ (∀ i ∈ M, ∀ j ∈ M, (∀ φ, |ans φ i - ans φ j| ≤ 2 * τ) → i = j) := by
  have h0N : 0 < N := by omega
  have h1N : 1 < N := by omega
  have hi01 : (⟨0, h0N⟩ : Fin N) ≠ ⟨1, h1N⟩ := by
    simp only [ne_eq, Fin.mk.injEq]
    omega
  refine ⟨Finset.univ, Finset.univ, 1, fun _ _ => 0, zero_le_one, Finset.Subset.refl _, ?_, ?_⟩
  · have hdim : sqDim (Finset.univ : Finset (Fin N)) 1
        (fun (_ : Unit) (_ : Fin N) => (0:ℝ)) = 1 := by
      apply le_antisymm
      · apply Finset.sup_le
        intro S hS
        rw [Finset.mem_filter, Finset.mem_powerset] at hS
        by_contra hcard
        push Not at hcard
        obtain ⟨i, hiS, j, hjS, hij⟩ := Finset.one_lt_card.mp hcard
        obtain ⟨φ, hφ⟩ := hS.2.2 i hiS j hjS hij
        unfold Separates at hφ
        simp only [sub_self, abs_zero] at hφ
        linarith
      · have hmem : ({(⟨0, h0N⟩ : Fin N)} : Finset (Fin N)) ∈
            (Finset.univ : Finset (Fin N)).powerset.filter
              (SepFam Finset.univ 1 (fun (_ : Unit) (_ : Fin N) => (0:ℝ))) := by
          rw [Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.subset_univ _, Finset.subset_univ _,
            fun i hi j hj hij => absurd
              ((Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm) hij⟩
        have hle := Finset.le_sup (f := Finset.card) hmem
        rw [Finset.card_singleton] at hle
        exact hle
    rw [hdim, Finset.card_univ, Fintype.card_fin]
    omega
  · intro hident
    exact hi01 (hident ⟨0, h0N⟩ (Finset.mem_univ _) ⟨1, h1N⟩ (Finset.mem_univ _)
      (fun _ => by norm_num))

end SQEnvelope
