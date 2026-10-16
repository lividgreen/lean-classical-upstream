module

public import Realizability.Realizability
public import Realizability.RealizabilityCCC
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Finite coproducts in the realizability category `Asm`

`Realizability/RealizabilityCCC.lean` built the carrier `RealizabilityCCC.Asm` — assemblies over
Kleene's first PCA (`Nat.Partrec.Code`) — and proved it **Cartesian closed** (terminal + products +
exponentials). This file adds the missing **finite coproducts** (initial object + binary coproduct
with its copairing universal property) on that same carrier, and the finite carrier assembly
`finAsm`.

## Why this is new infrastructure (upstreamable)
The 2026 realizability sweep found **no** realizability-coproduct in Lean/Mathlib (nor a
realizability category at all beyond what the `Realizability` modules build here). Coproducts of
assemblies are the standard "tagged union" construction: a realizer of a left/right injection is a
code carrying a **tag** (`0`/`1`, via `Nat.pair`) alongside a realizer of the injected element;
copairing runs one of two realizers according to the tag (`Partrec.cond`). We build that layer
directly on `Nat.Partrec.Code`, reusing the universal machinery of
`Realizability/Realizability.lean` (`exists_code`, `Code.eval_part`). It is genuinely upstreamable.

## What this establishes
* `initialAsm` — the empty assembly; `initialAsm_isInitial` : it is an **initial object** of `Asm`
  (the unique map out is `Empty.elim`, trackable vacuously; uniqueness is `Empty → B` subsingleton).
* `coprodAsm A B` — the binary coproduct: carrier `A ⊕ B`, a code realizes `inl a` iff it is
  `Nat.pair 0 (a-realizer)` and `inr b` iff `Nat.pair 1 (b-realizer)`.
* `inl`/`inr` are **tracked** morphisms, and `coprod_universal` is the copairing universal property
  — existence **and** uniqueness of the mediating realized morphism `[f, g] : A ⊕ B ⟶ C`.
* `finAsm M`, `trackable_of_fin_dom`: the finite assembly on `Fin (M+1)`, each element realized by
  its own value, and the fact that every function out of it is a morphism of `Asm`.
-/


@[expose] public section

namespace RealizabilityCoproduct

open RealizabilityCCC Nat.Partrec CategoryTheory CategoryTheory.Limits

/-! ### The initial object: the empty assembly -/

/-- The **initial assembly**: the empty carrier. Realizability is vacuous, and the unique map out of
it (`Empty.elim`) is trackable by any code. This is the standard initial object of a category of
assemblies. -/
def initialAsm : Asm where
  carrier := Empty
  realizes := fun _ x => x.elim
  realized := fun x => x.elim

/-- **`initialAsm` is an initial object of `Asm`.** For every assembly `B` the unique morphism
`initialAsm ⟶ B` has underlying map `Empty.elim`, trackable vacuously (no element of `Empty` has a
realizer, so *every* code tracks it — we pick `idCode`); uniqueness is `Empty → B.carrier` being a
subsingleton. -/
def initialAsm_isInitial : IsInitial initialAsm :=
  IsInitial.ofUniqueHom
    (fun B => ⟨Empty.elim, idCode, fun x _ _ => x.elim⟩)
    (fun _ _ => by apply Subtype.ext; funext x; exact x.elim)

/-! ### Binary coproducts: the tagged-union assembly -/

/-- **Coproduct assembly** `A ⊕ B`: a code realizes `inl a` iff its first `Nat.pair` component is
the tag `0` and its second realizes `a`; symmetrically `inr b` with tag `1`. -/
def coprodAsm (A B : Asm) : Asm where
  carrier := A.carrier ⊕ B.carrier
  realizes n x :=
    match x with
    | Sum.inl a => n.unpair.1 = 0 ∧ A.realizes n.unpair.2 a
    | Sum.inr b => n.unpair.1 = 1 ∧ B.realizes n.unpair.2 b
  realized x := by
    cases x with
    | inl a =>
        obtain ⟨na, ha⟩ := A.realized a
        exact ⟨Nat.pair 0 na, by
          change (Nat.pair 0 na).unpair.1 = 0 ∧ A.realizes (Nat.pair 0 na).unpair.2 a
          rw [Nat.unpair_pair]; exact ⟨rfl, ha⟩⟩
    | inr b =>
        obtain ⟨nb, hb⟩ := B.realized b
        exact ⟨Nat.pair 1 nb, by
          change (Nat.pair 1 nb).unpair.1 = 1 ∧ B.realizes (Nat.pair 1 nb).unpair.2 b
          rw [Nat.unpair_pair]; exact ⟨rfl, hb⟩⟩

@[simp] theorem coprodAsm_realizes_inl (A B : Asm) (n : ℕ) (a : A.carrier) :
    (coprodAsm A B).realizes n (Sum.inl a) ↔ (n.unpair.1 = 0 ∧ A.realizes n.unpair.2 a) := Iff.rfl

@[simp] theorem coprodAsm_realizes_inr (A B : Asm) (n : ℕ) (b : B.carrier) :
    (coprodAsm A B).realizes n (Sum.inr b) ↔ (n.unpair.1 = 1 ∧ B.realizes n.unpair.2 b) := Iff.rfl

/-! ### The injection and copairing realizer codes -/

/-- A code that tags an argument with `0`: `r · n = ⟨0, n⟩`. Built from `Nat.pair 0 ·` via
`exists_code`. -/
theorem exists_inlCode : ∃ r : ℕ, ∀ n, ap r n = Part.some (Nat.pair 0 n) := by
  have hc : Computable (fun n => Nat.pair 0 n) :=
    (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id).to_comp
  obtain ⟨c, hc'⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hc)
  exact ⟨Encodable.encode c, fun n => by rw [ap_encode]; exact congrFun hc' n⟩

/-- A code that tags an argument with `1`: `r · n = ⟨1, n⟩`. -/
theorem exists_inrCode : ∃ r : ℕ, ∀ n, ap r n = Part.some (Nat.pair 1 n) := by
  have hc : Computable (fun n => Nat.pair 1 n) :=
    (Primrec₂.natPair.comp (Primrec.const 1) Primrec.id).to_comp
  obtain ⟨c, hc'⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hc)
  exact ⟨Encodable.encode c, fun n => by rw [ap_encode]; exact congrFun hc' n⟩

/-- The **copairing realizer**: a single code that reads the tag `n.unpair.1` and runs `rf` on the
payload if the tag is `0`, else `rg`. Built by *arithmetically selecting* the realizer code
(`Primrec.ite` at the ℕ level) and feeding it to the universal evaluator
`Realizability.universal_evaluator`. -/
theorem exists_copairCode (rf rg : ℕ) :
    ∃ r : ℕ, ∀ n, ap r n =
      (if n.unpair.1 = 0 then ap rf n.unpair.2 else ap rg n.unpair.2) := by
  obtain ⟨E, hE⟩ := Realizability.universal_evaluator
  have hsel : PrimrecPred (fun n : ℕ => n.unpair.1 = 0) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)
  have harg : Computable (fun n : ℕ => Nat.pair (if n.unpair.1 = 0 then rf else rg) n.unpair.2) :=
    (Primrec₂.natPair.comp
      (Primrec.ite hsel (Primrec.const rf) (Primrec.const rg))
      (Primrec.snd.comp Primrec.unpair)).to_comp
  have hpf : Partrec
      (fun n : ℕ => E.eval (Nat.pair (if n.unpair.1 = 0 then rf else rg) n.unpair.2)) :=
    Code.eval_part.comp (Computable.const E) harg
  obtain ⟨c, hc'⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hpf)
  refine ⟨Encodable.encode c, fun n => ?_⟩
  rw [ap_encode, congrFun hc' n]
  by_cases h : n.unpair.1 = 0
  · simp only [ite_eq_left h]
    have hEr := hE (Denumerable.ofNat Code rf) n.unpair.2
    rw [Denumerable.encode_ofNat] at hEr
    exact hEr
  · simp only [ite_eq_right h]
    have hEr := hE (Denumerable.ofNat Code rg) n.unpair.2
    rw [Denumerable.encode_ofNat] at hEr
    exact hEr

/-! Chosen injection/copairing codes. Each is a realizer picked from the corresponding existence
lemma, so the realizers are genuine values; `.choose` uses only `Classical.choice`. -/

/-- The realizer of the left injection: it tags its input with `0` (`ap_inlCode`). -/
noncomputable def inlCode : ℕ := exists_inlCode.choose

/-- The realizer of the right injection: it tags its input with `1` (`ap_inrCode`). -/
noncomputable def inrCode : ℕ := exists_inrCode.choose

/-- The realizer of the copairing of two tracked maps: on a tagged input it dispatches to `rf` or
`rg` according to the tag (`ap_copairCode`). -/
noncomputable def copairCode (rf rg : ℕ) : ℕ := (exists_copairCode rf rg).choose

theorem ap_inlCode (n : ℕ) : ap inlCode n = Part.some (Nat.pair 0 n) := exists_inlCode.choose_spec n
theorem ap_inrCode (n : ℕ) : ap inrCode n = Part.some (Nat.pair 1 n) := exists_inrCode.choose_spec n

theorem ap_copairCode (rf rg n : ℕ) :
    ap (copairCode rf rg) n =
      (if n.unpair.1 = 0 then ap rf n.unpair.2 else ap rg n.unpair.2) :=
  (exists_copairCode rf rg).choose_spec n

/-! ### Injections and copairing are tracked -/

/-- The left injection `Sum.inl` is tracked, by `inlCode` (tag `0`). -/
theorem tracks_inl (A B : Asm) : Tracks A (coprodAsm A B) inlCode Sum.inl := by
  intro a n hn
  refine ⟨Nat.pair 0 n, by rw [ap_inlCode]; exact Part.mem_some _, ?_⟩
  rw [coprodAsm_realizes_inl, Nat.unpair_pair]
  exact ⟨rfl, hn⟩

/-- The right injection `Sum.inr` is tracked, by `inrCode` (tag `1`). -/
theorem tracks_inr (A B : Asm) : Tracks B (coprodAsm A B) inrCode Sum.inr := by
  intro b n hn
  refine ⟨Nat.pair 1 n, by rw [ap_inrCode]; exact Part.mem_some _, ?_⟩
  rw [coprodAsm_realizes_inr, Nat.unpair_pair]
  exact ⟨rfl, hn⟩

/-- Copairing preserves tracking: if `rf` tracks `f : A → C` and `rg` tracks `g : B → C`, then
`copairCode rf rg` tracks `[f, g] = Sum.elim f g : A ⊕ B → C`. -/
theorem tracks_copair {A B C : Asm} {rf rg : ℕ} {f : A.carrier → C.carrier}
    {g : B.carrier → C.carrier}
    (hrf : Tracks A C rf f) (hrg : Tracks B C rg g) :
    Tracks (coprodAsm A B) C (copairCode rf rg) (Sum.elim f g) := by
  intro x n hn
  cases x with
  | inl a =>
      rw [coprodAsm_realizes_inl] at hn
      obtain ⟨htag, ha⟩ := hn
      obtain ⟨m, hm, hc⟩ := hrf a n.unpair.2 ha
      refine ⟨m, ?_, hc⟩
      rw [ap_copairCode, ite_eq_left htag]
      exact hm
  | inr b =>
      rw [coprodAsm_realizes_inr] at hn
      obtain ⟨htag, hb⟩ := hn
      obtain ⟨m, hm, hc⟩ := hrg b n.unpair.2 hb
      refine ⟨m, ?_, hc⟩
      rw [ap_copairCode, ite_eq_right (by omega)]
      exact hm

/-! ### The coproduct as a categorical object of `Asm` -/

/-- The left injection as a morphism `A ⟶ A ⊕ B`. -/
def inl (A B : Asm) : A ⟶ coprodAsm A B := ⟨Sum.inl, inlCode, tracks_inl A B⟩

/-- The right injection as a morphism `B ⟶ A ⊕ B`. -/
def inr (A B : Asm) : B ⟶ coprodAsm A B := ⟨Sum.inr, inrCode, tracks_inr A B⟩

/-- The copairing (mediating) morphism `[f, g] : A ⊕ B ⟶ C`. -/
noncomputable def copair {A B C : Asm} (f : A ⟶ C) (g : B ⟶ C) : coprodAsm A B ⟶ C :=
  ⟨Sum.elim f.1 g.1, copairCode f.2.choose g.2.choose,
    tracks_copair f.2.choose_spec g.2.choose_spec⟩

@[simp] theorem inl_apply (A B : Asm) (a : A.carrier) : (inl A B).1 a = Sum.inl a := rfl
@[simp] theorem inr_apply (A B : Asm) (b : B.carrier) : (inr A B).1 b = Sum.inr b := rfl
@[simp] theorem copair_apply {A B C : Asm} (f : A ⟶ C) (g : B ⟶ C) (x : A.carrier ⊕ B.carrier) :
    (copair f g).1 x = Sum.elim f.1 g.1 x := rfl

/-- **The copairing universal property (finite coproduct on the genuine carrier).** For every pair
`f : A ⟶ C`, `g : B ⟶ C` there is a *unique* realized morphism `u : A ⊕ B ⟶ C` with
`u ∘ inl = f` and `u ∘ inr = g` (stated pointwise). Existence is `copair f g`; uniqueness is
extensional (morphism equality in `Asm` is function equality, the realizer existentially
quantified), by cases on `Sum`. -/
theorem coprod_universal {A B C : Asm} (f : A ⟶ C) (g : B ⟶ C) :
    ∃! u : coprodAsm A B ⟶ C,
      (∀ a, u.1 (Sum.inl a) = f.1 a) ∧ (∀ b, u.1 (Sum.inr b) = g.1 b) := by
  refine ⟨copair f g, ⟨fun _ => rfl, fun _ => rfl⟩, ?_⟩
  intro t ht
  apply Subtype.ext
  funext x
  cases x with
  | inl a => exact ht.1 a
  | inr b => exact ht.2 b

/-! ### The finite carrier assembly and finite-domain trackability -/

/-- The finite assembly on `Fin (M+1)`, each element realized by (exactly) its own value. -/
def finAsm (M : ℕ) : Asm where
  carrier := Fin (M + 1)
  realizes n k := n = k.val
  realized k := ⟨k.val, rfl⟩

@[simp] theorem finAsm_realizes (M : ℕ) (n : ℕ) (k : Fin (M + 1)) :
    (finAsm M).realizes n k ↔ n = k.val := Iff.rfl

/-- **Finite-domain trackability.** Every function out of the finite assembly `finAsm M` is
trackable (a morphism of `Asm`) — the realizer is a finite table keyed on the input value, extracted
via `Realizability.tableFn` and `Nat.Partrec.Code.exists_code`. This is the `Asm`-level counterpart
of `Realizability.realizes_of_finite`. -/
theorem trackable_of_fin_dom (M : ℕ) (B : Asm) (f : Fin (M + 1) → B.carrier) :
    Trackable (finAsm M) B f := by
  classical
  set pts : List (ℕ × ℕ) :=
    (Finset.univ.toList).map (fun k : Fin (M + 1) => (k.val, (B.realized (f k)).choose)) with hpts
  obtain ⟨c, hc⟩ :=
    Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp (Realizability.tableFn_primrec pts).to_comp)
  refine ⟨Encodable.encode c, fun (k : Fin (M + 1)) n hn => ?_⟩
  have hnk : n = k.val := hn
  subst hnk
  refine ⟨(B.realized (f k)).choose, ?_, (B.realized (f k)).choose_spec⟩
  rw [ap_encode]
  have hmem : (k.val, (B.realized (f k)).choose) ∈ pts := by
    rw [hpts, List.mem_map]
    exact ⟨k, Finset.mem_toList.mpr (Finset.mem_univ k), rfl⟩
  have huniq : ∀ k' v', (k', v') ∈ pts → k' = k.val → v' = (B.realized (f k)).choose := by
    intro k' v' hk'mem hk'eq
    rw [hpts, List.mem_map] at hk'mem
    obtain ⟨j, _, hj⟩ := hk'mem
    rw [Prod.mk.injEq] at hj
    obtain ⟨hj1, hj2⟩ := hj
    have hjk : j = k := Fin.val_injective (by rw [hj1, hk'eq])
    rw [← hj2, hjk]
  have hkey : Realizability.tableFn pts k.val = (B.realized (f k)).choose :=
    Realizability.tableFn_eval pts hmem huniq
  have heval : c.eval k.val = Part.some (Realizability.tableFn pts k.val) := by rw [hc]; rfl
  rw [heval, hkey]
  exact Part.mem_some _

end RealizabilityCoproduct
