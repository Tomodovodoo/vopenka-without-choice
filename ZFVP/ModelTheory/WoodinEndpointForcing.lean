import ZFVP.ModelTheory.WoodinEndpointPoset
import ZFVP.ModelTheory.UniformForcingDefinitions
import ZFVP.ModelTheory.WoodinSupercompactRankZF

/-! The forcing relation of the endpoint poset `Q_δ`, at a Woodin-supercompact `δ`.

This is the Lean form of the paper's `lem:Woodin-endpoint-forcing`.  The W02 construction is
an open obligation, so it appears here as the explicit premise `WoodinIterationConstruction`
on every exported statement, exactly as the frozen W05 boundary asks.  Nothing below proves
that premise.

The formula that defines the relation is `uniformForcingLevelFormula pol k` from
`UniformForcingDefinitions`.  It is a single semisentence in the seven variables
`P R D n φ b q`, and both it and its Levy bound `uniformForcingLevelBound pol k` are
functions of the polarity and the level alone: no endpoint, poset, order or name set enters
them.  `woodinEndpoint_uniform` is the statement that carries this: the same formula and the
same bound define the relation at two different endpoints at once. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Endpoint laws out of the construction premise -/

/-- The endpoint invariant, read off the W02 exit at a Woodin-supercompact `δ`. -/
theorem woodinEndpoint_exit {δ : V} (hcon : WoodinIterationConstruction (V := V))
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    IsWoodinIteration δ δ (woodinIterationPrefix δ) (woodinIterationCardinalPrefix δ) :=
  (hcon δ hδ hAC).2.2.1

/-- The quotient closure at the endpoint, also read off the W02 exit. -/
theorem woodinEndpoint_quotientClosure {δ : V} (hcon : WoodinIterationConstruction (V := V))
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    HasWoodinQuotientClosure δ (woodinIterationPrefix δ) (woodinIterationCardinalPrefix δ) :=
  (hcon δ hδ hAC).2.2.2

/-- `δ` is an ordinal whenever it is Woodin-supercompact. -/
theorem IsWoodinSupercompact.isOrdinal {δ : V} (hδ : IsWoodinSupercompact δ) : IsOrdinal δ :=
  hδ.1.1

/-- A Woodin-supercompact `δ` contains the empty set: it lies above `ω` and is transitive.
This discharges the `h0` side condition of `woodinEndpointTop_isTop`. -/
theorem IsWoodinSupercompact.empty_mem {δ : V} (hδ : IsWoodinSupercompact δ) : (∅ : V) ∈ δ := by
  let := hδ.isOrdinal
  exact IsOrdinal.toIsTransitive.mem_trans (show (∅ : V) ∈ (ω : V) by simp) hδ.omega_lt

/-- `Q_δ` with its order is a forcing preorder. -/
theorem woodinEndpoint_preorder {δ : V} (hcon : WoodinIterationConstruction (V := V))
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    IsForcingPreorder (woodinEndpointPoset δ) (woodinEndpointOrder δ) :=
  woodinEndpointPoset_preorder (woodinEndpoint_exit hcon hδ hAC)

/-- `Q_δ` has a largest condition.  Both side conditions of `woodinEndpointTop_isTop`, the
`IsOrdinal δ` instance and `∅ ∈ δ`, come from `IsWoodinSupercompact δ`. -/
theorem woodinEndpoint_top {δ : V} (hcon : WoodinIterationConstruction (V := V))
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    IsForcingTop (woodinEndpointPoset δ) (woodinEndpointOrder δ) (woodinEndpointTop δ) := by
  let := hδ.isOrdinal
  exact woodinEndpointTop_isTop (woodinEndpoint_exit hcon hδ hAC) hδ.empty_mem

/-- Each stage below the endpoint is a complete subforcing of `Q_δ`: the coordinate map at `k`
is a projection with the section map at `k` as its exact right inverse.  The `IsOrdinal δ`
instance is discharged from `IsWoodinSupercompact δ`; `k ∈ δ` is a genuine parameter and stays
a hypothesis. -/
theorem woodinEndpoint_splitProjection' {δ k : V} (hcon : WoodinIterationConstruction (V := V))
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hk : k ∈ δ) :
    IsForcingSplitProjection ((forcingCodeP (woodinIterationPrefix δ)) ‘ k)
      ((forcingCodeR (woodinIterationPrefix δ)) ‘ k)
      (woodinEndpointPoset δ) (woodinEndpointOrder δ)
      (forcingThreadCoordinate (woodinEndpointPoset δ) k)
      (forcingThreadSection δ (forcingCodeP (woodinIterationPrefix δ))
        (forcingCodeπ (woodinIterationPrefix δ)) (forcingCodeE (woodinIterationPrefix δ)) k) := by
  let := hδ.isOrdinal
  exact woodinEndpoint_splitProjection (woodinEndpoint_exit hcon hδ hAC) hk

/-! ### The defining formula at the endpoint -/

/-- The paper's `ϑ_k` at the endpoint: for each polarity and each standard level `k`, the single
formula `uniformForcingLevelFormula pol k` says, of `Q_δ` and its order, exactly that `φ` is a
code of Levy level `k` and that `q` forces it. -/
theorem woodinEndpoint_level_defines {δ : V} (hcon : WoodinIterationConstruction (V := V))
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (pol : LevyPolarity) (k : ℕ)
    {D n φ b q : V} (hb : b ∈ D ^ n) (hq : q ∈ woodinEndpointPoset δ) :
    (uniformForcingLevelFormula pol k).Evalb
        ![woodinEndpointPoset δ, woodinEndpointOrder δ, D, n, φ, b, q] ↔
      IsLevyFormulaCode pol k n φ ∧
        q ∈ internalForcingSet (woodinEndpointPoset δ) (woodinEndpointOrder δ) D n φ b :=
  eval_uniformForcingLevelFormula hb hq

/-- The complexity certificate.  Both `uniformForcingLevelFormula pol k` and the numeral
`uniformForcingLevelBound pol k` are functions of `pol` and `k` alone; neither mentions the
endpoint, the poset, the order or the name set. -/
theorem woodinEndpoint_level_bound (pol : LevyPolarity) (k : ℕ) :
    IsSigmaFormula (uniformForcingLevelBound pol k) (uniformForcingLevelFormula pol k) :=
  uniformForcingLevelFormula_sigma pol k

/-- Endpoint independence, stated with two endpoints in one statement: the same formula and the
same Levy bound define the forcing relation at `δ` and at `δ'`. -/
theorem woodinEndpoint_uniform (hcon : WoodinIterationConstruction (V := V)) (hAC : ¬InternalChoice V)
    (pol : LevyPolarity) (k : ℕ) {δ δ' : V} (hd : IsWoodinSupercompact δ)
    (hd' : IsWoodinSupercompact δ') {D n φ b q D' b' q' : V} (hb : b ∈ D ^ n)
    (hq : q ∈ woodinEndpointPoset δ) (hb' : b' ∈ D' ^ n) (hq' : q' ∈ woodinEndpointPoset δ') :
    ((uniformForcingLevelFormula pol k).Evalb
        ![woodinEndpointPoset δ, woodinEndpointOrder δ, D, n, φ, b, q] ↔
      IsLevyFormulaCode pol k n φ ∧
        q ∈ internalForcingSet (woodinEndpointPoset δ) (woodinEndpointOrder δ) D n φ b) ∧
    ((uniformForcingLevelFormula pol k).Evalb
        ![woodinEndpointPoset δ', woodinEndpointOrder δ', D', n, φ, b', q'] ↔
      IsLevyFormulaCode pol k n φ ∧
        q' ∈ internalForcingSet (woodinEndpointPoset δ') (woodinEndpointOrder δ') D' n φ b') :=
  ⟨woodinEndpoint_level_defines hcon hd hAC pol k hb hq,
   woodinEndpoint_level_defines hcon hd' hAC pol k hb' hq'⟩

/-- Monotonicity in the level, at the endpoint: a code forced at level `k` is still recognised
at any higher level by the same formula family. -/
theorem woodinEndpoint_level_mono {δ : V} (hcon : WoodinIterationConstruction (V := V))
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) {pol : LevyPolarity} {k l : ℕ}
    (hkl : k ≤ l) {D n φ b q : V} (hb : b ∈ D ^ n) (hq : q ∈ woodinEndpointPoset δ)
    (h : (uniformForcingLevelFormula pol k).Evalb
      ![woodinEndpointPoset δ, woodinEndpointOrder δ, D, n, φ, b, q]) :
    (uniformForcingLevelFormula pol l).Evalb
      ![woodinEndpointPoset δ, woodinEndpointOrder δ, D, n, φ, b, q] :=
  uniformForcingLevelFormula_mono hkl hb hq h

/-! ### The truth lemma at the endpoint -/

/-- The truth lemma for `Q_δ`: for a generic filter over a set `D` of `Q_δ`-names and a code of
Levy level `k`, truth in the extension and being forced by a condition of the filter agree. -/
theorem woodinEndpoint_genericTruth {δ : V} (hcon : WoodinIterationConstruction (V := V))
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (A : ForcingContext V)
    (hAP : A.P = woodinEndpointPoset δ) (hAR : A.R = woodinEndpointOrder δ) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) {pol : LevyPolarity} {k : ℕ} {n φ : V}
    (hφ : IsLevyFormulaCode pol k n φ) : A.GroundGenericTruth D hD n φ :=
  A.levelGenericTruth D hD hφ

/-- Soundness at the endpoint: a condition of the generic filter that forces a level-`k` code
makes it true in the extension. -/
theorem woodinEndpoint_genericTruth_sound {δ : V} (hcon : WoodinIterationConstruction (V := V))
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (A : ForcingContext V)
    (hAP : A.P = woodinEndpointPoset δ) (hAR : A.R = woodinEndpointOrder δ) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) {pol : LevyPolarity} {k : ℕ} {n φ b p : V}
    (hφ : IsLevyFormulaCode pol k n φ) (hb : b ∈ D ^ n) (hpG : p ∈ A.G)
    (hp : p ∈ internalForcingSet A.P A.R D n φ b) :
    MembershipSatisfies (range (A.evaluationGraph D hD)) (A.check n) (A.check φ)
      (A.sequenceValue b (A.nameSequence_of_mem_function hD hb)) :=
  A.levelGenericTruth_sound D hD hφ hb hpG hp

/-- Truth at the endpoint: a level-`k` code true in the extension is forced by some condition of
the generic filter. -/
theorem woodinEndpoint_genericTruth_forced {δ : V} (hcon : WoodinIterationConstruction (V := V))
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (A : ForcingContext V)
    (hAP : A.P = woodinEndpointPoset δ) (hAR : A.R = woodinEndpointOrder δ) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) {pol : LevyPolarity} {k : ℕ} {n φ b : V}
    (hφ : IsLevyFormulaCode pol k n φ) (hb : b ∈ D ^ n)
    (h : MembershipSatisfies (range (A.evaluationGraph D hD)) (A.check n) (A.check φ)
      (A.sequenceValue b (A.nameSequence_of_mem_function hD hb))) :
    ∃ p ∈ A.G, p ∈ internalForcingSet A.P A.R D n φ b :=
  A.levelGenericTruth_forced D hD hφ hb h

/-! ### The class hypothesis of the paper proof -/

/-- `V_δ` is an internal ZF model at a Woodin-supercompact `δ`.  Restatement of the W03 result
`IsWoodinSupercompact.internalZFModel`. -/
theorem woodinEndpoint_rank_zf {δ : V} (hδ : IsWoodinSupercompact δ) :
    IsInternalZFModel (hierarchy δ) := hδ.internalZFModel

/-- The same, as satisfaction of the ZF axiom set by the set domain of `V_δ`.  Restatement of
`IsWoodinSupercompact.models_zf`. -/
theorem woodinEndpoint_rank_models_zf {δ : V} [Nonempty (SetDomain (hierarchy δ))]
    (hδ : IsWoodinSupercompact δ) : (SetDomain (hierarchy δ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := hδ.models_zf

/-- Separation consequence used in the paper argument: a subclass of `Q_δ` cut out by a
definable predicate is a set.  The witness is `sep`, so this is a restatement of the ambient
separation scheme rather than new machinery. -/
theorem woodinEndpoint_definable_subclass_isSet (δ : V) (P : V → Prop)
    (hP : ℒₛₑₜ-predicate P) :
    ∃ S : V, ∀ q, q ∈ S ↔ q ∈ woodinEndpointPoset δ ∧ P q :=
  ⟨sep (woodinEndpointPoset δ) P hP, fun _ ↦ mem_sep_iff⟩

/-- The forcing set of a code at the endpoint is one such subset of `Q_δ`. -/
theorem woodinEndpoint_forcingSet_subset (δ D n φ b : V) :
    internalForcingSet (woodinEndpointPoset δ) (woodinEndpointOrder δ) D n φ b ⊆
      woodinEndpointPoset δ :=
  internalForcingSet_subset _ _ _ _ _ _

end ZFVP
