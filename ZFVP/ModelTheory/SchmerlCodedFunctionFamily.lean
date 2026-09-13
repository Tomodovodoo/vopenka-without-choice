import ZFVP.ModelTheory.SchmerlCodedFunctionBranchBound

/-! One actual family of cofinal finite-domain chains and selected function
trees, indexed by all sets the coded source regards as infinite. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedInfiniteSets (M : V) : V :=
  codedUnarySet M (encodeMembershipFormula internallyInfiniteFormula)

instance codedInfiniteSets_definable : ℒₛₑₜ-function₁[V] codedInfiniteSets := by unfold codedInfiniteSets; definability

theorem codedInfiniteSets_subset (M : V) : codedInfiniteSets M ⊆ structureDomain M :=
  fun _ hs ↦ ((mem_codedUnarySet _ _ _).mp hs).1

def IsCodedFiniteDomainFamily (M κ C : V) : Prop :=
  C ∈ (structureDomain M ^ κ) ^ codedInfiniteSets M ∧
    ∀ s ∈ codedInfiniteSets M, IsInternalCofinalStrictChain κ
      (codedFiniteDomains M s) (codedFiniteDomainOrder M s) (C ‘ s)

instance isCodedFiniteDomainFamily_definable : ℒₛₑₜ-relation₃[V] IsCodedFiniteDomainFamily := by
  unfold IsCodedFiniteDomainFamily
  definability

theorem IsCodedRubinFinSmallSource.finiteDomainChain {M : V} (h : IsCodedRubinFinSmallSource M)
    {s : V} (hs : s ∈ codedInfiniteSets M) :
    ∃ c, IsInternalCofinalStrictChain (hartogsNumber (ω : V)) (codedFiniteDomains M s)
      (codedFiniteDomainOrder M s) c := by
  obtain ⟨⟨D, E, rfl, hE⟩, hZF, _, hRubin, _⟩ := h
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hZF.valid.domain_nonempty
  let R := binaryIdentityRepresentation hD hE
  let : Nonempty (BinaryRelationDomain D E) := binaryRelationDomain_nonempty hD
  let : (BinaryRelationDomain D E)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := R.models_zf_of_isCodedZFModel hZF
  have hsD : s ∈ D := by simpa only [binaryRelationStructureCode_domain] using codedInfiniteSets_subset _ _ hs
  let a : BinaryRelationDomain D E := ⟨s, hsD⟩
  have ha : IsInternallyInfinite a := by
    have he := (R.mem_unarySet_iff internallyInfiniteFormula a).mp hs
    simpa using he
  exact R.exists_cofinal_finiteDomain_chain (κ := hartogsNumber (ω : V)) (s := a) hRubin ha

theorem IsCodedRubinFinSmallSource.functionTree_data (hAC : InternalChoice V) {M : V}
    (h : IsCodedRubinFinSmallSource M) {s c : V} (hs : s ∈ structureDomain M)
    (hc : IsInternalCofinalStrictChain (hartogsNumber (ω : V)) (codedFiniteDomains M s)
      (codedFiniteDomainOrder M s) c) :
    InternalRankedTree (codedSelectedFunctionNodes M s (hartogsNumber (ω : V)) c)
      (codedSelectedFunctionOrder M s (hartogsNumber (ω : V)) c) (hartogsNumber (ω : V))
      (codedSelectedFunctionRank M s (hartogsNumber (ω : V)) c) ∧
    IsForcingPoset (codedSelectedFunctionNodes M s (hartogsNumber (ω : V)) c)
      (codedSelectedFunctionOrder M s (hartogsNumber (ω : V)) c) ∧
    (∀ x ∈ codedSelectedFunctionNodes M s (hartogsNumber (ω : V)) c,
      ∀ y ∈ codedSelectedFunctionNodes M s (hartogsNumber (ω : V)) c,
      ⟨x, y⟩ₖ ∈ codedSelectedFunctionOrder M s (hartogsNumber (ω : V)) c →
      (codedSelectedFunctionRank M s (hartogsNumber (ω : V)) c) ‘ x =
        (codedSelectedFunctionRank M s (hartogsNumber (ω : V)) c) ‘ y → x = y) ∧
    codedSelectedFunctionNodes M s (hartogsNumber (ω : V)) c ≤# hartogsNumber (ω : V) ∧
    internalCofinalBranches (codedSelectedFunctionNodes M s (hartogsNumber (ω : V)) c)
      (codedSelectedFunctionOrder M s (hartogsNumber (ω : V)) c) (hartogsNumber (ω : V))
      (codedSelectedFunctionRank M s (hartogsNumber (ω : V)) c) ≤# hartogsNumber (ω : V) := by
  obtain ⟨⟨D, E, rfl, hE⟩, hZF, hcard, hRubin, _⟩ := h
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hZF.valid.domain_nonempty
  let R := binaryIdentityRepresentation hD hE
  let : Nonempty (BinaryRelationDomain D E) := binaryRelationDomain_nonempty hD
  let : (BinaryRelationDomain D E)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := R.models_zf_of_isCodedZFModel hZF
  have hsD : s ∈ D := by simpa only [binaryRelationStructureCode_domain] using hs
  let a : BinaryRelationDomain D E := ⟨s, hsD⟩
  refine ⟨R.selectedFunctionTree a hc, R.selectedFunctionOrder_poset a _ _,
    fun _ hx _ hy hxy he ↦ R.selectedFunctionRank_comparable_injective a hc hx hy hxy he,
    (cardLE_of_subset ?_).trans hcard, R.selectedFunctionBranches_cardLE a hAC hc hRubin hcard⟩
  intro x hx
  exact ((mem_codedParameterSet _ _ _ _).mp ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hx).1).1

theorem IsCodedRubinFinSmallSource.exists_finiteDomainFamily (hAC : InternalChoice V)
    {M : V} (h : IsCodedRubinFinSmallSource M) :
    ∃ C, IsCodedFiniteDomainFamily M (hartogsNumber (ω : V)) C := by
  let κ := hartogsNumber (ω : V)
  let candidates : V → V := fun s ↦ {c ∈ structureDomain M ^ κ ;
    IsInternalCofinalStrictChain κ (codedFiniteDomains M s) (codedFiniteDomainOrder M s) c}
  have hcand : ℒₛₑₜ-function₁[V] candidates := by
    have hh : ℒₛₑₜ-relation[V] (fun B s ↦ ∀ c, c ∈ B ↔ c ∈ structureDomain M ^ κ ∧
      IsInternalCofinalStrictChain κ (codedFiniteDomains M s) (codedFiniteDomainOrder M s) c) := by definability
    apply Language.Definable.of_iff hh
    intro v
    rw [mem_ext_iff]
    simp only [candidates, mem_sep_iff]
    rfl
  have hne : ∀ s ∈ codedInfiniteSets M, IsNonempty (candidates s) := by
    intro s hs
    obtain ⟨c, hc⟩ := h.finiteDomainChain hs
    have hcd : c ∈ structureDomain M ^ κ := mem_function_of_mem_function_of_subset hc.1
      (fun _ hx ↦ ((mem_codedParameterSet _ _ _ _).mp hx).1)
    exact ⟨c, mem_sep_iff.mpr ⟨hcd, hc⟩⟩
  obtain ⟨C, hC, hdC, hval⟩ := choice_for_definable_family hAC (codedInfiniteSets M) candidates hcand hne
  let : IsFunction C := hC
  refine ⟨C, ?_, fun s hs ↦ (mem_sep_iff.mp (hval s hs)).2⟩
  have hrC : range C ⊆ structureDomain M ^ κ := by
    intro c hc
    obtain ⟨s, hsc⟩ := mem_range_iff.mp hc
    have hs : s ∈ codedInfiniteSets M := hdC ▸ mem_domain_of_kpair_mem hsc
    have hv := (mem_sep_iff.mp (hval s hs)).1
    rwa [value_eq_of_kpair_mem hsc] at hv
  simpa only [hdC] using mem_function_of_mem_function_of_subset (IsFunction.mem_function C) hrC

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def codedFunctionTreeFamily (M κ C : V) : V :=
  definableGraph (codedInfiniteSets M) (fun s ↦ codedSelectedFunctionNodes M s κ (C ‘ s)) (by definability)

noncomputable def codedFunctionOrderFamily (M κ C : V) : V :=
  definableGraph (codedInfiniteSets M) (fun s ↦ codedSelectedFunctionOrder M s κ (C ‘ s)) (by definability)

noncomputable def codedFunctionRankFamily (M κ C : V) : V :=
  definableGraph (codedInfiniteSets M) (fun s ↦ codedSelectedFunctionRank M s κ (C ‘ s)) (by definability)

instance codedFunctionTreeFamily_isFunction (M κ C : V) : IsFunction (codedFunctionTreeFamily M κ C) :=
  definableGraph_isFunction _ _ _
instance codedFunctionOrderFamily_isFunction (M κ C : V) : IsFunction (codedFunctionOrderFamily M κ C) :=
  definableGraph_isFunction _ _ _
instance codedFunctionRankFamily_isFunction (M κ C : V) : IsFunction (codedFunctionRankFamily M κ C) :=
  definableGraph_isFunction _ _ _

theorem domain_codedFunctionTreeFamily (M κ C : V) : domain (codedFunctionTreeFamily M κ C) = codedInfiniteSets M := domain_definableGraph _ _ _
theorem domain_codedFunctionOrderFamily (M κ C : V) : domain (codedFunctionOrderFamily M κ C) = codedInfiniteSets M := domain_definableGraph _ _ _
theorem domain_codedFunctionRankFamily (M κ C : V) : domain (codedFunctionRankFamily M κ C) = codedInfiniteSets M := domain_definableGraph _ _ _

theorem value_codedFunctionTreeFamily {M κ C s : V} (hs : s ∈ codedInfiniteSets M) :
    (codedFunctionTreeFamily M κ C) ‘ s = codedSelectedFunctionNodes M s κ (C ‘ s) := value_definableGraph _ _ _ hs
theorem value_codedFunctionOrderFamily {M κ C s : V} (hs : s ∈ codedInfiniteSets M) :
    (codedFunctionOrderFamily M κ C) ‘ s = codedSelectedFunctionOrder M s κ (C ‘ s) := value_definableGraph _ _ _ hs
theorem value_codedFunctionRankFamily {M κ C s : V} (hs : s ∈ codedInfiniteSets M) :
    (codedFunctionRankFamily M κ C) ‘ s = codedSelectedFunctionRank M s κ (C ‘ s) := value_definableGraph _ _ _ hs

theorem IsCodedRubinFinSmallSource.functionFamily_data (hAC : InternalChoice V) {M C : V}
    (h : IsCodedRubinFinSmallSource M) (hC : IsCodedFiniteDomainFamily M (hartogsNumber (ω : V)) C) :
    codedInfiniteSets M ≤# hartogsNumber (ω : V) ∧
    ∀ s ∈ codedInfiniteSets M,
      InternalRankedTree ((codedFunctionTreeFamily M (hartogsNumber (ω : V)) C) ‘ s)
        ((codedFunctionOrderFamily M (hartogsNumber (ω : V)) C) ‘ s) (hartogsNumber (ω : V))
        ((codedFunctionRankFamily M (hartogsNumber (ω : V)) C) ‘ s) ∧
      IsForcingPoset ((codedFunctionTreeFamily M (hartogsNumber (ω : V)) C) ‘ s)
        ((codedFunctionOrderFamily M (hartogsNumber (ω : V)) C) ‘ s) ∧
      (∀ x ∈ (codedFunctionTreeFamily M (hartogsNumber (ω : V)) C) ‘ s,
        ∀ y ∈ (codedFunctionTreeFamily M (hartogsNumber (ω : V)) C) ‘ s,
        ⟨x, y⟩ₖ ∈ (codedFunctionOrderFamily M (hartogsNumber (ω : V)) C) ‘ s →
        ((codedFunctionRankFamily M (hartogsNumber (ω : V)) C) ‘ s) ‘ x =
          ((codedFunctionRankFamily M (hartogsNumber (ω : V)) C) ‘ s) ‘ y → x = y) ∧
      internalCofinalBranches ((codedFunctionTreeFamily M (hartogsNumber (ω : V)) C) ‘ s)
        ((codedFunctionOrderFamily M (hartogsNumber (ω : V)) C) ‘ s) (hartogsNumber (ω : V))
        ((codedFunctionRankFamily M (hartogsNumber (ω : V)) C) ‘ s) ≤# hartogsNumber (ω : V) := by
  refine ⟨(cardLE_of_subset (codedInfiniteSets_subset M)).trans h.2.2.1, ?_⟩
  intro s hs
  rw [value_codedFunctionTreeFamily hs, value_codedFunctionOrderFamily hs, value_codedFunctionRankFamily hs]
  obtain ⟨ht, hp, hinj, _, hbranch⟩ := h.functionTree_data hAC (codedInfiniteSets_subset M s hs) (hC.2 s hs)
  exact ⟨ht, hp, hinj, hbranch⟩

end ZFVP.Schmerl
