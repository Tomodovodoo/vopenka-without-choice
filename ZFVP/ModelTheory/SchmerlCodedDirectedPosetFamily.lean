import ZFVP.ModelTheory.SchmerlCodedDefinitionParameters

/-! The actual countable index of directed posets defined over a source.
Each index retains separate unary and binary formula/parameter witnesses. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local irreducible] unaryDefinitionSet binaryDefinitionRelation

noncomputable def codedDirectedPosetIndex (M : V) : V :=
  {i ∈ unaryDefinitionParameters M ×ˢ binaryDefinitionParameters M ;
    IsForcingPoset (unaryDefinitionSet M (kpair.π₁ i)) (binaryDefinitionRelation M (kpair.π₂ i)) ∧
    IsInternalDirectedNoMax (unaryDefinitionSet M (kpair.π₁ i)) (binaryDefinitionRelation M (kpair.π₂ i))}

instance codedDirectedPosetIndex_definable : ℒₛₑₜ-function₁[V] codedDirectedPosetIndex := by
  have h : ℒₛₑₜ-relation[V] (fun I M ↦ ∀ i, i ∈ I ↔
    i ∈ unaryDefinitionParameters M ×ˢ binaryDefinitionParameters M ∧
    IsForcingPoset (unaryDefinitionSet M (kpair.π₁ i)) (binaryDefinitionRelation M (kpair.π₂ i)) ∧
    IsInternalDirectedNoMax (unaryDefinitionSet M (kpair.π₁ i)) (binaryDefinitionRelation M (kpair.π₂ i))) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [codedDirectedPosetIndex, mem_sep_iff]
  rfl

theorem pair_mem_codedDirectedPosetIndex (M u r : V) : ⟨u, r⟩ₖ ∈ codedDirectedPosetIndex M ↔
    (u ∈ unaryDefinitionParameters M ∧ r ∈ binaryDefinitionParameters M) ∧
      IsForcingPoset (unaryDefinitionSet M u) (binaryDefinitionRelation M r) ∧
      IsInternalDirectedNoMax (unaryDefinitionSet M u) (binaryDefinitionRelation M r) := by
  simp only [codedDirectedPosetIndex, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]

theorem codedDirectedPosetIndex_spec {M i : V} (hi : i ∈ codedDirectedPosetIndex M) :
    kpair.π₁ i ∈ unaryDefinitionParameters M ∧ kpair.π₂ i ∈ binaryDefinitionParameters M ∧
      IsForcingPoset (unaryDefinitionSet M (kpair.π₁ i)) (binaryDefinitionRelation M (kpair.π₂ i)) ∧
      IsInternalDirectedNoMax (unaryDefinitionSet M (kpair.π₁ i)) (binaryDefinitionRelation M (kpair.π₂ i)) := by
  obtain ⟨u, hu, r, hr, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hi).1
  obtain ⟨_, hpos, hdir⟩ := (pair_mem_codedDirectedPosetIndex M u r).mp hi
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using And.intro hu ⟨hr, hpos, hdir⟩

theorem codedDirectedPosetIndex_countable (hAC : InternalChoice V) {M : V}
    (hM : IsInternallyCountable (structureDomain M)) : IsInternallyCountable (codedDirectedPosetIndex M) :=
  internallyCountable_subset
    ((prod_cardLE_prod (unaryDefinitionParameters_countable hAC hM)
      (binaryDefinitionParameters_countable hAC hM)).trans omega_prod_cardLE_omega)
    (fun _ hi ↦ (mem_sep_iff.mp hi).1)

noncomputable def codedDirectedPosetDomains (M : V) : V :=
  definableGraph (codedDirectedPosetIndex M) (fun i ↦ unaryDefinitionSet M (kpair.π₁ i)) (by definability)

noncomputable def codedDirectedPosetRelations (M : V) : V :=
  definableGraph (codedDirectedPosetIndex M) (fun i ↦ binaryDefinitionRelation M (kpair.π₂ i)) (by definability)

instance codedDirectedPosetDomains_definable : ℒₛₑₜ-function₁[V] codedDirectedPosetDomains := by
  have h : ℒₛₑₜ-relation[V] (fun P M ↦ ∀ p, p ∈ P ↔
    ∃ i ∈ codedDirectedPosetIndex M, p = ⟨i, unaryDefinitionSet M (kpair.π₁ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [codedDirectedPosetDomains, mem_definableGraph_iff]
  rfl

instance codedDirectedPosetRelations_definable : ℒₛₑₜ-function₁[V] codedDirectedPosetRelations := by
  have h : ℒₛₑₜ-relation[V] (fun R M ↦ ∀ p, p ∈ R ↔
    ∃ i ∈ codedDirectedPosetIndex M, p = ⟨i, binaryDefinitionRelation M (kpair.π₂ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [codedDirectedPosetRelations, mem_definableGraph_iff]
  rfl

theorem codedDirectedPosetDomains_mem (M : V) :
    codedDirectedPosetDomains M ∈ power (structureDomain M) ^ codedDirectedPosetIndex M :=
  definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun i _ ↦ mem_power_iff.mpr (unaryDefinitionSet_subset M (kpair.π₁ i)))

theorem codedDirectedPosetRelations_mem (M : V) :
    codedDirectedPosetRelations M ∈ power (structureDomain M ×ˢ structureDomain M) ^ codedDirectedPosetIndex M :=
  definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun i _ ↦ mem_power_iff.mpr (binaryDefinitionRelation_subset M (kpair.π₂ i)))

theorem codedDirectedPosetDomains_value {M i : V} (hi : i ∈ codedDirectedPosetIndex M) :
    (codedDirectedPosetDomains M) ‘ i = unaryDefinitionSet M (kpair.π₁ i) := value_definableGraph _ _ _ hi

theorem codedDirectedPosetRelations_value {M i : V} (hi : i ∈ codedDirectedPosetIndex M) :
    (codedDirectedPosetRelations M) ‘ i = binaryDefinitionRelation M (kpair.π₂ i) := value_definableGraph _ _ _ hi

theorem codedDirectedPosetFamily_poset {M i : V} (hi : i ∈ codedDirectedPosetIndex M) :
    IsForcingPoset ((codedDirectedPosetDomains M) ‘ i) ((codedDirectedPosetRelations M) ‘ i) := by
  rw [codedDirectedPosetDomains_value hi, codedDirectedPosetRelations_value hi]
  exact (codedDirectedPosetIndex_spec hi).2.2.1

theorem codedDirectedPosetFamily_directed {M i : V} (hi : i ∈ codedDirectedPosetIndex M) :
    IsInternalDirectedNoMax ((codedDirectedPosetDomains M) ‘ i) ((codedDirectedPosetRelations M) ‘ i) := by
  rw [codedDirectedPosetDomains_value hi, codedDirectedPosetRelations_value hi]
  exact (codedDirectedPosetIndex_spec hi).2.2.2

theorem codedDirectedPosetFamily_definitions {M i : V} (hi : i ∈ codedDirectedPosetIndex M) :
    IsCodedDefinableSet M ((codedDirectedPosetDomains M) ‘ i) ∧
      IsCodedDefinableRelation M ((codedDirectedPosetRelations M) ‘ i) := by
  rw [codedDirectedPosetDomains_value hi, codedDirectedPosetRelations_value hi]
  exact ⟨unaryDefinitionSet_isCodedDefinable (codedDirectedPosetIndex_spec hi).1,
    binaryDefinitionRelation_isCodedDefinable (codedDirectedPosetIndex_spec hi).2.1⟩

theorem codedDirectedPosetIndex_complete {M P R : V}
    (hP : IsCodedDefinableSet M P) (hR : IsCodedDefinableRelation M R)
    (hpos : IsForcingPoset P R) (hdir : IsInternalDirectedNoMax P R) :
    ∃ i ∈ codedDirectedPosetIndex M,
      unaryDefinitionSet M (kpair.π₁ i) = P ∧ binaryDefinitionRelation M (kpair.π₂ i) = R := by
  obtain ⟨u, hu, huP⟩ := hP.exists_unaryDefinition
  obtain ⟨r, hr, hrR⟩ := hR.exists_binaryDefinition
  refine ⟨⟨u, r⟩ₖ, ?_, ?_⟩
  · apply (pair_mem_codedDirectedPosetIndex M u r).mpr
    exact ⟨⟨hu, hr⟩, by simpa only [huP, hrR] using hpos, by simpa only [huP, hrR] using hdir⟩
  · simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using And.intro huP hrR

theorem codedDirectedPosetFamily_complete {M P R : V}
    (hP : IsCodedDefinableSet M P) (hR : IsCodedDefinableRelation M R)
    (hpos : IsForcingPoset P R) (hdir : IsInternalDirectedNoMax P R) :
    ∃ i ∈ codedDirectedPosetIndex M,
      (codedDirectedPosetDomains M) ‘ i = P ∧ (codedDirectedPosetRelations M) ‘ i = R := by
  obtain ⟨i, hi, hPi, hRi⟩ := codedDirectedPosetIndex_complete hP hR hpos hdir
  exact ⟨i, hi, (codedDirectedPosetDomains_value hi).trans hPi, (codedDirectedPosetRelations_value hi).trans hRi⟩

theorem codedDirectedPosetDomains_membership {M i x : V} (hi : i ∈ codedDirectedPosetIndex M) :
    x ∈ (codedDirectedPosetDomains M) ‘ i ↔ x ∈ structureDomain M ∧
      codedSatisfies M (succ (definitionParameterCount (kpair.π₁ i))) (definitionFormula (kpair.π₁ i))
        (assignmentPrepend (definitionParameterCount (kpair.π₁ i)) (definitionTuple (kpair.π₁ i)) x) := by
  rw [codedDirectedPosetDomains_value hi]
  exact mem_unaryDefinitionSet _ _ _

theorem codedDirectedPosetRelations_membership {M i x y : V} (hi : i ∈ codedDirectedPosetIndex M) :
    ⟨x, y⟩ₖ ∈ (codedDirectedPosetRelations M) ‘ i ↔ (x ∈ structureDomain M ∧ y ∈ structureDomain M) ∧
      codedSatisfies M (succ (succ (definitionParameterCount (kpair.π₂ i)))) (definitionFormula (kpair.π₂ i))
        (assignmentPrepend (succ (definitionParameterCount (kpair.π₂ i)))
          (assignmentPrepend (definitionParameterCount (kpair.π₂ i)) (definitionTuple (kpair.π₂ i)) y) x) := by
  rw [codedDirectedPosetRelations_value hi]
  exact pair_mem_binaryDefinitionRelation _ _ _ _

end ZFVP.Schmerl
