import ZFVP.ModelTheory.SchmerlCodedFunctionFamily
import ZFVP.ModelTheory.SchmerlCodedFunctionTransport

/-! A single actual relation records every selected finite domain. The family
graphs and this relation commute with membership end extensions. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedSelectedDomainRelation (M C : V) : V :=
  {p ∈ structureDomain M ×ˢ structureDomain M ;
    kpair.π₁ p ∈ codedInfiniteSets M ∧ kpair.π₂ p ∈ range (C ‘ (kpair.π₁ p))}

instance codedSelectedDomainRelation_definable : ℒₛₑₜ-function₂[V] codedSelectedDomainRelation := by
  have h : ℒₛₑₜ-relation₃[V] (fun S M C ↦ ∀ p, p ∈ S ↔
    p ∈ structureDomain M ×ˢ structureDomain M ∧
      kpair.π₁ p ∈ codedInfiniteSets M ∧ kpair.π₂ p ∈ range (C ‘ (kpair.π₁ p))) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [codedSelectedDomainRelation, mem_sep_iff]
  rfl

theorem codedSelectedDomainRelation_subset (M C : V) :
    codedSelectedDomainRelation M C ⊆ structureDomain M ×ˢ structureDomain M :=
  fun _ hp ↦ (mem_sep_iff.mp hp).1

theorem pair_mem_codedSelectedDomainRelation {M κ C : V} (hC : IsCodedFiniteDomainFamily M κ C)
    (s d : V) : ⟨s, d⟩ₖ ∈ codedSelectedDomainRelation M C ↔
      s ∈ codedInfiniteSets M ∧ d ∈ range (C ‘ s) := by
  simp only [codedSelectedDomainRelation, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  exact ⟨And.right, fun hp ↦ ⟨⟨codedInfiniteSets_subset M s hp.1,
    range_subset_of_mem_function (function_value_mem hC.1 hp.1) d hp.2⟩, hp⟩⟩

theorem pair_mem_codedSelectedDomainRelation_of_mem {M κ C s : V}
    (hC : IsCodedFiniteDomainFamily M κ C) (hs : s ∈ codedInfiniteSets M) (d : V) :
    ⟨s, d⟩ₖ ∈ codedSelectedDomainRelation M C ↔ d ∈ range (C ‘ s) := by
  rw [pair_mem_codedSelectedDomainRelation hC, and_iff_right hs]

end ZFVP.Schmerl

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl
variable {V U : Type*} [SetStructure V] [SetStructure U]
  [Nonempty V] [Nonempty U] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W]
variable (R : BinaryRelationRepresentation (V := V) W) (j : MembershipEndExtension V U)

theorem endExtension_codedInfiniteSets : j (codedInfiniteSets R.code) = codedInfiniteSets (R.endExtension j).code :=
  R.endExtension_codedUnarySet j internallyInfiniteFormula

theorem endExtension_finiteDomainFamily {κ C : V} (hC : IsCodedFiniteDomainFamily R.code κ C) :
    IsCodedFiniteDomainFamily (R.endExtension j).code (j κ) (j C) := by
  constructor
  · have hsub : j (structureDomain R.code ^ κ) ⊆ j (structureDomain R.code) ^ j κ := by
      intro c hc
      obtain ⟨d, hd, rfl⟩ := j.endExtension _ c hc
      exact (j.function_iff d κ (structureDomain R.code)).mpr hd
    have hh := mem_function_of_mem_function_of_subset
      ((j.function_iff C (codedInfiniteSets R.code) (structureDomain R.code ^ κ)).mpr hC.1) hsub
    rw [R.endExtension_codedInfiniteSets j] at hh
    simpa only [code, binaryRelationStructureCode_domain, endExtension] using hh
  · intro s hs
    rw [← R.endExtension_codedInfiniteSets j] at hs
    obtain ⟨a, ha, rfl⟩ := j.endExtension _ s hs
    have haD : a ∈ R.carrier := by
      simpa only [code, binaryRelationStructureCode_domain] using codedInfiniteSets_subset R.code a ha
    simpa only [j.map_value_total] using R.endExtension_finiteDomainChain j a haD (hC.2 a ha)

theorem endExtension_codedSelectedDomainRelation (C : V) :
    j (codedSelectedDomainRelation R.code C) = codedSelectedDomainRelation (R.endExtension j).code (j C) := by
  have he := j.map_separation (R.carrier ×ˢ R.carrier)
    (fun p ↦ kpair.π₁ p ∈ codedInfiniteSets R.code ∧ kpair.π₂ p ∈ range (C ‘ (kpair.π₁ p)))
    (fun p ↦ kpair.π₁ p ∈ codedInfiniteSets (R.endExtension j).code ∧
      kpair.π₂ p ∈ range ((j C) ‘ (kpair.π₁ p)))
    (by definability) (by definability) (by
      intro p _
      simp only [← j.map_first, ← j.map_second, ← R.endExtension_codedInfiniteSets j,
        ← j.map_value_total, ← j.map_range, j.mem_iff])
  simpa only [codedSelectedDomainRelation, code, binaryRelationStructureCode_domain, endExtension, j.map_prod] using he

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

theorem endExtension_codedFunctionTreeFamily (κ C : V) :
    j (codedFunctionTreeFamily R.code κ C) = codedFunctionTreeFamily (R.endExtension j).code (j κ) (j C) := by
  have he := j.map_definableGraph (codedInfiniteSets R.code)
    (fun s ↦ codedSelectedFunctionNodes R.code s κ (C ‘ s))
    (fun s ↦ codedSelectedFunctionNodes (R.endExtension j).code s (j κ) ((j C) ‘ s))
    (by definability) (by definability) (by
      intro s hs
      have hsD : s ∈ R.carrier := by
        simpa only [code, binaryRelationStructureCode_domain] using codedInfiniteSets_subset R.code s hs
      rw [R.endExtension_codedSelectedFunctionNodes j s hsD, j.map_value_total])
  simpa only [codedFunctionTreeFamily, R.endExtension_codedInfiniteSets j] using he

theorem endExtension_codedFunctionOrderFamily (κ C : V) :
    j (codedFunctionOrderFamily R.code κ C) = codedFunctionOrderFamily (R.endExtension j).code (j κ) (j C) := by
  have he := j.map_definableGraph (codedInfiniteSets R.code)
    (fun s ↦ codedSelectedFunctionOrder R.code s κ (C ‘ s))
    (fun s ↦ codedSelectedFunctionOrder (R.endExtension j).code s (j κ) ((j C) ‘ s))
    (by definability) (by definability) (by
      intro s hs
      have hsD : s ∈ R.carrier := by
        simpa only [code, binaryRelationStructureCode_domain] using codedInfiniteSets_subset R.code s hs
      rw [R.endExtension_codedSelectedFunctionOrder j s hsD, j.map_value_total])
  simpa only [codedFunctionOrderFamily, R.endExtension_codedInfiniteSets j] using he

theorem endExtension_codedFunctionRankFamily (κ C : V) :
    j (codedFunctionRankFamily R.code κ C) = codedFunctionRankFamily (R.endExtension j).code (j κ) (j C) := by
  have he := j.map_definableGraph (codedInfiniteSets R.code)
    (fun s ↦ codedSelectedFunctionRank R.code s κ (C ‘ s))
    (fun s ↦ codedSelectedFunctionRank (R.endExtension j).code s (j κ) ((j C) ‘ s))
    (by definability) (by definability) (by
      intro s hs
      have hsD : s ∈ R.carrier := by
        simpa only [code, binaryRelationStructureCode_domain] using codedInfiniteSets_subset R.code s hs
      rw [R.endExtension_codedSelectedFunctionRank j s hsD, j.map_value_total])
  simpa only [codedFunctionRankFamily, R.endExtension_codedInfiniteSets j] using he

end ZFVP.BinaryRelationRepresentation
