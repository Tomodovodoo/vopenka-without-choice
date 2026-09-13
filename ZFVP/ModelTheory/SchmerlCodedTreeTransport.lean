import ZFVP.ModelTheory.SchmerlCodedRepresentedDefinitions
import ZFVP.ModelTheory.SchmerlCodedBranchFilter
import ZFVP.SetTheory.EndExtensionRegular

/-! The selected tree and its full-filter reconstruction commute with a
membership end extension. The represented model itself retains its original
binary relation throughout. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V U : Type*} [SetStructure V] [SetStructure U]
  [Nonempty V] [Nonempty U] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W]
variable (R : BinaryRelationRepresentation (V := V) W) (j : MembershipEndExtension V U)

theorem codedUnarySet_subset_carrier (φ : V) : codedUnarySet R.code φ ⊆ R.carrier := by
  intro x hx
  simpa only [code, binaryRelationStructureCode_domain] using ((mem_codedUnarySet _ _ _).mp hx).1

theorem endExtension_codedOrdinals : j (codedOrdinals R.code) = codedOrdinals (R.endExtension j).code :=
  R.endExtension_codedUnarySet j ordinalNodeFormula

theorem endExtension_codedClassNodes : j (codedClassNodes R.code) = codedClassNodes (R.endExtension j).code :=
  R.endExtension_codedUnarySet j classNodeFormula

theorem endExtension_codedOrdinalOrder : j (codedOrdinalOrder R.code) = codedOrdinalOrder (R.endExtension j).code := by
  simpa only [codedOrdinalOrder, R.endExtension_codedOrdinals j] using
    R.endExtension_codedBinaryOn j ordinalOrderFormula (A := codedOrdinals R.code) (B := codedOrdinals R.code)
      (R.codedUnarySet_subset_carrier _) (R.codedUnarySet_subset_carrier _)

theorem endExtension_codedClassOrder : j (codedClassOrder R.code) = codedClassOrder (R.endExtension j).code := by
  simpa only [codedClassOrder, R.endExtension_codedClassNodes j] using
    R.endExtension_codedBinaryOn j classOrderFormula (A := codedClassNodes R.code) (B := codedClassNodes R.code)
      (R.codedUnarySet_subset_carrier _) (R.codedUnarySet_subset_carrier _)

theorem endExtension_codedClassLevels : j (codedClassLevels R.code) = codedClassLevels (R.endExtension j).code := by
  simpa only [codedClassLevels, R.endExtension_codedClassNodes j, R.endExtension_codedOrdinals j] using
    R.endExtension_codedBinaryOn j classRankFormula (A := codedClassNodes R.code) (B := codedOrdinals R.code)
      (R.codedUnarySet_subset_carrier _) (R.codedUnarySet_subset_carrier _)

theorem endExtension_codedSelectedClassNodes (κ c : V) :
    j (codedSelectedClassNodes R.code κ c) = codedSelectedClassNodes (R.endExtension j).code (j κ) (j c) := by
  have he := j.map_separation (codedClassNodes R.code)
    (fun x ↦ ∃ i ∈ κ, (codedClassLevels R.code) ‘ x = c ‘ i)
    (fun x ↦ ∃ i ∈ j κ, (codedClassLevels (R.endExtension j).code) ‘ x = (j c) ‘ i)
    (by definability) (by definability) (by
      intro x _
      simp only [← R.endExtension_codedClassLevels j, j.exists_mem_iff, ← j.map_value_total, j.injective.eq_iff])
  simpa only [codedSelectedClassNodes, R.endExtension_codedClassNodes j] using he

theorem endExtension_codedSelectedClassOrder (κ c : V) :
    j (codedSelectedClassOrder R.code κ c) = codedSelectedClassOrder (R.endExtension j).code (j κ) (j c) := by
  simp only [codedSelectedClassOrder, j.map_inter, j.map_prod,
    R.endExtension_codedClassOrder j, R.endExtension_codedSelectedClassNodes j]

theorem endExtension_codedSelectedClassRank (κ c : V) :
    j (codedSelectedClassRank R.code κ c) = codedSelectedClassRank (R.endExtension j).code (j κ) (j c) := by
  have he := j.map_separation (codedSelectedClassNodes R.code κ c ×ˢ κ)
    (fun p ↦ (codedClassLevels R.code) ‘ (kpair.π₁ p) = c ‘ (kpair.π₂ p))
    (fun p ↦ (codedClassLevels (R.endExtension j).code) ‘ (kpair.π₁ p) = (j c) ‘ (kpair.π₂ p))
    (by definability) (by definability) (by
      intro p _
      simp only [← R.endExtension_codedClassLevels j, ← j.map_first, ← j.map_second,
        ← j.map_value_total, j.injective.eq_iff])
  simpa only [codedSelectedClassRank, j.map_prod, R.endExtension_codedSelectedClassNodes j] using he

theorem endExtension_codedBranchFilter (B : V) :
    j (codedBranchFilter R.code B) = codedBranchFilter (R.endExtension j).code (j B) := by
  have he := j.map_separation (codedClassNodes R.code)
    (fun x ↦ ∃ y ∈ B, ⟨x, y⟩ₖ ∈ codedClassOrder R.code)
    (fun x ↦ ∃ y ∈ j B, ⟨x, y⟩ₖ ∈ codedClassOrder (R.endExtension j).code)
    (by definability) (by definability) (by
      intro x _
      simp only [j.exists_mem_iff, ← R.endExtension_codedClassOrder j, ← j.map_kpair, j.mem_iff])
  simpa only [codedBranchFilter, R.endExtension_codedClassNodes j] using he

theorem endExtension_cofinalChain {κ c : V}
    (hc : IsInternalCofinalStrictChain κ (codedOrdinals R.code) (codedOrdinalOrder R.code) c) :
    IsInternalCofinalStrictChain (j κ) (codedOrdinals (R.endExtension j).code)
      (codedOrdinalOrder (R.endExtension j).code) (j c) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← R.endExtension_codedOrdinals j]
    exact (j.function_iff c κ (codedOrdinals R.code)).mpr hc.1
  · intro i hi k hk hik
    obtain ⟨a, ha, rfl⟩ := j.endExtension κ i hi
    obtain ⟨b, hb, rfl⟩ := j.endExtension κ k hk
    have hab := hc.2.1 a ha b hb ((j.mem_iff _ _).mp hik)
    simp only [← j.map_value_total, ← R.endExtension_codedOrdinalOrder j, ← j.map_kpair, j.mem_iff]
    exact ⟨hab.1, j.injective.ne hab.2⟩
  · intro x hx
    rw [← R.endExtension_codedOrdinals j] at hx
    obtain ⟨y, hy, rfl⟩ := j.endExtension _ x hx
    obtain ⟨i, hi, hyi⟩ := hc.2.2 y hy
    refine ⟨j i, (j.mem_iff _ _).mpr hi, ?_⟩
    simpa only [← j.map_value_total, ← R.endExtension_codedOrdinalOrder j, ← j.map_kpair, j.mem_iff] using hyi

end ZFVP.BinaryRelationRepresentation
