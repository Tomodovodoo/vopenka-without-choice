import ZFVP.ModelTheory.SchmerlCodedTreeTransport
import ZFVP.ModelTheory.SchmerlCodedFunctionBranchFilter

/-! Transport of the actual finite-domain selection and branch filters. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl
variable {V U : Type*} [SetStructure V] [SetStructure U]
  [Nonempty V] [Nonempty U] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W]
variable (R : BinaryRelationRepresentation (V := V) W) (j : MembershipEndExtension V U)

theorem codedParameterSet_subset_carrier (φ s : V) : codedParameterSet R.code φ s ⊆ R.carrier := by
  intro x hx
  simpa only [code, binaryRelationStructureCode_domain] using ((mem_codedParameterSet _ _ _ _).mp hx).1

theorem endExtension_codedParameterSet (φ : SetTheorySemisentence 2) {s : V} (hs : s ∈ R.carrier) :
    j (codedParameterSet R.code (encodeMembershipFormula φ) s) =
      codedParameterSet (R.endExtension j).code (encodeMembershipFormula φ) (j s) := by
  have he := j.map_separation R.carrier
    (fun x ↦ codedBinary R.code (encodeMembershipFormula φ) x s)
    (fun x ↦ codedBinary (R.endExtension j).code (encodeMembershipFormula φ) x (j s))
    (by definability) (by definability) (by
      intro x hx
      exact (R.endExtension_codedBinary j φ hx hs).symm)
  simpa only [codedParameterSet, code, binaryRelationStructureCode_domain, endExtension] using he

variable (s : V) (hs : s ∈ R.carrier)
include hs

theorem endExtension_codedFiniteDomains :
    j (codedFiniteDomains R.code s) = codedFiniteDomains (R.endExtension j).code (j s) :=
  R.endExtension_codedParameterSet j finiteDomainFormula hs

theorem endExtension_codedFunctionNodes :
    j (codedFunctionNodes R.code s) = codedFunctionNodes (R.endExtension j).code (j s) :=
  R.endExtension_codedParameterSet j finiteBinaryFunctionFormula hs

theorem endExtension_codedFiniteDomainOrder :
    j (codedFiniteDomainOrder R.code s) = codedFiniteDomainOrder (R.endExtension j).code (j s) := by
  simpa only [codedFiniteDomainOrder, R.endExtension_codedFiniteDomains j s hs] using
    R.endExtension_codedBinaryOn j (“p q. p ⊆ q” : SetTheorySemisentence 2)
      (A := codedFiniteDomains R.code s) (B := codedFiniteDomains R.code s)
      (R.codedParameterSet_subset_carrier _ _) (R.codedParameterSet_subset_carrier _ _)

theorem endExtension_codedFunctionOrder :
    j (codedFunctionOrder R.code s) = codedFunctionOrder (R.endExtension j).code (j s) := by
  simpa only [codedFunctionOrder, R.endExtension_codedFunctionNodes j s hs] using
    R.endExtension_codedBinaryOn j (“p q. p ⊆ q” : SetTheorySemisentence 2)
      (A := codedFunctionNodes R.code s) (B := codedFunctionNodes R.code s)
      (R.codedParameterSet_subset_carrier _ _) (R.codedParameterSet_subset_carrier _ _)

theorem endExtension_codedFunctionDomains :
    j (codedFunctionDomains R.code s) = codedFunctionDomains (R.endExtension j).code (j s) := by
  simpa only [codedFunctionDomains, R.endExtension_codedFunctionNodes j s hs,
    R.endExtension_codedFiniteDomains j s hs] using
    R.endExtension_codedBinaryOn j (f“p a. a = !domain.dfn p” : SetTheorySemisentence 2)
      (A := codedFunctionNodes R.code s) (B := codedFiniteDomains R.code s)
      (R.codedParameterSet_subset_carrier _ _) (R.codedParameterSet_subset_carrier _ _)

theorem endExtension_codedSelectedFunctionNodes (κ c : V) :
    j (codedSelectedFunctionNodes R.code s κ c) = codedSelectedFunctionNodes (R.endExtension j).code (j s) (j κ) (j c) := by
  have he := j.map_separation (codedFunctionNodes R.code s)
    (fun x ↦ ∃ i ∈ κ, (codedFunctionDomains R.code s) ‘ x = c ‘ i)
    (fun x ↦ ∃ i ∈ j κ, (codedFunctionDomains (R.endExtension j).code (j s)) ‘ x = (j c) ‘ i)
    (by definability) (by definability) (by
      intro x _
      simp only [← R.endExtension_codedFunctionDomains j s hs, j.exists_mem_iff, ← j.map_value_total, j.injective.eq_iff])
  simpa only [codedSelectedFunctionNodes, R.endExtension_codedFunctionNodes j s hs] using he

theorem endExtension_codedSelectedFunctionOrder (κ c : V) :
    j (codedSelectedFunctionOrder R.code s κ c) = codedSelectedFunctionOrder (R.endExtension j).code (j s) (j κ) (j c) := by
  simp only [codedSelectedFunctionOrder, j.map_inter, j.map_prod,
    R.endExtension_codedFunctionOrder j s hs, R.endExtension_codedSelectedFunctionNodes j s hs]

theorem endExtension_codedSelectedFunctionRank (κ c : V) :
    j (codedSelectedFunctionRank R.code s κ c) = codedSelectedFunctionRank (R.endExtension j).code (j s) (j κ) (j c) := by
  have he := j.map_separation (codedSelectedFunctionNodes R.code s κ c ×ˢ κ)
    (fun p ↦ (codedFunctionDomains R.code s) ‘ (kpair.π₁ p) = c ‘ (kpair.π₂ p))
    (fun p ↦ (codedFunctionDomains (R.endExtension j).code (j s)) ‘ (kpair.π₁ p) = (j c) ‘ (kpair.π₂ p))
    (by definability) (by definability) (by
      intro p _
      simp only [← R.endExtension_codedFunctionDomains j s hs, ← j.map_first, ← j.map_second,
        ← j.map_value_total, j.injective.eq_iff])
  simpa only [codedSelectedFunctionRank, j.map_prod, R.endExtension_codedSelectedFunctionNodes j s hs] using he

theorem endExtension_codedFunctionBranchFilter (B : V) :
    j (codedFunctionBranchFilter R.code s B) = codedFunctionBranchFilter (R.endExtension j).code (j s) (j B) := by
  have he := j.map_separation (codedFunctionNodes R.code s)
    (fun x ↦ ∃ y ∈ B, ⟨x, y⟩ₖ ∈ codedFunctionOrder R.code s)
    (fun x ↦ ∃ y ∈ j B, ⟨x, y⟩ₖ ∈ codedFunctionOrder (R.endExtension j).code (j s))
    (by definability) (by definability) (by
      intro x _
      simp only [j.exists_mem_iff, ← R.endExtension_codedFunctionOrder j s hs, ← j.map_kpair, j.mem_iff])
  simpa only [codedFunctionBranchFilter, R.endExtension_codedFunctionNodes j s hs] using he

theorem endExtension_finiteDomainChain {κ c : V}
    (hc : IsInternalCofinalStrictChain κ (codedFiniteDomains R.code s) (codedFiniteDomainOrder R.code s) c) :
    IsInternalCofinalStrictChain (j κ) (codedFiniteDomains (R.endExtension j).code (j s))
      (codedFiniteDomainOrder (R.endExtension j).code (j s)) (j c) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← R.endExtension_codedFiniteDomains j s hs]
    exact (j.function_iff c κ (codedFiniteDomains R.code s)).mpr hc.1
  · intro i hi k hk hik
    obtain ⟨a, ha, rfl⟩ := j.endExtension κ i hi
    obtain ⟨b, hb, rfl⟩ := j.endExtension κ k hk
    have hab := hc.2.1 a ha b hb ((j.mem_iff _ _).mp hik)
    simp only [← j.map_value_total, ← R.endExtension_codedFiniteDomainOrder j s hs, ← j.map_kpair, j.mem_iff]
    exact ⟨hab.1, j.injective.ne hab.2⟩
  · intro x hx
    rw [← R.endExtension_codedFiniteDomains j s hs] at hx
    obtain ⟨y, hy, rfl⟩ := j.endExtension _ x hx
    obtain ⟨i, hi, hyi⟩ := hc.2.2 y hy
    refine ⟨j i, (j.mem_iff _ _).mpr hi, ?_⟩
    simpa only [← j.map_value_total, ← R.endExtension_codedFiniteDomainOrder j s hs, ← j.map_kpair, j.mem_iff] using hyi

end ZFVP.BinaryRelationRepresentation

