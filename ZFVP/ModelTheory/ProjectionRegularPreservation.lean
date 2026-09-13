import ZFVP.ModelTheory.ProjectionClosedPreservation
import ZFVP.SetTheory.EndExtensionFinite

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem check_regular_of_short_functions_bounded (A : ForcingContext V) {κ : V} [IsOrdinal κ]
    (hω : (ω : V) ⊆ κ)
    (hb : ∀ α ∈ κ, ∀ f ∈ A.check κ ^ A.check α,
      ∃ β ∈ A.check κ, ∀ a ∈ A.check α, f ‘ a ∈ β) : IsRegularCardinal (A.check κ) := by
  have hcf : internalCofinality (A.check κ) = A.check κ := by
    rcases IsOrdinal.subset_iff.mp (internalCofinality_subset (A.check κ)) with he | hlt
    · exact he
    obtain ⟨α, hα, he⟩ := (A.mem_check_iff κ _).mp hlt
    obtain ⟨f, hf⟩ := cofinalMap_exists (A.check κ)
    rw [he] at hf
    obtain ⟨β, hβ, hbound⟩ := hb α hα f hf.1
    obtain ⟨a, ha, hβa⟩ := hf.2 β hβ
    exact False.elim (mem_irrefl (f ‘ a) (hβa _ (hbound a ha)))
  refine ⟨hcf ▸ internalCofinality_initial (A.check κ), ?_, hcf⟩
  have hh := (A.checkEmbedding.subset_iff (ω : V) κ).mpr hω
  change A.check ω ⊆ A.check κ at hh
  rwa [show A.check ω = (ω : A.Model) from A.checkEmbedding.map_omega] at hh

theorem check_regular_of_separative_closed (A : ForcingContext V) {κ : V}
    (hκ : IsRegularCardinal κ) (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α)
    (hclosed : IsForcingClosedBelow A.P (forcingSeparativeOrder A.P A.R) κ) :
    IsRegularCardinal (A.check κ) := by
  let := hκ.1.1
  have hcf : internalCofinality (A.check κ) = A.check κ := by
    rcases IsOrdinal.subset_iff.mp (internalCofinality_subset (A.check κ)) with he | hlt
    · exact he
    obtain ⟨γ, hγ, he⟩ := (A.mem_check_iff κ _).mp hlt
    let := IsOrdinal.of_mem hγ
    obtain ⟨f, hf⟩ := cofinalMap_exists (A.check κ)
    rw [he] at hf
    have hthrough : IsForcingClosedThrough A.P (forcingSeparativeOrder A.P A.R) γ := by
      intro α hα hαγ
      let := hα
      exact hclosed α (ordinal_mem_of_subset_mem hαγ hγ)
    obtain ⟨g, hg, hgf⟩ := A.function_eq_check_of_separative_closed (hDC γ hγ) hthrough hf.1
    let := IsFunction.of_mem hg
    obtain ⟨β, hβ, hb⟩ := regularCardinal_maps_bounded hκ hγ hg
    obtain ⟨a, ha, hβa⟩ := hf.2 (A.check β) ((A.check_mem_iff β κ).mpr hβ)
    obtain ⟨j, hj, rfl⟩ := (A.mem_check_iff γ a).mp ha
    have hb' : f ‘ (A.check j) ∈ A.check β := by
      rw [← hgf, A.check_value ((domain_eq_of_mem_function hg).symm ▸ hj)]
      exact (A.check_mem_iff _ _).mpr (hb j hj)
    exact False.elim (mem_irrefl (f ‘ (A.check j)) (hβa _ hb'))
  refine ⟨hcf ▸ internalCofinality_initial (A.check κ), ?_, hcf⟩
  have hh := (A.checkEmbedding.subset_iff (ω : V) κ).mpr hκ.2.1
  change A.check ω ⊆ A.check κ at hh
  rwa [show A.check ω = (ω : A.Model) from A.checkEmbedding.map_omega] at hh

theorem projectionInclusion_regular_of_separative_closed (A B : ForcingContext V) {π E : V}
    (hπ : IsForcingSplitProjection A.P A.R B.P B.R π E)
    (he : forcingProjectionGeneric A.P A.R π B.G = A.G) {κ : A.Model}
    (hκ : IsRegularCardinal κ) (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α)
    (hclosed : IsForcingClosedBelow (A.projectionQuotient B.P π)
      (forcingSeparativeOrder (A.projectionQuotient B.P π) (A.projectionQuotientOrder B.P B.R π)) κ) :
    IsRegularCardinal (A.projectionInclusion B hπ he κ) := by
  let C := A.projectionQuotientContext B hπ he
  let j := A.projectionFactorizationElementaryMap B hπ he
  have hC := C.check_regular_of_separative_closed hκ hDC hclosed
  have hB := (Defined.eval_iff _).mp ((j.evalb regularCardinalFormula ![C.check κ]).mp
    ((Defined.eval_iff _).mpr hC))
  change IsRegularCardinal (A.projectionFactorizationEquiv B hπ he (C.check κ)) at hB
  exact A.projectionFactorizationEquiv_check B hπ he κ ▸ hB

theorem projectionInclusion_function_values_bounded_of_separative_closed (A B : ForcingContext V) {π E : V}
    (hπ : IsForcingSplitProjection A.P A.R B.P B.R π E)
    (he : forcingProjectionGeneric A.P A.R π B.G = A.G) {κ α : A.Model}
    (hκ : IsRegularCardinal κ) (hα : α ∈ κ) (hDC : InternalDependentChoiceAt α)
    (hclosed : IsForcingClosedThrough (A.projectionQuotient B.P π)
      (forcingSeparativeOrder (A.projectionQuotient B.P π) (A.projectionQuotientOrder B.P B.R π)) α)
    {f : B.Model}
    (hf : f ∈ A.projectionInclusion B hπ he κ ^ A.projectionInclusion B hπ he α) :
    ∃ β ∈ A.projectionInclusion B hπ he κ,
      ∀ a ∈ A.projectionInclusion B hπ he α, f ‘ a ∈ β := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hα
  let j := A.projectionInclusion B hπ he
  obtain ⟨g, hg, hgf⟩ := A.projectionInclusion_function_of_separative_closed B hπ he hDC hclosed hf
  obtain ⟨β, hβ, hb⟩ := regularCardinal_maps_bounded hκ hα hg
  refine ⟨j β, (j.mem_iff β κ).mpr hβ, ?_⟩
  intro a ha
  obtain ⟨b, hbα, rfl⟩ := j.endExtension α a ha
  rw [← hgf, ← j.map_value_total]
  exact (j.mem_iff _ _).mpr (hb b hbα)

theorem projectionInclusion_dependentChoiceBelow_of_separative_closed (A B : ForcingContext V) {π E : V}
    (hπ : IsForcingSplitProjection A.P A.R B.P B.R π E)
    (he : forcingProjectionGeneric A.P A.R π B.G = A.G) {κ : A.Model} [IsOrdinal κ]
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α)
    (hclosed : IsForcingClosedBelow (A.projectionQuotient B.P π)
      (forcingSeparativeOrder (A.projectionQuotient B.P π) (A.projectionQuotientOrder B.P B.R π)) κ) :
    ∀ α ∈ A.projectionInclusion B hπ he κ, InternalDependentChoiceAt α := by
  intro α hα
  obtain ⟨γ, hγ, rfl⟩ := (A.projectionInclusion B hπ he).endExtension κ α hα
  let := IsOrdinal.of_mem hγ
  apply A.projectionInclusion_dependentChoiceAt_of_separative_closed B hπ he (hDC γ hγ)
  intro β hβ hβγ
  let := hβ
  exact hclosed β (ordinal_mem_of_subset_mem hβγ hγ)

end ForcingContext
end ZFVP
