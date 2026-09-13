import ZFVP.ModelTheory.WoodinEndpointPresentationCoherence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinIteration_endpoint_order {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) :
    (forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ =
      forcingThreadOrder δ (forcingCodeR (woodinIterationPrefix δ))
        (forcingDirectLimit δ (forcingCodeP (woodinIterationPrefix δ))
          (forcingCodeπ (woodinIterationPrefix δ)) (forcingCodeE (woodinIterationPrefix δ))
          (forcingCodeUniverse (woodinIterationPrefix δ))) := by
  rw [woodinIteration_endpoint_direct hδ hAC, kpair.π₁_kpair]
  exact forcingThreadCode_order _ _ _

theorem woodinIterationPrefix_extends_endpoint {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) :
    ForcingCodeExtends (woodinIterationPrefix δ) (kpair.π₁ (woodinIterationRec δ)) := by
  rw [woodinIteration_endpoint_direct hδ hAC, kpair.π₁_kpair]
  exact forcingThreadCode_extends (woodinIterationExit hδ hAC).2.2.1.code _

theorem woodinStageMap_endpoint_value {δ i p : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) (hz : ⟨i, p⟩ₖ ∈ woodinStageCarrier δ) :
    (woodinStageMap δ) ‘ ⟨i, p⟩ₖ =
      ((forcingCodeE (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨i, δ⟩ₖ) ‘ p := by
  let := hδ.inaccessible.1
  have hz' := (kpair_mem_forcingStageConditions_iff _ _ _ _ _).mp hz
  rw [woodinIteration_endpoint_section hδ hAC hz'.1]
  simp only [woodinStageMap, forcingStageThreadMap_value hz, kpair.π₁_kpair, kpair.π₂_kpair]
  exact (forcingThreadSection_value hz'.2.2).symm

/-- Literal inclusion of stage codes commutes with the actual endpoint section. -/
theorem woodinStageMap_endpoint_commutes {δ ε z : V}
    (hδ : IsWoodinSupercompact δ) (hε : IsWoodinSupercompact ε)
    (hAC : ¬InternalChoice V) (hδε : δ ∈ ε) (hz : z ∈ woodinStageCarrier δ) :
    (woodinStageMap ε) ‘ z =
      ((forcingCodeE (kpair.π₁ (woodinIterationRec ε))) ‘ ⟨δ, ε⟩ₖ) ‘
        ((woodinStageMap δ) ‘ z) := by
  let := hδ.inaccessible.1
  let := hε.inaccessible.1
  have hsub : δ ⊆ ε := IsOrdinal.toIsTransitive.transitive _ hδε
  have hzε := woodinStageCarrier_endpoint_mono hδ hε hAC hsub z hz
  obtain ⟨i, hi, p, _, hp, rfl⟩ := (mem_forcingStageConditions_iff _ _ _ _).mp hz
  rw [woodinStageMap_endpoint_value hε hAC hzε, woodinStageMap_endpoint_value hδ hAC hz]
  have hd := (woodinIteration_endpoint_valid hδ hAC).1.code
  have he := (woodinIteration_endpoint_valid hε hAC).1.code
  have hx := (woodinIterationRec_extends_to_prefix hδε).trans
    (woodinIterationPrefix_extends_endpoint hε hAC)
  have hiδ : i ∈ succ δ := mem_succ_iff.mpr (Or.inr hi)
  have hdδ := mem_succ_self δ
  have hE := hd.tableE.value_of_subset he.tableE hx.subE
    (mem_prod_iff.mpr ⟨i, hiδ, δ, hdδ, rfl⟩)
  rw [hE]
  have hP := (woodinIterationExit hδ hAC).2.2.1.code.tableP.value_of_subset he.tableP
    ((woodinIterationPrefix_extends_endpoint hδ hAC).trans hx).subP hi
  have hpε := hP ▸ hp
  exact (he.system.split.secComp i (mem_succ_iff.mpr (Or.inr (hsub i hi)))
    δ (mem_succ_iff.mpr (Or.inr hδε)) ε (mem_succ_self ε)
    (IsOrdinal.toIsTransitive.transitive _ hi) hsub p hpε).symm

end ZFVP
