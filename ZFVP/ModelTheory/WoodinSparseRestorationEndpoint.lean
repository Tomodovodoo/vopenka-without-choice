import ZFVP.ModelTheory.WoodinSparseRestorationGround
import ZFVP.ModelTheory.WoodinSparseEndpointZFC

/-! Existence of an actual generic endpoint for finite restoration.
Countability is external; no external well-foundedness of the ground model
or of its internally coded names is used.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Meet the internally coded dense sets of the actual constructed endpoint. -/
theorem exists_woodinEndpointGeneric [Countable V] {Λ : V}
    (hΛ : IsWoodinSupercompact Λ) (hAC : ¬InternalChoice V) :
    ∃ G : Set V, IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ) G := by
  have hvalid := (woodinIteration_endpoint_valid hΛ hAC).1.code.system
  obtain ⟨G, hG, _⟩ := exists_externalForcingGeneric
    (hvalid.order.preorder Λ (mem_succ_self Λ))
    (hvalid.tops.top Λ (mem_succ_self Λ)).1
  exact ⟨G, hG⟩

variable [Countable V] [V↓[ℒₛₑₜ] ⊧* unboundedExtendibilityTheory]

/-- UE supplies a sufficiently correct extendible endpoint,
the generic of its actual iteration, and its actual sparse ZFC rank. -/
theorem prunedUE_exists_sparseRestorationGeneric (r : ℕ) (code : SetTheorySemisentence 2)
    (hAC : ¬InternalChoice V) (α : V) (hα : IsOrdinal α) :
    ∃ (Λ : V) (hΛ : IsCnExtendible (woodinSparseRestorationLevel r code) Λ)
      (G : Set V) (hG : IsExternalForcingGeneric
        ((forcingCodeP (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ) G),
      α ∈ Λ ∧ (woodinSeedCardinal : V) ∈ Λ ∧
        letI : IsOrdinal Λ := hΛ.1.1
        (WoodinSparseEndpointModel.RankModel (woodinSparse_restorationFacts hΛ).2.2 hAC hG)↓[ℒₛₑₜ]
          ⊧* 𝗭𝗙𝗖 := by
  obtain ⟨Λ, hαΛ, hΛ, _, _, hW⟩ :=
    prunedUE_exists_sparseRestorationEndpoint (r := r) (code := code) α hα
  obtain ⟨G, hG⟩ := exists_woodinEndpointGeneric hW hAC
  let := hΛ.1.1
  exact ⟨Λ, hΛ, G, hG, hαΛ, woodinSeedCardinal_lt hW,
    WoodinSparseEndpointModel.rankModel_models_zfc (woodinSparse_restorationFacts hΛ).2.2 hAC hG⟩

end ZFVP
