import ZFVP.ModelTheory.WoodinSparseRestrictedLiftRank

/-! Ground ordinals enumerate the ordinals of the actual sparse endpoint rank. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinSparseEndpointModel
variable {Ω : V} [IsOrdinal Ω] (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
  {G : Set V} (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG
local notation "W" => RankModel hΩ hAC hG

theorem checkedOrdinal_mem_iff {α β : V} [IsOrdinal α] [IsOrdinal β]
    (hα : α ∈ Ω) (hβ : β ∈ Ω) :
    checkedOrdinal hΩ hAC hG hα ∈ checkedOrdinal hΩ hAC hG hβ ↔ α ∈ β :=
  (E).check_mem_iff α β

theorem checkedOrdinal_eq_iff {α β : V} [IsOrdinal α] [IsOrdinal β]
    (hα : α ∈ Ω) (hβ : β ∈ Ω) :
    checkedOrdinal hΩ hAC hG hα = checkedOrdinal hΩ hAC hG hβ ↔ α = β := by
  constructor
  · intro h
    exact (E).checkEmbedding.injective (congrArg Subtype.val h)
  · intro h
    subst β
    rfl

/-- This quantifies over all ordinals of the rank model, including those
represented by arbitrary names of a possibly ill-founded ground model. -/
theorem ordinal_eq_checkedOrdinal (α : W) (hα : IsOrdinal α) :
    ∃ (β : V) (hβ : IsOrdinal β) (hβΩ : β ∈ Ω),
      letI := hβ
      α = checkedOrdinal hΩ hAC hG hβΩ := by
  let := hierarchy_transitive ((E).check Ω)
  let : IsOrdinal α.val := (TransitiveZF.ordinal_iff (hierarchy ((E).check Ω)) α).mp hα
  obtain ⟨β, hβ, he⟩ := (E).ordinal_eq_check α.val
  let := hβ
  have hβΩ : β ∈ Ω := ((E).check_mem_iff _ _).mp
    (he ▸ ordinal_mem_hierarchy_iff.mp α.property)
  exact ⟨β, hβ, hβΩ, Subtype.ext he⟩

end WoodinSparseEndpointModel
end ZFVP
