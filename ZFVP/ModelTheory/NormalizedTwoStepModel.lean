import ZFVP.ModelTheory.NormalizedTwoStepExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R one δ Q S : V} [IsOrdinal δ]

local notation "Cₛ" => boundedNameTwoStep P R δ Q
local notation "Cₙ" => normalizedNameTwoStep P R one δ Q
local notation "Rₛ" => nameTwoStepOrderOn P R S Cₛ
local notation "Rₙ" => nameTwoStepOrderOn P R S Cₙ

noncomputable def boundedTwoStepContext
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅)
    (G : Set V) (hG : IsExternalForcingGeneric Cₛ Rₛ G) : ForcingContext V :=
  ⟨Cₛ, Rₛ, ⟨one, ∅⟩ₖ, G, boundedNameTwoStep_preorder hR ht hI.posetName hI.orderName hI.preorder,
    boundedNameTwoStep_top hR ht hP hI, hG⟩

noncomputable def normalizedTwoStepContext
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅)
    (G : Set V) (hG : IsExternalForcingGeneric Cₛ Rₛ G) : ForcingContext V := by
  have h0 := forcedTop_mem hR ht ht.1 ⟨Q, hI.posetName⟩ ⟨S, hI.orderName⟩ ⟨∅, hI.topName⟩ (hI.top one ht.1)
  exact ⟨Cₙ, Rₙ, ⟨one, ∅⟩ₖ, {z | z ∈ G ∧ z ∈ Cₙ},
    normalizedNameTwoStep_preorder hR ht hI.posetName hI.orderName hI.preorder,
    normalizedNameTwoStep_top hR ht hP hI,
    (normalizedNameTwoStep_generic_iff hR ht hδ hP hI.posetName hI.orderName h0 hI.preorder hG.1).mp hG⟩

variable (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
  (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅)
  (G : Set V)

include hR ht hδ hP hI G

/-- The normalized presentation gives an isomorphic membership model, with
the inclusion of its names as the forward map. -/
noncomputable def normalizedTwoStepModelEquiv (hG : IsExternalForcingGeneric Cₛ Rₛ G) : (normalizedTwoStepContext hR ht hδ hP hI G hG).Model ≃ (boundedTwoStepContext hR ht hP hI G hG).Model :=
  (normalizedTwoStepContext hR ht hδ hP hI G hG).equivalentRetractionModelEquiv (boundedTwoStepContext hR ht hP hI G hG) (normalizedTwoStepRetraction_spec hR ht hδ hP hI) (fun _ ↦ Iff.rfl) (normalizedTwoStepRetraction_below hR ht hδ hP hI)

theorem normalizedTwoStepModelEquiv_mem_iff (hG : IsExternalForcingGeneric Cₛ Rₛ G) (x y : (normalizedTwoStepContext hR ht hδ hP hI G hG).Model) :
    normalizedTwoStepModelEquiv hR ht hδ hP hI G hG x ∈
      normalizedTwoStepModelEquiv hR ht hδ hP hI G hG y ↔ x ∈ y :=
  (normalizedTwoStepContext hR ht hδ hP hI G hG).equivalentRetractionModelEquiv_mem_iff (boundedTwoStepContext hR ht hP hI G hG) (normalizedTwoStepRetraction_spec hR ht hδ hP hI) (fun _ ↦ Iff.rfl) (normalizedTwoStepRetraction_below hR ht hδ hP hI) x y

theorem normalizedTwoStepModelEquiv_check (hG : IsExternalForcingGeneric Cₛ Rₛ G) (x : V) :
    normalizedTwoStepModelEquiv hR ht hδ hP hI G hG ((normalizedTwoStepContext hR ht hδ hP hI G hG).check x) = (boundedTwoStepContext hR ht hP hI G hG).check x :=
  (normalizedTwoStepContext hR ht hδ hP hI G hG).equivalentRetractionModelEquiv_check (boundedTwoStepContext hR ht hP hI G hG) (normalizedTwoStepRetraction_spec hR ht hδ hP hI) (fun _ ↦ Iff.rfl) (normalizedTwoStepRetraction_below hR ht hδ hP hI) rfl x

theorem normalizedTwoStepModelEquiv_name (hG : IsExternalForcingGeneric Cₛ Rₛ G) (τ : ForcingName Cₙ) :
    normalizedTwoStepModelEquiv hR ht hδ hP hI G hG ((normalizedTwoStepContext hR ht hδ hP hI G hG).ofName τ) =
      (boundedTwoStepContext hR ht hP hI G hG).ofName ⟨τ.val, τ.property.mono (normalizedNameTwoStep_subset hR ht)⟩ :=
  (normalizedTwoStepContext hR ht hδ hP hI G hG).equivalentRetractionModelEquiv_name (boundedTwoStepContext hR ht hP hI G hG) (normalizedTwoStepRetraction_spec hR ht hδ hP hI) (fun _ ↦ Iff.rfl) (normalizedTwoStepRetraction_below hR ht hδ hP hI) τ

noncomputable def normalizedTwoStepElementaryMap (hG : IsExternalForcingGeneric Cₛ Rₛ G) : ElementaryMap (normalizedTwoStepContext hR ht hδ hP hI G hG).Model (boundedTwoStepContext hR ht hP hI G hG).Model :=
  ElementaryMap.ofMembershipIso (normalizedTwoStepModelEquiv hR ht hδ hP hI G hG)
    (normalizedTwoStepModelEquiv_mem_iff hR ht hδ hP hI G hG)

end ZFVP
