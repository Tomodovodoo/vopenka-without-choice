import ZFVP.ModelTheory.NormalizedTwoStepForcing
import ZFVP.ModelTheory.EquivalentSuborderFilterEquiv

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R one δ Q S : V} [IsOrdinal δ]

local notation "Cₛ" => boundedNameTwoStep P R δ Q
local notation "Cₙ" => normalizedNameTwoStep P R one δ Q
local notation "Rₛ" => nameTwoStepOrderOn P R S Cₛ
local notation "Rₙ" => nameTwoStepOrderOn P R S Cₙ

noncomputable def normalizedTwoStepGenericsEquiv
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅) :
    {G : Set V // IsExternalForcingGeneric Cₛ Rₛ G} ≃ {H : Set V // IsExternalForcingGeneric Cₙ Rₙ H} := by
  have h0 := forcedTop_mem hR ht ht.1 ⟨Q, hI.posetName⟩ ⟨S, hI.orderName⟩ ⟨∅, hI.topName⟩ (hI.top one ht.1)
  exact equivalentSuborderGenericsEquiv
    (boundedNameTwoStep_preorder hR ht hI.posetName hI.orderName hI.preorder)
    (normalizedNameTwoStep_subset hR ht)
    (fun _ hn _ hm ↦ normalizedNameTwoStep_inclusion_order_iff hR ht hn hm)
    (normalizedNameTwoStep_equivalent_representatives hR ht hδ hP hI.posetName hI.orderName h0 hI.preorder)

theorem normalizedTwoStepGenericsEquiv_apply
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅)
    (G : {G : Set V // IsExternalForcingGeneric Cₛ Rₛ G}) :
    (normalizedTwoStepGenericsEquiv hR ht hδ hP hI G).val = {n | n ∈ G.val ∧ n ∈ Cₙ} := rfl

theorem normalizedTwoStepGenericsEquiv_symm_apply
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅)
    (H : {H : Set V // IsExternalForcingGeneric Cₙ Rₙ H}) :
    ((normalizedTwoStepGenericsEquiv hR ht hδ hP hI).symm H).val = suborderGeneratedFilter Cₛ Rₛ H.val := rfl

theorem guardedTwoStepCode_generic_iff {G : Set V} {z : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅)
    (hG : IsExternalForcingFilter Cₛ Rₛ G) (hz : z ∈ Cₛ) :
    (guardedTwoStepCode P R one z ∈ G ∧ guardedTwoStepCode P R one z ∈ Cₙ) ↔ z ∈ G := by
  have h0 := forcedTop_mem hR ht ht.1 ⟨Q, hI.posetName⟩ ⟨S, hI.orderName⟩ ⟨∅, hI.topName⟩ (hI.top one ht.1)
  have hn := guardedTwoStepCode_mem hR ht hδ hP h0 hz
  have hp : kpair.π₁ z ∈ P := by
    obtain ⟨p, hp, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    simpa using hp
  have he := guardedTwoStepCode_equivalent hR ht hδ hP hI.posetName hI.orderName h0 (hI.preorder _ hp) hz
  exact ⟨fun h ↦ hG.2.2.1 _ h.1 z hz he.1,
    fun h ↦ ⟨hG.2.2.1 z h _ (normalizedNameTwoStep_subset hR ht _ hn) he.2, hn⟩⟩

end ZFVP
