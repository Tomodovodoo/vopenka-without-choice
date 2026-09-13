import ZFVP.ModelTheory.RankCollapsePrefixRestoration
import ZFVP.ModelTheory.WoodinStrictRestoration
import ZFVP.ModelTheory.WoodinPrefixSemantics

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]

namespace ForcingContext
variable (A : ForcingContext V) {κ c δ ρ γ e : V}
  [IsOrdinal c] [IsOrdinal δ]
  (hδ : IsWoodinSupercompact δ) (hρ : IsSigmaOneStarCorrect ρ) (hγ : IsSigmaOneStarCorrect γ)
  (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
  (hc : IsCriticalPoint (hierarchy (succ ρ)) e c) (hcρ : c ∈ ρ)
  (hci : IsChoicelessInaccessible c) (hP : A.P ∈ hierarchy c) (hR : A.R ∈ hierarchy c)
  (hκc : κ ∈ c) (hks : κ ⊆ c) (hcδ : c ∈ δ) (hcs : c ⊆ δ) (hz : (∅ : V) ∈ κ)
  (hec : e ‘ c = δ) (hκ : IsRegularCardinal (A.check κ))
  (hDC : ∀ α ∈ A.check κ, InternalDependentChoiceAt α)

include hδ hρ hγ he hc hcρ hci hP hR hκc hks hcδ hcs hz hec hκ hDC

theorem rankCollapse_initial_tail_dependentChoiceBelow {H : Set A.Model}
    (hH : IsExternalForcingGeneric (woodinCollapse (A.check κ) (A.check δ))
      (woodinCollapseOrder (A.check κ) (A.check δ)) H) :
    let Hc := woodinCollapseInitialGeneric (A.check κ) (A.check c) H
    let gc := A.rankCollapse_initial_generic hci hP hκ hcs hH
    ∀ η ∈ (woodinCollapseContext hκ (A.check c) Hc gc).check (A.check c), InternalDependentChoiceAt η := by
  dsimp only
  let Hc := woodinCollapseInitialGeneric (A.check κ) (A.check c) H
  let gc := A.rankCollapse_initial_generic hci hP hκ hcs hH
  let C := A.rankCollapseCombinedContext hci hP hks hz gc
  let B := A.rankCollapseCombinedContext hδ.inaccessible (hierarchy_mono hcs A.P hP)
    (subset_trans hks hcs) hz hH
  have hTail : ∀ p, p ∈ Hc ↔ p ∈ H ∧ p ∈ woodinCollapse (A.check κ) (A.check c) := fun _ ↦ Iff.rfl
  have hb : ∀ η ∈ B.check δ, InternalDependentChoiceAt η :=
    A.rankCollapse_combined_dependentChoiceBelow hδ (hierarchy_mono hcs A.P hP)
      (hierarchy_mono hcs A.R hR) (IsOrdinal.toIsTransitive.mem_trans hκc hcδ) hκ hDC hH
      (subset_trans hks hcs) hz
  have hd : ∀ η ∈ C.check c, InternalDependentChoiceAt η :=
    (A.rankCollapse_dependentChoiceBelow_iff hδ hρ hγ he hc hcρ hci hP hR hκc hks hcs hz hec
      gc hH hTail).mpr hb
  let ih := rankCollapse_iterand_countable A.order A.top hci hP hks hz
  let gh := A.rankCollapse_generic hci hP hks gc
  let T := TwoStepModel.iterandContext A ih gh
  have ht : T = woodinCollapseContext hκ (A.check c) Hc gc :=
    A.rankCollapse_iterandContext_eq hci hP hks hz gc hκ
  have hf := (TwoStepModel.combinedElementaryMap A ih gh).map_defined dependentChoiceBelowFormula
    (fun v ↦ ∀ η ∈ v 0, InternalDependentChoiceAt η)
    (fun v ↦ ∀ η ∈ v 0, InternalDependentChoiceAt η) ![C.check c]
  have hu : ∀ η ∈ T.check (A.check c), InternalDependentChoiceAt η := by
    have hh := hf.mp hd
    change ∀ η ∈ TwoStepModel.combinedEquiv A ih gh (C.check c), InternalDependentChoiceAt η at hh
    exact TwoStepModel.combinedEquiv_check A ih gh c ▸ hh
  rwa [ht] at hu

theorem rankCollapse_localRestoration : IsWoodinLocalRestoration (A.check κ) (A.check c) := by
  refine ⟨inferInstance, ?_⟩
  intro p hp
  have hreg := forcingFormula_regular (woodinCollapse_poset (A.check κ) (A.check c)).1
    dependentChoiceBelowFormula (standardTuple ![checkName ∅ (A.check c)])
  apply hreg.2.2 p hp
  intro q hq _
  have hs : A.check c ⊆ A.check δ := (A.checkEmbedding.subset_iff _ _).mpr hcs
  obtain ⟨H, hH, hqH⟩ := exists_externalForcingGeneric
    (woodinCollapse_poset (A.check κ) (A.check δ)).1 (woodinCollapse_mono hs q hq)
  let Hc := woodinCollapseInitialGeneric (A.check κ) (A.check c) H
  let gc := A.rankCollapse_initial_generic hci hP hκ hcs hH
  let T := woodinCollapseContext hκ (A.check c) Hc gc
  have hqT : q ∈ T.G := ⟨hqH, hq⟩
  have hd := A.rankCollapse_initial_tail_dependentChoiceBelow hδ hρ hγ he hc hcρ hci hP hR
    hκc hks hcδ hcs hz hec hκ hDC hH
  exact T.dependentChoiceBelow_forcing_witness hd hqT

end ForcingContext
end ZFVP
