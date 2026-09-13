import ZFVP.ModelTheory.SuccessorRankElementaryLift

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SuccessorRankLiftData
variable {A B : ForcingContext V} {δ ε e π : V} (L : SuccessorRankLiftData A B δ ε e)
  (hπ : IsForcingRetraction A.P A.R B.P B.R π)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)

theorem graph_agrees_rankLift (x : SetDomain (hierarchy (A.check δ))) :
    (L.graph hπ) ‘ (ForcingContext.retractionInclusion A B hπ hG x.val) =
      (L.rankElementaryLift x).val := by
  rw [← L.sourceRankName_value x, ForcingContext.retractionInclusion_ofName,
    L.graph_value hπ hG _ (L.sourceRankName_rank x)]
  rfl

noncomputable def graphSourceFun (x : SetDomain (hierarchy (A.check δ))) :
    SetDomain (domain (L.graph hπ)) :=
  ⟨ForcingContext.retractionInclusion A B hπ hG x.val, by
    rw [L.graph_domain_eq_rank_image hπ hG]
    exact (ForcingContext.retractionInclusion_mem_iff A B hπ hG _ _).mpr x.property⟩

theorem graphSourceFun_bijective : Function.Bijective (L.graphSourceFun hπ hG) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact ForcingContext.retractionInclusion_injective A B hπ hG (congrArg Subtype.val he)
  · intro x
    obtain ⟨τ, hτ, he⟩ := (L.graph_domain hπ x.val).mp x.property
    exact ⟨L.sourceRankValue τ hτ, Subtype.ext he.symm⟩

noncomputable def graphSourceEquiv :
    SetDomain (hierarchy (A.check δ)) ≃ SetDomain (domain (L.graph hπ)) :=
  Equiv.ofBijective (L.graphSourceFun hπ hG) (L.graphSourceFun_bijective hπ hG)

theorem graphSourceEquiv_mem (x y : SetDomain (hierarchy (A.check δ))) :
    L.graphSourceEquiv hπ hG x ∈ L.graphSourceEquiv hπ hG y ↔ x ∈ y :=
  ForcingContext.retractionInclusion_mem_iff A B hπ hG x.val y.val

noncomputable def graphElementaryMap :
    ElementaryMap (SetDomain (domain (L.graph hπ))) (SetDomain (hierarchy (B.check ε))) :=
  L.rankElementaryLift.comp (ElementaryMap.ofMembershipIso (L.graphSourceEquiv hπ hG).symm
    (fun x y ↦ by
      have he := L.graphSourceEquiv_mem hπ hG ((L.graphSourceEquiv hπ hG).symm x)
        ((L.graphSourceEquiv hπ hG).symm y)
      simpa only [Equiv.apply_symm_apply] using he.symm))

theorem graphElementaryMap_value (x : SetDomain (domain (L.graph hπ))) :
    (L.graphElementaryMap hπ hG x).val = (L.graph hπ) ‘ x.val := by
  have he := L.graph_agrees_rankLift hπ hG ((L.graphSourceEquiv hπ hG).symm x)
  have hx : ForcingContext.retractionInclusion A B hπ hG
      ((L.graphSourceEquiv hπ hG).symm x).val = x.val :=
    congrArg Subtype.val ((L.graphSourceEquiv hπ hG).apply_symm_apply x)
  rw [hx] at he
  exact he.symm

end SuccessorRankLiftData
end ZFVP
