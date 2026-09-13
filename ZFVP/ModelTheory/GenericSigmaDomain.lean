import ZFVP.ModelTheory.GenericBoundedTruth
import ZFVP.SetTheory.ForcingNameFamilyExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem sigmaOneTruth_forcingDomain (A : ForcingContext V) {n φ b : V}
    [IsFunction b] (hs : IsNameSequence A.P b) (hd : domain b = n)
    (hφ : IsMembershipFormulaCode n φ)
    (hσ : IsLevyFormulaCode .sigma 1 (A.check n) (A.check φ))
    (ht : SigmaOneTruth (A.check n) (A.check φ) (A.sequenceValue b hs)) :
    ∃ p ∈ A.G, ∃ D, IsForcingNameFamily A.P D ∧ IsNonempty D ∧ b ∈ D ^ n ∧
      InternalForces A.P A.R D n φ b p := by
  obtain ⟨T, hT, hneT, hbT, ht⟩ := ht
  obtain ⟨τ, hτ⟩ := A.ofName_surjective T
  obtain ⟨D, hD, hne, hb, hτD⟩ := nameSequence_family_with_witness hs hd τ.property
  let E := range (A.evaluationGraph D hD.names)
  have hc : ∀ σ ∈ D, ∀ u p, ⟨u, p⟩ₖ ∈ σ → u ∈ D :=
    fun σ hσ u _ hu ↦ hD.subname_closed σ hσ u (mem_domain_of_kpair_mem hu)
  let : IsTransitive E := A.evaluationRange_transitive D hD.names hc
  let : IsTransitive T := hT
  have hET : T ⊆ E := by
    intro x hx
    have hτE : A.ofName τ ∈ E :=
      (A.mem_range_evaluationGraph_iff D hD.names _).mpr ⟨τ.val, hτD, rfl⟩
    exact (show IsTransitive E from inferInstance).mem_trans (hτ ▸ hx) hτE
  have htE := membershipSatisfies_sigmaOne_upward hσ hneT
    (A.evaluationRange_nonempty D hD.names hne) hET hbT ht
  obtain ⟨p, hp, hf⟩ := (A.groundGenericTruth D hD.names hφ b hb).mp htE
  exact ⟨p, hp, D, hD, hne, hb, (mem_internalForcingSet hφ).mp hf⟩

end ForcingContext
end ZFVP
