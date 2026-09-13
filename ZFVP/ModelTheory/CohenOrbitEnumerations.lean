import ZFVP.ModelTheory.CohenOrbitFamily
import ZFVP.SetTheory.FiniteDomainEnumerationFamily
import ZFVP.SetTheory.EndExtensionRelations

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)

/-- Ground enumerations give one internal finite enumeration of the input domain for every
member of the evaluated orbit family. Choice is used only in the ground model. -/
theorem cohen_orbit_enumeration_family (hAC : InternalChoice V) {D : V}
    (hD : IsCohenSupportPool D) :
    ∃ e : (cohenContext (ω : V) G hG).Model,
      ∀ j ∈ (cohenContext (ω : V) G hG).check D,
        ∃ n ∈ (ω : (cohenContext (ω : V) G hG).Model),
          e ‘ j ∈ (range (e ‘ j)) ^ n ∧
          range (e ‘ j) ⊆ (ω : (cohenContext (ω : V) G hG).Model) ∧
          ∀ a ∈ domain ((orbitFamily hG D hD) ‘ j), a ∈ reals hG ^ (range (e ‘ j)) := by
  let S := cohenContext (ω : V) G hG
  obtain ⟨s, hs, hsd, henum⟩ := finite_domain_enumeration_family hAC D kpair.π₂
    (by definability) (fun z hz ↦ (hD z hz).2.2.1)
  have : IsFunction s := hs
  refine ⟨S.check s, ?_⟩
  intro j hj
  obtain ⟨z, hz, rfl⟩ := (S.mem_check_iff D j).mp hj
  obtain ⟨n, hn, hsn, _, hsr⟩ := henum z hz
  have hv : (S.check s) ‘ (S.check z) = S.check (s ‘ z) :=
    (S.checkEmbedding.map_value s z (hsd.symm ▸ hz)).symm
  have hr : range (S.check (s ‘ z)) = S.check (kpair.π₂ z) :=
    (S.checkEmbedding.map_range (s ‘ z)).symm.trans (congrArg S.check hsr)
  refine ⟨S.check n, (S.checkEmbedding.natural_iff n).mpr hn, ?_⟩
  rw [hv, hr]
  refine ⟨(S.checkEmbedding.function_iff (s ‘ z) n (kpair.π₂ z)).mpr hsn, ?_, ?_⟩
  · rw [← S.checkEmbedding.map_omega]
    exact (S.checkEmbedding.subset_iff (kpair.π₂ z) (ω : V)).mpr (hD z hz).2.1
  · intro a ha
    rw [orbitFamily_value hG hD hz] at ha
    exact orbitEvaluation_domain_subset hG (kpair.π₂ z) (hD z hz).2.1 (hD z hz).2.2.1
      ⟨kpair.π₁ z, (hD z hz).1⟩ a ha

end CohenModel
end ZFVP
