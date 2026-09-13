import ZFVP.ModelTheory.ForcingSemanticConsequence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingRegular.subset_of_all_generics [Countable V] {P R A B : V}
    (hR : IsForcingPreorder P R) (hA : IsForcingRegular P R A) (hB : IsForcingRegular P R B)
    (h : ∀ G : Set V, IsExternalForcingGeneric P R G → GenericMeets G A → GenericMeets G B) :
    A ⊆ B := by
  intro p hp
  apply hB.2.2 p (hA.1 p hp)
  intro q hq hqp
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hR hq
  have hpG := hG.1.2.2.1 q hqG p (hA.1 p hp) hqp
  obtain ⟨r, hrG, hr⟩ := h G hG ⟨p, hpG, hp⟩
  obtain ⟨s, hsG, hsr, hsq⟩ := hG.1.2.2.2 r hrG q hqG
  exact ⟨s, hB.2.1 r hr s (hG.1.1 s hsG) hsr, hsq⟩

theorem IsForcingRegular.eq_of_all_generics [Countable V] {P R A B : V}
    (hR : IsForcingPreorder P R) (hA : IsForcingRegular P R A) (hB : IsForcingRegular P R B)
    (h : ∀ G : Set V, IsExternalForcingGeneric P R G → (GenericMeets G A ↔ GenericMeets G B)) :
    A = B := by
  apply mem_ext
  intro p
  exact ⟨hA.subset_of_all_generics hR hB (fun G hG ↦ (h G hG).mp) p,
    hB.subset_of_all_generics hR hA (fun G hG ↦ (h G hG).mpr) p⟩

end ZFVP
