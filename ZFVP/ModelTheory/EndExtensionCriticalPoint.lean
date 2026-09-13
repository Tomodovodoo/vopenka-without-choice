import ZFVP.ModelTheory.EndExtensionCodedMembershipEmbedding
import ZFVP.ModelTheory.CriticalPoint
import ZFVP.SetTheory.EndExtensionHierarchyAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem criticalPoint_map (j : MembershipEndExtension V W) {A f κ : V}
    [IsTransitive A] (hκ : IsCriticalPoint A f κ) :
    IsCriticalPoint (j A) (j f) (j κ) := by
  let := hκ.ordinal
  let : IsOrdinal (j κ) := (j.ordinal_iff κ).mpr hκ.ordinal
  have hmove : (j f) ‘ (j κ) ≠ j κ := by
    rw [← j.map_value_total]
    exact fun h ↦ hκ.moved (j.injective h)
  refine ⟨inferInstance, ⟨(j.mem_iff _ _).mpr hκ.mem_domain, hmove⟩, ?_⟩
  intro α hα hαmove
  let := hα
  rcases IsOrdinal.mem_trichotomy (j κ) α with hlt | heq | hgt
  · exact IsOrdinal.toIsTransitive.transitive _ hlt
  · rw [heq]
  · obtain ⟨a, ha, rfl⟩ := j.endExtension κ α hgt
    exact False.elim (hαmove.2 (by rw [← j.map_value_total, hκ.fixed_below ha]))

theorem criticalPoint_iff (j : MembershipEndExtension V W) {A f κ : V}
    [IsTransitive A] : IsCriticalPoint (j A) (j f) (j κ) ↔ IsCriticalPoint A f κ := by
  constructor
  · intro hκ
    refine ⟨(j.ordinal_iff κ).mp hκ.ordinal,
      ⟨(j.mem_iff _ _).mp hκ.mem_domain, ?_⟩, ?_⟩
    · intro heq
      exact hκ.moved (by rw [← j.map_value_total, heq])
    · intro α hα hαmove
      apply (j.subset_iff κ α).mp
      apply hκ.2.2 (j α) ((j.ordinal_iff α).mpr hα)
      refine ⟨(j.mem_iff _ _).mpr hαmove.1, ?_⟩
      intro heq
      rw [← j.map_value_total] at heq
      exact hαmove.2 (j.injective heq)
  · exact j.criticalPoint_map

end MembershipEndExtension
end ZFVP
