import ZFVP.SetTheory.NameValue
import ZFVP.SetTheory.NameAction
import ZFVP.SetTheory.InverseFunction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem value_mem_image_iff {P Q π G p : V} (hπ : π ∈ Q ^ P) (hinj : Injective π)
    (hG : G ⊆ P) (hp : p ∈ P) : π ‘ p ∈ range (π ↾ G) ↔ p ∈ G := by
  have : IsFunction π := IsFunction.of_mem hπ
  constructor
  · intro h
    obtain ⟨q, hq⟩ := mem_range_iff.mp h
    obtain ⟨hqπ, hqG⟩ := kpair_mem_restrict_iff.mp hq
    have he : q = p := injective_value_eq hπ hinj (hG q hqG) hp (value_eq_of_kpair_mem hqπ)
    exact he ▸ hqG
  · intro hpG
    exact mem_range_of_kpair_mem (kpair_mem_restrict_iff.mpr
      ⟨kpair_value_mem (by simpa only [domain_eq_of_mem_function hπ] using hp), hpG⟩)

theorem nameValue_nameAction {P Q π G τ : V} (hπ : π ∈ Q ^ P) (hinj : Injective π)
    (hG : G ⊆ P) (hτ : IsForcingName P τ) :
    nameValue (range (π ↾ G)) (nameAction π τ) = nameValue G τ := by
  apply forcingName_induction P
    (fun τ ↦ nameValue (range (π ↾ G)) (nameAction π τ) = nameValue G τ) (by definability) ?_ τ hτ
  intro τ hτ ih
  apply SetTheory.mem_ext_iff.mpr
  intro z
  rw [mem_nameValue_iff, mem_nameValue_iff]
  constructor
  · rintro ⟨υ, q, hq, hυq, hz⟩
    obtain ⟨σ, p, hp, he⟩ := (mem_nameAction_iff hτ π _).mp hυq
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact ⟨σ, p, (value_mem_image_iff hπ hinj hG (forcingName_condition hτ hp)).mp hq, hp,
      by simpa only [ih σ p hp] using hz⟩
  · rintro ⟨σ, p, hpG, hp, hz⟩
    exact ⟨nameAction π σ, π ‘ p,
      (value_mem_image_iff hπ hinj hG (forcingName_condition hτ hp)).mpr hpG,
      (mem_nameAction_iff hτ π _).mpr ⟨σ, p, hp, rfl⟩,
      by simpa only [ih σ p hp] using hz⟩

end ZFVP
