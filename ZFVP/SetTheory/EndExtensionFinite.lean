import ZFVP.SetTheory.EndExtensionRelations
import ZFVP.SetTheory.FiniteSets

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem injective_iff (j : MembershipEndExtension V W) (f : V) : Injective (j f) ↔ Injective f := by
  constructor
  · intro hf x y z hx hy
    apply j.injective
    apply hf (j x) (j y) (j z)
    · rw [← j.map_kpair, j.mem_iff]
      exact hx
    · rw [← j.map_kpair, j.mem_iff]
      exact hy
  · intro hf x y z hx hy
    obtain ⟨a, b, hab, rfl, rfl⟩ := (j.pair_mem_image_iff f x z).mp hx
    obtain ⟨c, d, hcd, rfl, hbd⟩ := (j.pair_mem_image_iff f y (j b)).mp hy
    have he : b = d := j.injective hbd
    subst d
    exact congrArg j (hf a c b hab hcd)

theorem map_cardLE (j : MembershipEndExtension V W) {A B : V} (h : A ≤# B) : j A ≤# j B := by
  obtain ⟨f, hf, hi⟩ := h
  exact ⟨j f, (j.function_iff f A B).mpr hf, (j.injective_iff f).mpr hi⟩

theorem map_cardEQ (j : MembershipEndExtension V W) {A B : V} (h : A ≋ B) : j A ≋ j B :=
  ⟨j.map_cardLE h.1, j.map_cardLE h.2⟩

theorem map_internallyFinite (j : MembershipEndExtension V W) {A : V}
    (hA : IsInternallyFinite A) : IsInternallyFinite (j A) := by
  obtain ⟨n, hn, hAn⟩ := hA
  exact ⟨j n, (j.natural_iff n).mpr hn, j.map_cardEQ hAn⟩

end MembershipEndExtension
end ZFVP
