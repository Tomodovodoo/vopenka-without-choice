import ZFVP.SetTheory.EndExtensionFinite
import ZFVP.SetTheory.WellOrderedSelection

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_prod (j : MembershipEndExtension V W) (A B : V) : j (A ×ˢ B) = j A ×ˢ j B := by
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := j.endExtension _ z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hx
    rw [j.map_kpair]
    exact kpair_mem_iff.mpr ⟨(j.mem_iff _ _).mpr ha, (j.mem_iff _ _).mpr hb⟩
  · intro hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨x, hx, rfl⟩ := j.endExtension A a ha
    obtain ⟨y, hy, rfl⟩ := j.endExtension B b hb
    rw [← j.map_kpair, j.mem_iff]
    exact kpair_mem_iff.mpr ⟨hx, hy⟩

theorem map_wellOrderable (j : MembershipEndExtension V W) {A : V} (hA : IsWellOrderable A) :
    IsWellOrderable (j A) := by
  obtain ⟨α, hα, haα⟩ := (wellOrderable_iff_cardLE_ordinal A).mp hA
  have hα' : IsOrdinal (j α) :=
    (j.bounded_defined isOrdinalFormula_bounded (fun v ↦ IsOrdinal (v 0))
      (fun v ↦ IsOrdinal (v 0)) ![α]).mp hα
  exact (wellOrderable_iff_cardLE_ordinal (j A)).mpr ⟨j α, hα', j.map_cardLE haα⟩

end MembershipEndExtension
end ZFVP
