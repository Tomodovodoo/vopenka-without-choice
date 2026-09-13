import ZFVP.ModelTheory.ForcingRealizationEmbedding
import ZFVP.ModelTheory.ForcingModelNameValue

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingRealization
variable {A : ForcingContext V} (L : ForcingRealization A W)

theorem value_genericSet : L.value A.genericSet = L.genericSet := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨z, hz, he⟩ := L.value_endExtension A.genericSet hy
    obtain ⟨p, hp, rfl⟩ := (A.mem_genericSet_iff z).mp hz
    rw [L.value_check] at he
    exact he ▸ (L.generic_mem p).mpr hp
  · intro hy
    obtain ⟨p, hp, rfl⟩ := L.ground.endExtension A.P y (L.generic_subset y hy)
    have h := (L.value_mem_iff (A.check p) A.genericSet).mpr
      ((A.check_mem_genericSet_iff p).mpr ((L.generic_mem p).mp hy))
    rwa [L.value_check] at h

end ForcingRealization

namespace ForcingContext

theorem realization_value (A : ForcingContext V) (x : A.Model) : A.realization.value x = x := by
  obtain ⟨τ, rfl⟩ := A.ofName_surjective x
  exact A.nameValue_genericSet_check τ

end ForcingContext

namespace ForcingRealization
variable {A : ForcingContext V} (B : ForcingContext W)
  (L : ForcingRealization A B.Model)

theorem value_surjective_of_generators
    (hcheck : ∀ x : W, ∃ y : A.Model, L.value y = B.check x)
    (hgeneric : ∃ g : A.Model, L.value g = B.genericSet) : Function.Surjective L.value := by
  intro x
  obtain ⟨τ, rfl⟩ := B.ofName_surjective x
  obtain ⟨y, hy⟩ := hcheck τ.val
  obtain ⟨g, hg⟩ := hgeneric
  refine ⟨nameValue g y, ?_⟩
  have he := L.embedding.map_nameValue g y
  change L.value (nameValue g y) = nameValue (L.value g) (L.value y) at he
  rw [hg, hy, B.nameValue_genericSet_check τ] at he
  exact he

end ForcingRealization
end ZFVP
