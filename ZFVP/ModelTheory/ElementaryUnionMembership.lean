import ZFVP.ModelTheory.ElementaryBoundedWitness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A hull element in the union of a hull family belongs to a family member
that is itself in the hull. -/
theorem IsElementaryInclusion.union_member_witness {X B I z : V} [IsTransitive B]
    (h : IsElementaryInclusion X B) (hI : I ∈ X) (hz : z ∈ X) (hzU : z ∈ ⋃ˢ I) :
    ∃ Z ∈ I ∩ X, z ∈ Z := by
  obtain ⟨Z, hZI, hzZ⟩ := mem_sUnion_iff.mp hzU
  have hZB : Z ∈ B := (inferInstance : IsTransitive B).mem_trans hZI (h.subset _ hI)
  obtain ⟨Y, hYX, he⟩ := h.bounded_witness
    (φ := “Z I z. Z ∈ I ∧ z ∈ Z”) (.and (.rel _ _) (.rel _ _))
    ![I, z] (by simp [hI, hz]) ⟨Z, hZB, by simp [hZI, hzZ]⟩
  have hy : Y ∈ I ∧ z ∈ Y := by simpa using he
  exact ⟨Y, mem_inter_iff.mpr ⟨hy.1, hYX⟩, hy.2⟩

end ZFVP
