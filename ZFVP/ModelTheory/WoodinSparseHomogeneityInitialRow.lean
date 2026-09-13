import ZFVP.ModelTheory.WoodinSparseHomogeneityBuilder
import ZFVP.ModelTheory.CoherentAutomorphismWitnessRecursion

set_option maxHeartbeats 1000000

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseHomogeneityInitialRow_spec {Δ θ c a b δ H W : V} [IsOrdinal Δ] [IsOrdinal θ]
    (hc : IsForcingIterationCode Δ c) (hθ : θ ∈ Δ)
    (hh : IsCoherentAutomorphismWitnessHistory θ c a b δ H W) (hθδ : θ ⊆ δ)
    (hP : (forcingCodeP c) ‘ θ = (forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
    (ha : a ‘ θ ∈ (forcingCodeP c) ‘ θ)
    (hab : ⟨a ‘ θ, b ‘ θ⟩ₖ ∈ (forcingCodeR c) ‘ θ)
    (hap : ∀ i ∈ θ, ((forcingCodeπ c) ‘ ⟨i, θ⟩ₖ) ‘ (a ‘ θ) = a ‘ i) :
    IsCoherentAutomorphismWitnessRow θ c a b δ H W (woodinSparseHomogeneityInitialRow θ (a ‘ θ)) := by
  have he : woodinSparseHomogeneityInitialRow θ (a ‘ θ) = ⟨identity ((forcingCodeP c) ‘ θ), a ‘ θ⟩ₖ := by
    rw [woodinSparseHomogeneityInitialRow, hP]
  rw [he]
  have hiδ : ∀ i ∈ θ, i ⊆ δ := fun i hi ↦ subset_trans (IsOrdinal.toIsTransitive.transitive _ hi) hθδ
  have hiΔ : ∀ i ∈ θ, i ∈ Δ := fun i hi ↦ IsOrdinal.toIsTransitive.mem_trans hi hθ
  constructor <;> simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  · constructor
    · exact forcingAutomorphism_identity _ _
    · exact identity_value (hc.system.tops.top θ hθ).1
    · intro i hi p hp
      rw [identity_value hp]
      exact (hh.fixesInitial i hi (hiδ i hi) _
        (hc.system.split.projMaps i (hiΔ i hi) θ hθ (IsOrdinal.toIsTransitive.transitive _ hi) p hp)).symm
    · intro i hi p hp
      rw [hh.fixesInitial i hi (hiδ i hi) p hp]
      exact identity_value (hc.system.split.secMaps i (hiΔ i hi) θ hθ
        (IsOrdinal.toIsTransitive.transitive _ hi) p hp)
  · intro p hp
    simp only [identity_value hp]
  · intro _ p hp
    exact identity_value hp
  · exact ha
  · simpa only [kpair.π₁_kpair, kpair.π₂_kpair, identity_value ha] using (hc.system.order.preorder θ hθ).2.1 _ ha
  · exact hab
  · intro i hi
    simpa only [kpair.π₂_kpair, hh.initialWitness i hi (hiδ i hi)] using hap i hi
  · intro x hx
    exact mem_union_iff.mpr (Or.inl hx)
  · intro _
    trivial

end ZFVP


