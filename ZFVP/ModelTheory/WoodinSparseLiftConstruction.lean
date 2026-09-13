import ZFVP.ModelTheory.WoodinSparseSuccessorLift
import ZFVP.ModelTheory.WoodinSparseInverseLift
import ZFVP.ModelTheory.WoodinSparseDirectLift

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseLiftRow_step {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (ih : ∀ j ∈ θ, IsWoodinSparseLiftRow j) : IsWoodinSparseLiftRow θ := by
  classical
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  intro i hi p hp b hb hle
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact woodinSparseStageMap_diagonal_lift hΩ hAC hsub hp hb hle
  have h0 : θ ≠ ∅ := fun he ↦ not_mem_empty (he ▸ hi)
  by_cases hsucc : θ = succ (⋃ˢ θ)
  · generalize hk : ⋃ˢ θ = k at hsucc
    subst θ
    let : IsOrdinal k := IsOrdinal.of_mem (mem_succ_self k)
    exact woodinSparseStageMap_successor_lift hΩ hAC hθ (ih k (mem_succ_self k)) hi hp hb hle
  by_cases hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))
  · exact woodinSparseStageMap_direct_lift hΩ hAC hsub h0 hsucc hinac ih hi hp hb hle
  · exact woodinSparseStageMap_inverse_lift hΩ hAC hθ h0 hsucc hinac ih hi hp hb hle

theorem woodinSparseLiftRow_correct {Ω : V} (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ∀ θ ∈ Ω, IsWoodinSparseLiftRow θ := by
  let := hΩ.inaccessible.1
  have hall := transfinite_induction (fun ξ : V ↦ ξ ∈ Ω → IsWoodinSparseLiftRow ξ) (by definability) ?_
  · intro θ hθ
    let := IsOrdinal.of_mem hθ
    exact hall (IsOrdinal.toOrdinal θ) hθ
  intro θ ih hθ
  apply woodinSparseLiftRow_step hΩ hAC hθ
  intro i hi
  let := IsOrdinal.of_mem hi
  exact ih (IsOrdinal.toOrdinal i) hi (IsOrdinal.toIsTransitive.mem_trans hi hθ)

theorem woodinSparseLiftRow_endpoint {Ω : V} (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    IsWoodinSparseLiftRow Ω := by
  let := hΩ.inaccessible.1
  obtain ⟨h0, hlim, hinac⟩ := woodinEndpoint_branch hΩ hAC
  intro i hi p hp b hb hle
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact woodinSparseStageMap_diagonal_lift hΩ hAC (subset_refl _) hp hb hle
  · exact woodinSparseStageMap_direct_lift hΩ hAC (subset_refl Ω) h0 hlim hinac
      (woodinSparseLiftRow_correct hΩ hAC) hi hp hb hle

theorem woodinSparseLiftRow_correct_le {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) : IsWoodinSparseLiftRow θ := by
  let := hΩ.inaccessible.1
  rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
  · exact woodinSparseLiftRow_endpoint hΩ hAC
  · exact woodinSparseLiftRow_correct hΩ hAC θ hθ

end ZFVP
