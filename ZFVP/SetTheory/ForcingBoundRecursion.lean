import ZFVP.SetTheory.ForcingBoundDefinability
import ZFVP.SetTheory.ForcingBoundUnion
import ZFVP.SetTheory.UniformRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private def boundTableInvariant (P R π E i I θ B : V) : Prop :=
  IsFunction B ∧ domain B = θ ∧ IsCoherentForcingBound θ P R π B i I ∧
    IsSectionCompatibleForcingBound θ P R π E B i I

private instance boundTableInvariant_definable (P R π E i I : V) :
    ℒₛₑₜ-relation[V] (boundTableInvariant P R π E i I) := by
  unfold boundTableInvariant
  apply Language.Definable.and
  · definability
  · apply Language.Definable.and
    · definability
    · exact Language.Definable.and (coherentForcingBound_definable P R π i I)
        (sectionCompatibleForcingBound_definable P R π E i I)

noncomputable def forcingBoundRecursionStep (F : V → V → V) (H : V) : V :=
  F (domain H) (⋃ˢ range H)

theorem forcingBoundRecursionStep_definable (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    ℒₛₑₜ-function₁[V] (forcingBoundRecursionStep F) := by
  unfold forcingBoundRecursionStep
  definability

theorem forcingBound_recursion {η P R π E i I : V} [IsOrdinal η]
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F)
    (hstep : ∀ θ ∈ succ η, IsOrdinal θ → ∀ B,
      IsIterationTable θ B → IsCoherentForcingBound θ P R π B i I →
      IsSectionCompatibleForcingBound θ P R π E B i I →
      IsIterationTable (succ θ) (F θ B) ∧ IsCoherentForcingBound (succ θ) P R π (F θ B) i I ∧
      IsSectionCompatibleForcingBound (succ θ) P R π E (F θ B) i I ∧ B ⊆ F θ B) :
    let b := Replacement.transfiniteRec (forcingBoundRecursionStep F) (forcingBoundRecursionStep_definable F hF) η
    IsIterationTable (succ η) b ∧ IsCoherentForcingBound (succ η) P R π b i I ∧
      IsSectionCompatibleForcingBound (succ η) P R π E b i I := by
  let r := Replacement.transfiniteRec (forcingBoundRecursionStep F) (forcingBoundRecursionStep_definable F hF)
  have dr : ℒₛₑₜ-function₁ r := Replacement.transfiniteRec_definable _
  have hall := transfinite_induction
    (fun θ ↦ θ ∈ succ η → boundTableInvariant P R π E i I (succ θ) (r θ) ∧
      ∀ j ∈ θ, r j ⊆ r θ) (by definability) ?_
  · have hh := hall (IsOrdinal.toOrdinal η) (mem_succ_self η)
    exact ⟨⟨hh.1.1, hh.1.2.1⟩, hh.1.2.2.1, hh.1.2.2.2⟩
  intro θ ih hθη
  have hsub (j : V) (hj : j ∈ (θ : V)) : j ∈ succ η := IsOrdinal.toIsTransitive.mem_trans hj hθη
  have ht (j : V) (hj : j ∈ (θ : V)) : IsIterationTable (succ j) (r j) := by
    let := IsOrdinal.of_mem hj
    exact ⟨(ih (IsOrdinal.toOrdinal j) hj (hsub j hj)).1.1,
      (ih (IsOrdinal.toOrdinal j) hj (hsub j hj)).1.2.1⟩
  have hd : ∀ j ∈ (θ : V), ∀ k ∈ (θ : V), ∃ l ∈ (θ : V), r j ⊆ r l ∧ r k ⊆ r l := by
    intro j hj k hk
    let := IsOrdinal.of_mem hj
    let := IsOrdinal.of_mem hk
    rcases IsOrdinal.mem_trichotomy j k with hjk | rfl | hkj
    · exact ⟨k, hk, (ih (IsOrdinal.toOrdinal k) hk (hsub k hk)).2 j hjk, subset_refl _⟩
    · exact ⟨j, hj, subset_refl _, subset_refl _⟩
    · exact ⟨j, hj, subset_refl _, (ih (IsOrdinal.toOrdinal j) hj (hsub j hj)).2 k hkj⟩
  have hu := forcingBound_tableUnion dr ht hd
    (fun j hj ↦ by
      let := IsOrdinal.of_mem hj
      exact (ih (IsOrdinal.toOrdinal j) hj (hsub j hj)).1.2.2.1)
    (fun j hj ↦ by
      let := IsOrdinal.of_mem hj
      exact (ih (IsOrdinal.toOrdinal j) hj (hsub j hj)).1.2.2.2)
  have hs := hstep θ hθη inferInstance _ hu.1 hu.2.1 hu.2.2
  have he : r θ = F θ (iterationTableUnion θ r dr) := by
    have hh := Replacement.transfiniteRec_spec (forcingBoundRecursionStep F) (forcingBoundRecursionStep_definable F hF) θ
    change r θ = forcingBoundRecursionStep F (definableGraph θ r dr) at hh
    rw [hh]
    simp only [forcingBoundRecursionStep, domain_definableGraph, range_definableGraph, iterationTableUnion]
  rw [he]
  refine ⟨⟨hs.1.function, hs.1.domain_eq, hs.2.1, hs.2.2.1⟩, ?_⟩
  intro j hj
  apply subset_trans ?_ hs.2.2.2
  intro z hz
  exact mem_sUnion_iff.mpr ⟨r j, (repl_spec dr).mpr ⟨j, hj, rfl⟩, hz⟩

end ZFVP
