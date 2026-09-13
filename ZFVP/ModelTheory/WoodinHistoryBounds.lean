import ZFVP.ModelTheory.WoodinBoundDefinability
import ZFVP.ModelTheory.WoodinFixedBoundSteps
import ZFVP.SetTheory.ForcingBoundBaseSteps
import ZFVP.SetTheory.ForcingBoundRecursion
import ZFVP.SetTheory.NaturalPredecessor
import ZFVP.SetTheory.ForcingSystemDiagonal

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinal_limit_of_not_successor {θ : V} [IsOrdinal θ]
    (h : θ ≠ succ (⋃ˢ θ)) : ∀ j ∈ θ, succ j ∈ θ := by
  intro j hj
  let := IsOrdinal.of_mem hj
  rcases IsOrdinal.mem_trichotomy (succ j) θ with hlt | he | hgt
  · exact hlt
  · exact (h (by rw [← he, sUnion_succ_of_transitive])).elim
  · rcases mem_succ_iff.mp hgt with he | hθj
    · exact (mem_irrefl θ (he ▸ hj)).elim
    · exact (mem_irrefl θ (IsOrdinal.toIsTransitive.mem_trans hθj hj)).elim

/-- Bound-table rule for a supplied stage history, before limit restoration. -/
noncomputable def woodinHistoryBoundStep (P S K i I θ B : V) : V := by
  classical
  exact if θ ∈ i then forcingFamilyNext θ B ∅ else
    if θ = i then forcingFamilyNext θ B (forcingIdentityBound (P ‘ i) I) else
    if θ = succ (⋃ˢ θ) then woodinSuccessorBoundTable (⋃ˢ θ) (S ‘ θ) (K ‘ θ) B i I else
      woodinLimitBaseBoundTable θ (S ‘ θ) (K ‘ θ) B i I

instance woodinHistoryBoundStep_definable (P S K i I : V) :
    ℒₛₑₜ-function₂[V] (woodinHistoryBoundStep P S K i I) := by
  classical
  have hd : ℒₛₑₜ-relation₃ (fun y θ B : V ↦
      (θ ∈ i ∧ y = forcingFamilyNext θ B ∅) ∨
      (θ ∉ i ∧ θ = i ∧ y = forcingFamilyNext θ B (forcingIdentityBound (P ‘ i) I)) ∨
      (θ ∉ i ∧ θ ≠ i ∧ θ = succ (⋃ˢ θ) ∧
        y = woodinSuccessorBoundTable (⋃ˢ θ) (S ‘ θ) (K ‘ θ) B i I) ∨
      (θ ∉ i ∧ θ ≠ i ∧ θ ≠ succ (⋃ˢ θ) ∧
        y = woodinLimitBaseBoundTable θ (S ‘ θ) (K ‘ θ) B i I)) := by
    apply Language.Definable.or
    · definability
    · apply Language.Definable.or
      · definability
      · apply Language.Definable.or
        · apply Language.Definable.and
          · definability
          · apply Language.Definable.and
            · definability
            · apply Language.Definable.and
              · definability
              · apply Language.DefinableRel.comp (P := Eq)
                · definability
                · apply Language.DefinableFunction₄.comp (F := fun k s K B ↦ woodinSuccessorBoundTable k s K B i I) <;> definability
        · apply Language.Definable.and
          · definability
          · apply Language.Definable.and
            · definability
            · apply Language.Definable.and
              · definability
              · apply Language.DefinableRel.comp (P := Eq)
                · definability
                · apply Language.DefinableFunction₄.comp (F := fun θ s K B ↦ woodinLimitBaseBoundTable θ s K B i I) <;> definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = woodinHistoryBoundStep P S K i I (v 1) (v 2) ↔ _
  unfold woodinHistoryBoundStep
  split_ifs <;> tauto

/-- Construct coherent bounds from a history whose limit stages are the chosen bases.
The extra noninaccessible-limit collapse is not part of these history hypotheses. -/
theorem woodinHistoryBound_recursion {δ η z S K i I : V} [IsOrdinal η] [IsOrdinal i]
    (hδ : IsWoodinSupercompact δ) (hz : IsForcingIterationCode (succ η) z)
    (hh : ∀ θ ∈ succ η, i ∈ θ → IsWoodinIteration δ θ (S ‘ θ) (K ‘ θ))
    (hI : ∀ θ ∈ succ η, i ∈ θ → I ∈ (K ‘ θ) ‘ i)
    (hs : ∀ θ ∈ succ η, i ∈ θ → θ = succ (⋃ˢ θ) →
      ForcingCodeExtends (woodinIterationSuccessor (⋃ˢ θ) (S ‘ θ) (K ‘ θ)) z)
    (hl : ∀ θ ∈ succ η, i ∈ θ → (∀ j ∈ θ, succ j ∈ θ) →
      ForcingCodeExtends (woodinLimitBase θ (S ‘ θ) (K ‘ θ)) z) :
    let F := woodinHistoryBoundStep (forcingCodeP z) S K i I
    let b := Replacement.transfiniteRec (forcingBoundRecursionStep F)
      (forcingBoundRecursionStep_definable F (woodinHistoryBoundStep_definable _ _ _ _ _)) η
    IsIterationTable (succ η) b ∧
      IsCoherentForcingBound (succ η) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z) b i I ∧
      IsSectionCompatibleForcingBound (succ η) (forcingCodeP z) (forcingCodeR z)
        (forcingCodeπ z) (forcingCodeE z) b i I := by
  classical
  apply forcingBound_recursion (woodinHistoryBoundStep (forcingCodeP z) S K i I)
    (woodinHistoryBoundStep_definable _ _ _ _ _)
  intro θ hθη ho B ht hb hc
  let := ho
  rcases IsOrdinal.mem_trichotomy θ i with hθi | he | hiθ
  · have hsub : succ θ ⊆ i := by
      intro j hj
      rcases mem_succ_iff.mp hj with rfl | hj
      · exact hθi
      · exact IsOrdinal.toIsTransitive.mem_trans hj hθi
    simpa only [woodinHistoryBoundStep, ite_eq_left hθi] using
      forcingBound_step_before_base (P := forcingCodeP z) (R := forcingCodeR z)
        (π := forcingCodeπ z) (E := forcingCodeE z) (I := I) hsub ht
  · subst θ
    simpa only [woodinHistoryBoundStep, mem_irrefl, ite_false, ite_true] using
      forcingBound_step_at_base (I := I) ht
        (hz.system.split.projection_diagonal hz.system.functions hθη)
        (hz.system.split.section_diagonal hz.system.functions hθη)
  · have hn : θ ∉ i := by
      intro hθi
      exact mem_irrefl i (IsOrdinal.toIsTransitive.mem_trans hiθ hθi)
    have he : θ ≠ i := (ne_of_mem hiθ).symm
    simp only [woodinHistoryBoundStep, ite_eq_right hn, ite_eq_right he]
    by_cases hsucc : θ = succ (⋃ˢ θ)
    · rw [ite_eq_left hsucc]
      have hkθ : ⋃ˢ θ ∈ θ := by
        exact (congrArg (fun x : V ↦ (⋃ˢ θ) ∈ x) hsucc).mpr (mem_succ_self (⋃ˢ θ))
      let := IsOrdinal.of_mem hkθ
      have hw : IsWoodinIteration δ (succ (⋃ˢ θ)) (S ‘ θ) (K ‘ θ) := by
        simpa only [← hsucc] using hh θ hθη hiθ
      have hout := hw.successor_bound_step_fixed hδ hz (hs θ hθη hiθ hsucc)
        (by simpa only [← hsucc] using hiθ) (hI θ hθη hiθ)
        (by simpa only [← hsucc] using ht)
        (by simpa only [← hsucc] using hb)
        (by simpa only [← hsucc] using hc)
      simpa only [← hsucc] using hout
    · rw [ite_eq_right hsucc]
      have hlim := ordinal_limit_of_not_successor hsucc
      have h0 : (∅ : V) ∈ θ := by
        rcases IsOrdinal.subset_iff.mp (empty_subset i) with he0 | h0i
        · exact he0 ▸ hiθ
        · exact IsOrdinal.toIsTransitive.mem_trans h0i hiθ
      exact (hh θ hθη hiθ).limitBase_bound_step_fixed hlim h0 hz
        (hl θ hθη hiθ hlim) hiθ (hI θ hθη hiθ) ht hb hc

theorem IsCoherentForcingBound.relativeDirectedClosedAt {θ P R π B i I j : V}
    (h : IsCoherentForcingBound θ P R π B i I) (hj : j ∈ θ) (hij : i ⊆ j) :
    IsForcingRelativeDirectedClosedAt (P ‘ i) (R ‘ i) (P ‘ j) (R ‘ j) (π ‘ ⟨i, j⟩ₖ) I := by
  intro f hf p hp hb
  exact ⟨(B ‘ j) ‘ ⟨f, p⟩ₖ, h.bound j hj hij f hf p hp hb⟩

end ZFVP






