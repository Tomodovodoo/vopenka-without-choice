import ZFVP.SetTheory.BoundedDependentChoiceFailure
import ZFVP.SetTheory.WoodinClosedContainers

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem closedContainer_shortFunctions {B κ : V} [IsOrdinal κ]
    (ht : IsTransitive B) (hr : IsFunctionRestrictionClosed B)
    (hκ : κ ∈ B) (hc : B ^ κ ⊆ B) :
    ∀ A ∈ B, ∀ β ∈ succ κ, ∀ f ∈ A ^ β, f ∈ B := by
  intro A hA β hβ f hf
  have hβB : β ∈ B := by
    rcases mem_succ_iff.mp hβ with rfl | hβ
    · exact hκ
    · exact ht.mem_trans hβ hκ
  have hβκ : β ⊆ κ := by
    rcases mem_succ_iff.mp hβ with rfl | hβ
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hβ
  exact hr.function_mem hc hκ hβB hβκ ⟨κ, hκ⟩
    (mem_function_of_mem_function_of_subset hf (ht.transitive A hA))

theorem IsWoodinSupercompact.dependentChoice_failure_certificate_at {δ κ α : V} [IsOrdinal α]
    (hδ : IsWoodinSupercompact δ) (hκ : κ ∈ α) (hfail : ¬InternalDependentChoiceAt κ) :
    ∃ B : V, IsRankFunctionClosed α B ∧ hierarchy α ∈ B ∧ κ ∈ B ∧
      IsTransitive B ∧ IsFunctionRestrictionClosed B ∧ IsBoundedDependentChoiceFailure κ B := by
  classical
  let := IsOrdinal.of_mem hκ
  unfold InternalDependentChoiceAt at hfail
  push Not at hfail
  obtain ⟨A, R, hA, hserial, hno⟩ := hfail
  let D := hierarchy α
  obtain ⟨B, hc, hp, ht, hr⟩ := hδ.exists_rankClosed_restrictionContainer α ⟨⟨A, R⟩ₖ, D⟩ₖ
  let := ht
  obtain ⟨hAR, hD⟩ := kpair_components_mem_transitive hp
  obtain ⟨hAB, hRB⟩ := kpair_components_mem_transitive hAR
  have hκD : κ ∈ D := ordinal_mem_hierarchy_iff.mpr hκ
  have hκB : κ ∈ B := ht.mem_trans hκD hD
  have hκsub : κ ⊆ D := (hierarchy_transitive α).transitive κ hκD
  have hcκ : B ^ κ ⊆ B := fun f hf ↦ hr.function_mem hc hD hκB hκsub ⟨κ, hκB⟩ hf
  have hshort := closedContainer_shortFunctions ht hr hκB hcκ
  refine ⟨B, hc, hD, hκB, ht, hr, A, hAB, R, hRB, hA, ?_, ?_⟩
  · intro β hβ s _hs hsf
    exact hserial s ((mem_shorterSequences _ _ _).mpr ⟨β, hβ, hsf⟩)
  · intro f _hfB hpath
    have hp := (boundedDependentChoicePath_iff
      (fun β hβ r hrf ↦ hshort A hAB β (mem_succ_iff.mpr (Or.inr hβ)) r hrf)).mp hpath
    obtain ⟨β, hβ, hn⟩ := hno f hp.1
    exact hn (hp.2 β hβ)

theorem IsWoodinSupercompact.dependentChoice_failure_certificate {δ κ : V} [IsOrdinal κ]
    (hδ : IsWoodinSupercompact δ) (hfail : ¬InternalDependentChoiceAt κ) :
    ∃ B : V, IsRankFunctionClosed (succ κ) B ∧ hierarchy (succ κ) ∈ B ∧ κ ∈ B ∧
      IsTransitive B ∧ IsFunctionRestrictionClosed B ∧ IsBoundedDependentChoiceFailure κ B :=
  hδ.dependentChoice_failure_certificate_at (mem_succ_self κ) hfail

end ZFVP
