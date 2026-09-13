import ZFVP.SetTheory.AtomicForcingSubstitution
import ZFVP.SetTheory.ForcingNegation

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def atomicSeparation (P R σ τ : V) : V :=
  {p ∈ P ; ∃ υ s, ⟨υ, s⟩ₖ ∈ σ ∧ ⟨p, s⟩ₖ ∈ R ∧
    p ∈ forcingNegation P R (atomicMembership P R υ τ)}

theorem mem_atomicSeparation_iff (P R σ τ p : V) : p ∈ atomicSeparation P R σ τ ↔
    p ∈ P ∧ ∃ υ s, ⟨υ, s⟩ₖ ∈ σ ∧ ⟨p, s⟩ₖ ∈ R ∧
      p ∈ forcingNegation P R (atomicMembership P R υ τ) := mem_sep_iff

instance atomicSeparation_definable (P R : V) : ℒₛₑₜ-function₂[V] (atomicSeparation P R) := by
  have h : ℒₛₑₜ-relation₃ (fun C σ τ : V ↦ ∀ p, p ∈ C ↔
      p ∈ P ∧ ∃ υ s, ⟨υ, s⟩ₖ ∈ σ ∧ ⟨p, s⟩ₖ ∈ R ∧
        p ∈ forcingNegation P R (atomicMembership P R υ τ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = atomicSeparation P R (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_atomicSeparation_iff]

theorem atomicSeparation_of_failure {P R σ τ p : V} (hR : IsForcingPreorder P R)
    (hn : ¬∀ υ s, ⟨υ, s⟩ₖ ∈ σ → ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨q, s⟩ₖ ∈ R →
      q ∈ atomicMembership P R υ τ) : ∃ q ∈ atomicSeparation P R σ τ, ⟨q, p⟩ₖ ∈ R := by
  classical
  push_neg at hn
  obtain ⟨υ, s, hs, q, hq, hqp, hqs, hnot⟩ := hn
  obtain ⟨r, hrN, hrq⟩ := exists_forcingNegation_of_not_mem hq hnot
    (fun q hq hd ↦ atomicMembership_dense hR hq hd)
  have hrP := forcingNegation_subset _ _ _ r hrN
  exact ⟨r, (mem_atomicSeparation_iff _ _ _ _ _).mpr
    ⟨hrP, υ, s, hs, hR.2.2 r hrP q hq s (forcingOrder_right_mem hR hqs) hrq hqs, hrN⟩,
    hR.2.2 r hrP q hq p (forcingOrder_right_mem hR hqp) hrq hqp⟩

noncomputable def atomicEqualityDecisions (P R σ τ : V) : V :=
  atomicEquality P R σ τ ∪ (atomicSeparation P R σ τ ∪ atomicSeparation P R τ σ)

theorem mem_atomicEqualityDecisions_iff (P R σ τ p : V) : p ∈ atomicEqualityDecisions P R σ τ ↔
    p ∈ atomicEquality P R σ τ ∨ p ∈ atomicSeparation P R σ τ ∨ p ∈ atomicSeparation P R τ σ := by
  simp only [atomicEqualityDecisions, mem_union_iff]

instance atomicEqualityDecisions_definable (P R : V) :
    ℒₛₑₜ-function₂[V] (atomicEqualityDecisions P R) := by
  unfold atomicEqualityDecisions
  definability

theorem atomicEqualityDecisions_dense {P R : V} (hR : IsForcingPreorder P R) (σ τ : V) :
    ForcingDense P R (atomicEqualityDecisions P R σ τ) := by
  classical
  refine ⟨?_, ?_⟩
  · intro p hp
    rcases (mem_atomicEqualityDecisions_iff _ _ _ _ _).mp hp with he | hl | hr
    · exact atomicEquality_subset _ _ _ _ p he
    · exact ((mem_atomicSeparation_iff _ _ _ _ _).mp hl).1
    · exact ((mem_atomicSeparation_iff _ _ _ _ _).mp hr).1
  · intro p hp
    by_cases he : p ∈ atomicEquality P R σ τ
    · exact ⟨p, (mem_atomicEqualityDecisions_iff _ _ _ _ _).mpr (Or.inl he), hR.2.1 p hp⟩
    · have hn := he
      rw [atomicEquality_iff_membership _ _ _ _ _ hR] at hn
      have hn' : ¬((∀ υ s, ⟨υ, s⟩ₖ ∈ σ → ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨q, s⟩ₖ ∈ R →
          q ∈ atomicMembership P R υ τ) ∧
        (∀ ν t, ⟨ν, t⟩ₖ ∈ τ → ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨q, t⟩ₖ ∈ R →
          q ∈ atomicMembership P R ν σ)) := fun h ↦ hn ⟨hp, h⟩
      rcases not_and_or.mp hn' with hl | hr
      · obtain ⟨q, hq, hqp⟩ := atomicSeparation_of_failure hR hl
        exact ⟨q, (mem_atomicEqualityDecisions_iff _ _ _ _ _).mpr (Or.inr (Or.inl hq)), hqp⟩
      · obtain ⟨q, hq, hqp⟩ := atomicSeparation_of_failure hR hr
        exact ⟨q, (mem_atomicEqualityDecisions_iff _ _ _ _ _).mpr (Or.inr (Or.inr hq)), hqp⟩

end ZFVP
