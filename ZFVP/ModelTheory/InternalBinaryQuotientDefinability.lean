import ZFVP.ModelTheory.InternalBinaryQuotient

/-! Uniform definability of the actual quotient and projection. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance internalQuotientProjection_definable : ℒₛₑₜ-function₂[V] internalQuotientProjection := by
  have h : ℒₛₑₜ-relation₃[V] (fun Q D E ↦ ∀ p, p ∈ Q ↔ ∃ x ∈ D, p = ⟨x, internalEquivalenceClass D E x⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [internalQuotientProjection, mem_definableGraph_iff]
  rfl

instance internalQuotientEdges_definable : ℒₛₑₜ-function₃[V] internalQuotientEdges := by
  have h : ℒₛₑₜ-relation₄[V] (fun Q D E R ↦ ∀ q, q ∈ Q ↔ ∃ p ∈ R,
      q = ⟨internalEquivalenceClass D E (kpair.π₁ p), internalEquivalenceClass D E (kpair.π₂ p)⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_internalQuotientEdges]
  rfl

instance internalQuotientStructure_definable : ℒₛₑₜ-function₃[V] internalQuotientStructure := by
  unfold internalQuotientStructure
  definability

end ZFVP
