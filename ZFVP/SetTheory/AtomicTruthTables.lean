import ZFVP.SetTheory.AtomicMembership

/-! A set of equality triples is determined by the atomic forcing equations. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def atomicTruthSet (P H σ τ : V) : V :=
  {p ∈ P ; ⟨⟨σ, τ⟩ₖ, p⟩ₖ ∈ H}

instance atomicTruthSet_definable (P H : V) : ℒₛₑₜ-function₂[V] (atomicTruthSet P H) := by
  have h : ℒₛₑₜ-relation₃[V] (fun C σ τ ↦ ∀ p, p ∈ C ↔ p ∈ P ∧ ⟨⟨σ, τ⟩ₖ, p⟩ₖ ∈ H) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = atomicTruthSet P H (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp [atomicTruthSet]

theorem mem_atomicTruthSet_iff (P H σ τ p : V) :
    p ∈ atomicTruthSet P H σ τ ↔ p ∈ P ∧ ⟨⟨σ, τ⟩ₖ, p⟩ₖ ∈ H := by
  simp [atomicTruthSet]

def IsAtomicTruthTable (P R T H : V) : Prop := ∀ σ ∈ T, ∀ τ ∈ T, ∀ p ∈ P,
  ⟨⟨σ, τ⟩ₖ, p⟩ₖ ∈ H ↔ AtomicEqualityTest P R (atomicTruthSet P H) σ τ p

theorem IsAtomicTruthTable.correct {P R T H : V} (h : IsAtomicTruthTable P R T H)
    (hT : IsSubnameClosed T) : ∀ σ ∈ T, ∀ τ ∈ T, atomicTruthSet P H σ τ = atomicEquality P R σ τ := by
  apply projectedRank_induction T (fun x : V ↦ x) (by definability)
    (fun σ ↦ ∀ τ ∈ T, atomicTruthSet P H σ τ = atomicEquality P R σ τ) (by definability)
  intro σ hσ ih τ hτ
  apply mem_ext
  intro p
  rw [mem_atomicTruthSet_iff, mem_atomicEquality_iff]
  apply and_congr_right
  intro hp
  rw [h σ hσ τ hτ p hp]
  apply atomicEqualityTest_congr
  intro υ s hs ν t ht
  exact ih υ (hT σ hσ υ (mem_domain_of_kpair_mem hs)) (rank_subname_lt hs)
    ν (hT τ hτ ν (mem_domain_of_kpair_mem ht))

theorem IsAtomicTruthTable.entry {P R T H σ τ p : V} (h : IsAtomicTruthTable P R T H)
    (hT : IsSubnameClosed T) (hσ : σ ∈ T) (hτ : τ ∈ T) :
    p ∈ P ∧ ⟨⟨σ, τ⟩ₖ, p⟩ₖ ∈ H ↔ p ∈ atomicEquality P R σ τ := by
  rw [← mem_atomicTruthSet_iff, h.correct hT σ hσ τ hτ]

theorem atomicTruthTable_exists (P R T : V) (hT : IsSubnameClosed T) :
    ∃ H : V, IsAtomicTruthTable P R T H := by
  let H : V := {z ∈ (T ×ˢ T) ×ˢ P ; kpair.π₂ z ∈
    atomicEquality P R (kpair.π₁ (kpair.π₁ z)) (kpair.π₂ (kpair.π₁ z))}
  have hmem (σ τ p : V) : ⟨⟨σ, τ⟩ₖ, p⟩ₖ ∈ H ↔
      σ ∈ T ∧ τ ∈ T ∧ p ∈ P ∧ p ∈ atomicEquality P R σ τ := by
    simp [H, and_assoc]
  have hsets {σ τ : V} (hσ : σ ∈ T) (hτ : τ ∈ T) :
      atomicTruthSet P H σ τ = atomicEquality P R σ τ := by
    apply mem_ext
    intro p
    rw [mem_atomicTruthSet_iff, hmem]
    exact ⟨fun hp ↦ hp.2.2.2.2,
      fun hp ↦ ⟨atomicEquality_subset P R σ τ p hp, hσ, hτ, atomicEquality_subset P R σ τ p hp, hp⟩⟩
  refine ⟨H, ?_⟩
  intro σ hσ τ hτ p hp
  rw [hmem]
  have he := atomicEqualityTest_congr P R σ τ p (atomicTruthSet P H) (atomicEquality P R)
    (fun υ s hs ν t ht ↦ hsets (hT σ hσ υ (mem_domain_of_kpair_mem hs))
      (hT τ hτ ν (mem_domain_of_kpair_mem ht)))
  rw [he, mem_atomicEquality_iff]
  simp only [hσ, hτ, hp, true_and]

end ZFVP
