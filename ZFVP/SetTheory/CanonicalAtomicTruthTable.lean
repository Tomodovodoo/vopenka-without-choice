import ZFVP.SetTheory.AtomicTruthTables
import ZFVP.SetTheory.RankBounds
import ZFVP.SetTheory.AtomicForcingDictionary

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def canonicalAtomicTruthTable (P R U : V) : V :=
  {z ∈ (U ×ˢ U) ×ˢ P; kpair.π₂ z ∈ atomicEquality P R (kpair.π₁ (kpair.π₁ z)) (kpair.π₂ (kpair.π₁ z))}

attribute [local aesop safe (rule_sets := [Definability])] Language.DefinableFunction₄.comp

instance canonicalAtomicTruthTable_definable : ℒₛₑₜ-function₃[V] canonicalAtomicTruthTable := by
  let : ℒₛₑₜ-function₄[V] atomicEquality := atomicEqualityFormula_defined.to_definable
  have hd : ℒₛₑₜ-relation₄[V] (fun H P R U ↦ ∀ z,
      z ∈ H ↔ z ∈ (U ×ˢ U) ×ˢ P ∧
        kpair.π₂ z ∈ atomicEquality P R (kpair.π₁ (kpair.π₁ z)) (kpair.π₂ (kpair.π₁ z))) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = canonicalAtomicTruthTable (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [canonicalAtomicTruthTable, mem_sep_iff]

theorem mem_canonicalAtomicTruthTable_iff {P R U σ τ p : V} :
    ⟨⟨σ, τ⟩ₖ, p⟩ₖ ∈ canonicalAtomicTruthTable P R U ↔
      σ ∈ U ∧ τ ∈ U ∧ p ∈ P ∧ p ∈ atomicEquality P R σ τ := by
  simp [canonicalAtomicTruthTable, and_assoc]

theorem canonicalAtomicTruthTable_sets {P R U σ τ : V} (hσ : σ ∈ U) (hτ : τ ∈ U) :
    atomicTruthSet P (canonicalAtomicTruthTable P R U) σ τ = atomicEquality P R σ τ := by
  apply mem_ext
  intro p
  rw [mem_atomicTruthSet_iff, mem_canonicalAtomicTruthTable_iff]
  exact ⟨fun h ↦ h.2.2.2.2, fun h ↦ ⟨atomicEquality_subset _ _ _ _ _ h,
    hσ, hτ, atomicEquality_subset _ _ _ _ _ h, h⟩⟩

theorem canonicalAtomicTruthTable_spec (P R U : V) (hU : IsSubnameClosed U) :
    IsAtomicTruthTable P R U (canonicalAtomicTruthTable P R U) := by
  intro σ hσ τ hτ p hp
  rw [mem_canonicalAtomicTruthTable_iff]
  have he := atomicEqualityTest_congr P R σ τ p
    (atomicTruthSet P (canonicalAtomicTruthTable P R U)) (atomicEquality P R)
    (fun υ s hs ν t ht ↦ canonicalAtomicTruthTable_sets
      (hU σ hσ υ (mem_domain_of_kpair_mem hs)) (hU τ hτ ν (mem_domain_of_kpair_mem ht)))
  rw [he, mem_atomicEquality_iff]
  simp only [hσ, hτ, hp, true_and]

theorem canonicalAtomicTruthTable_subset_hierarchy {P R η : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hP : P ⊆ hierarchy η) :
    canonicalAtomicTruthTable P R (hierarchy η) ⊆ hierarchy η := by
  intro z hz
  obtain ⟨st, hst, p, hp, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨σ, hσ, τ, hτ, rfl⟩ := mem_prod_iff.mp hst
  exact kpair_mem_hierarchy_limit hη (kpair_mem_hierarchy_limit hη hσ hτ) (hP p hp)

theorem canonicalAtomicTruthTable_mem_successor {P R η : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hP : P ⊆ hierarchy η) :
    canonicalAtomicTruthTable P R (hierarchy η) ∈ hierarchy (succ η) := by
  rw [hierarchy_succ, mem_power_iff]
  exact canonicalAtomicTruthTable_subset_hierarchy hη hP

end ZFVP
