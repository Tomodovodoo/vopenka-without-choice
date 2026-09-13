import ZFVP.SetTheory.AtomicMembership

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def atomicMembershipWitnesses (P R σ τ : V) : V :=
  {r ∈ P ; ∃ ν s, ⟨ν, s⟩ₖ ∈ τ ∧ ⟨r, s⟩ₖ ∈ R ∧ r ∈ atomicEquality P R σ ν}

theorem mem_atomicMembershipWitnesses_iff (P R σ τ r : V) :
    r ∈ atomicMembershipWitnesses P R σ τ ↔
      r ∈ P ∧ ∃ ν s, ⟨ν, s⟩ₖ ∈ τ ∧ ⟨r, s⟩ₖ ∈ R ∧ r ∈ atomicEquality P R σ ν := mem_sep_iff

instance atomicMembershipWitnesses_definable (P R : V) :
    ℒₛₑₜ-function₂[V] (atomicMembershipWitnesses P R) := by
  have h : ℒₛₑₜ-relation₃ (fun C σ τ : V ↦ ∀ r, r ∈ C ↔
      r ∈ P ∧ ∃ ν s, ⟨ν, s⟩ₖ ∈ τ ∧ ⟨r, s⟩ₖ ∈ R ∧ r ∈ atomicEquality P R σ ν) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = atomicMembershipWitnesses P R (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_atomicMembershipWitnesses_iff]

theorem atomicMembershipWitnesses_dense {P R σ τ p : V} (hp : p ∈ atomicMembership P R σ τ) :
    ForcingDenseBelow P R (atomicMembershipWitnesses P R σ τ) p := by
  obtain ⟨_, hh⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hp
  refine ⟨fun r hr ↦ (mem_sep_iff.mp hr).1, ?_⟩
  intro q hq hqp
  obtain ⟨r, hr, hrq, ν, s, hs, hrs, he⟩ := hh q hq hqp
  exact ⟨r, mem_sep_iff.mpr ⟨hr, ν, s, hs, hrs, he⟩, hrq⟩

end ZFVP
