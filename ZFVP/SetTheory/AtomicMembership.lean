import ZFVP.SetTheory.AtomicEquality

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def AtomicMembershipTest (P R σ τ p : V) : Prop :=
  ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
    ∃ ν s, ⟨ν, s⟩ₖ ∈ τ ∧ ⟨r, s⟩ₖ ∈ R ∧ r ∈ atomicEquality P R σ ν

instance atomicMembershipTest_definable (P R : V) : ℒₛₑₜ-relation₃[V] (AtomicMembershipTest P R) := by
  unfold AtomicMembershipTest
  definability

noncomputable def atomicMembership (P R σ τ : V) : V :=
  sep P (AtomicMembershipTest P R σ τ) (by definability)

theorem mem_atomicMembership_iff (P R σ τ p : V) :
    p ∈ atomicMembership P R σ τ ↔ p ∈ P ∧ AtomicMembershipTest P R σ τ p := by
  simp only [atomicMembership, AtomicMembershipTest, mem_sep_iff]

instance atomicMembership_definable (P R : V) : ℒₛₑₜ-function₂[V] (atomicMembership P R) := by
  have h : ℒₛₑₜ-relation₃ (fun z σ τ : V ↦
      ∀ p, p ∈ z ↔ p ∈ P ∧ AtomicMembershipTest P R σ τ p) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = atomicMembership P R (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_atomicMembership_iff]

theorem atomicMembership_subset (P R σ τ : V) : atomicMembership P R σ τ ⊆ P := by
  intro p hp
  exact ((mem_atomicMembership_iff _ _ _ _ _).mp hp).1

theorem atomicMembership_mono {P R σ τ p q : V} (hR : IsForcingPreorder P R)
    (hp : p ∈ atomicMembership P R σ τ) (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R) :
    q ∈ atomicMembership P R σ τ := by
  obtain ⟨hpP, hh⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hp
  exact (mem_atomicMembership_iff _ _ _ _ _).mpr
    ⟨hq, fun r hr hrq ↦ hh r hr (hR.2.2 r hr q hq p hpP hrq hqp)⟩

theorem atomicMembership_dense {P R σ τ p : V} (hR : IsForcingPreorder P R) (hp : p ∈ P)
    (hd : ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ atomicMembership P R σ τ, ⟨r, q⟩ₖ ∈ R) :
    p ∈ atomicMembership P R σ τ := by
  apply (mem_atomicMembership_iff _ _ _ _ _).mpr
  refine ⟨hp, ?_⟩
  intro q hq hqp
  obtain ⟨r, hr, hrq⟩ := hd q hq hqp
  obtain ⟨hrP, hh⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hr
  obtain ⟨v, hv, hvr, ν, s, hs, hvs, he⟩ := hh r hrP (hR.2.1 r hrP)
  exact ⟨v, hv, hR.2.2 v hv r hrP q hq hvr hrq, ν, s, hs, hvs, he⟩

theorem atomicMembership_of_pair {P R σ τ p : V} (hR : IsForcingPreorder P R)
    (hp : p ∈ P) (hpair : ⟨σ, p⟩ₖ ∈ τ) : p ∈ atomicMembership P R σ τ := by
  apply (mem_atomicMembership_iff _ _ _ _ _).mpr
  refine ⟨hp, ?_⟩
  intro q hq hqp
  exact ⟨q, hq, hR.2.1 q hq, σ, p, hpair, hqp, (atomicEquality_refl hR σ).symm ▸ hq⟩

theorem atomicMembership_empty {P R : V} (hR : IsForcingPreorder P R) (σ : V) :
    atomicMembership P R σ ∅ = ∅ := by
  apply SetTheory.subset_antisymm ?_ (empty_subset _)
  intro p hp
  obtain ⟨hpP, hh⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hp
  obtain ⟨r, _, _, ν, s, hs, _, _⟩ := hh p hpP (hR.2.1 p hpP)
  exact False.elim (not_mem_empty hs)

end ZFVP
