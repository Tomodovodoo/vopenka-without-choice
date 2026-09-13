import ZFVP.SetTheory.DeltaOneAtomicForcing
import ZFVP.SetTheory.EndExtensionLevy
import ZFVP.SetTheory.EndExtensionWellOrdering
import ZFVP.SetTheory.AtomicSeparation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem atomicEquality_mem_iff (j : MembershipEndExtension V W) (P R σ τ p : V) :
    p ∈ atomicEquality P R σ τ ↔ j p ∈ atomicEquality (j P) (j R) (j σ) (j τ) :=
  j.deltaOne_defined (sigmaOneAtomicEqualityFormula_sigmaOne true) piOneAtomicEqualityFormula_piOne
    (fun v ↦ v 4 ∈ atomicEquality (v 0) (v 1) (v 2) (v 3))
    (fun v ↦ v 4 ∈ atomicEquality (v 0) (v 1) (v 2) (v 3)) ![P, R, σ, τ, p]

theorem atomicMembership_mem_iff (j : MembershipEndExtension V W) (P R σ τ p : V) :
    p ∈ atomicMembership P R σ τ ↔ j p ∈ atomicMembership (j P) (j R) (j σ) (j τ) :=
  j.deltaOne_defined (sigmaOneAtomicMembershipFormula_sigmaOne true) piOneAtomicMembershipFormula_piOne
    (fun v ↦ v 4 ∈ atomicMembership (v 0) (v 1) (v 2) (v 3))
    (fun v ↦ v 4 ∈ atomicMembership (v 0) (v 1) (v 2) (v 3)) ![P, R, σ, τ, p]

theorem map_atomicEquality (j : MembershipEndExtension V W) (P R σ τ : V) :
    j (atomicEquality P R σ τ) = atomicEquality (j P) (j R) (j σ) (j τ) := by
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := j.endExtension _ p hp
    exact (j.atomicEquality_mem_iff _ _ _ _ _).mp hq
  · intro hp
    obtain ⟨q, hq, rfl⟩ := j.endExtension P p (atomicEquality_subset _ _ _ _ p hp)
    exact (j.mem_iff _ _).mpr ((j.atomicEquality_mem_iff _ _ _ _ _).mpr hp)

theorem map_atomicMembership (j : MembershipEndExtension V W) (P R σ τ : V) :
    j (atomicMembership P R σ τ) = atomicMembership (j P) (j R) (j σ) (j τ) := by
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := j.endExtension _ p hp
    exact (j.atomicMembership_mem_iff _ _ _ _ _).mp hq
  · intro hp
    obtain ⟨q, hq, rfl⟩ := j.endExtension P p (atomicMembership_subset _ _ _ _ p hp)
    exact (j.mem_iff _ _).mpr ((j.atomicMembership_mem_iff _ _ _ _ _).mpr hp)

theorem map_forcingNegation (j : MembershipEndExtension V W) (P R A : V) :
    j (forcingNegation P R A) = forcingNegation (j P) (j R) (j A) := by
  unfold forcingNegation
  apply j.map_separation
  intro p hp
  rw [j.forall_mem_iff]
  simp only [← j.map_kpair, j.mem_iff]

theorem map_atomicSeparation (j : MembershipEndExtension V W) (P R σ τ : V) :
    j (atomicSeparation P R σ τ) = atomicSeparation (j P) (j R) (j σ) (j τ) := by
  unfold atomicSeparation
  apply j.map_separation
  intro p hp
  constructor
  · rintro ⟨υ, s, hυs, hps, hn⟩
    refine ⟨j υ, j s, ?_, ?_, ?_⟩
    · rw [← j.map_kpair, j.mem_iff]; exact hυs
    · rw [← j.map_kpair, j.mem_iff]; exact hps
    · rw [← j.map_atomicMembership, ← j.map_forcingNegation, j.mem_iff]
      exact hn
  · rintro ⟨υ, s, hυs, hps, hn⟩
    obtain ⟨ν, r, hνr, rfl, rfl⟩ := (j.pair_mem_image_iff σ υ s).mp hυs
    refine ⟨ν, r, hνr, ?_, ?_⟩
    · rwa [← j.map_kpair, j.mem_iff] at hps
    · rwa [← j.map_atomicMembership, ← j.map_forcingNegation, j.mem_iff] at hn

theorem map_atomicEqualityDecisions (j : MembershipEndExtension V W) (P R σ τ : V) :
    j (atomicEqualityDecisions P R σ τ) = atomicEqualityDecisions (j P) (j R) (j σ) (j τ) := by
  simp only [atomicEqualityDecisions, j.map_union, j.map_atomicEquality, j.map_atomicSeparation]

theorem map_subnameClosed (j : MembershipEndExtension V W) {N : V} (hN : IsSubnameClosed N) :
    IsSubnameClosed (j N) := by
  intro x hx y hy
  obtain ⟨τ, hτ, rfl⟩ := j.endExtension N x hx
  obtain ⟨s, hys⟩ := mem_domain_iff.mp hy
  obtain ⟨ν, p, hνp, rfl, rfl⟩ := (j.pair_mem_image_iff τ y s).mp hys
  exact (j.mem_iff _ _).mpr (hN τ hτ ν (mem_domain_of_kpair_mem hνp))

theorem map_forcingPreorder (j : MembershipEndExtension V W) {P R : V} (hR : IsForcingPreorder P R) :
    IsForcingPreorder (j P) (j R) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← j.map_prod]
    exact (j.subset_iff _ _).mpr hR.1
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := j.endExtension P p hp
    rw [← j.map_kpair, j.mem_iff]
    exact hR.2.1 q hq
  · intro p hp q hq r hr hpq hqr
    obtain ⟨a, ha, rfl⟩ := j.endExtension P p hp
    obtain ⟨b, hb, rfl⟩ := j.endExtension P q hq
    obtain ⟨c, hc, rfl⟩ := j.endExtension P r hr
    rw [← j.map_kpair, j.mem_iff] at hpq hqr ⊢
    exact hR.2.2 a ha b hb c hc hpq hqr

end MembershipEndExtension
end ZFVP
