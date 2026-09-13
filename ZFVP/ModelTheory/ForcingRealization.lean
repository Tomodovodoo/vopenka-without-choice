import ZFVP.ModelTheory.LocalAtomicTruth
import ZFVP.ModelTheory.ForcingModel
import ZFVP.SetTheory.EndExtensionAtomicForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An actual internal set realizing the prescribed external generic over an end extension. -/
structure ForcingRealization (A : ForcingContext V) (W : Type*) [SetStructure W] where
  ground : MembershipEndExtension V W
  genericSet : W
  generic_subset : genericSet ⊆ ground A.P
  generic_mem : ∀ p : V, ground p ∈ genericSet ↔ p ∈ A.G

namespace ForcingRealization
variable {A : ForcingContext V} (L : ForcingRealization A W)

theorem filter : IsForcingFilter (L.ground A.P) (L.ground A.R) L.genericSet := by
  refine ⟨L.generic_subset, ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := A.generic.1.2.1
    exact ⟨L.ground p, (L.generic_mem p).mpr hp⟩
  · intro p hp q hq hpq
    obtain ⟨a, ha, rfl⟩ := L.ground.endExtension A.P p (L.generic_subset p hp)
    obtain ⟨b, hb, rfl⟩ := L.ground.endExtension A.P q hq
    rw [← L.ground.map_kpair, L.ground.mem_iff] at hpq
    exact (L.generic_mem b).mpr (A.generic.1.2.2.1 a ((L.generic_mem a).mp hp) b hb hpq)
  · intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := L.ground.endExtension A.P p (L.generic_subset p hp)
    obtain ⟨b, hb, rfl⟩ := L.ground.endExtension A.P q (L.generic_subset q hq)
    obtain ⟨c, hc, hca, hcb⟩ := A.generic.1.2.2.2 a ((L.generic_mem a).mp hp) b ((L.generic_mem b).mp hq)
    exact ⟨L.ground c, (L.generic_mem c).mpr hc,
      by rw [← L.ground.map_kpair, L.ground.mem_iff]; exact hca,
      by rw [← L.ground.map_kpair, L.ground.mem_iff]; exact hcb⟩

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem meets_iff (D : V) :
    (∃ p ∈ L.genericSet, p ∈ L.ground D) ↔ GenericMeets A.G D := by
  constructor
  · rintro ⟨p, hp, hpD⟩
    obtain ⟨q, hq, rfl⟩ := L.ground.endExtension D p hpD
    exact ⟨q, (L.generic_mem q).mp hp, hq⟩
  · rintro ⟨p, hp, hpD⟩
    exact ⟨L.ground p, (L.generic_mem p).mpr hp, (L.ground.mem_iff p D).mpr hpD⟩

theorem membership_witnesses (N : V) :
    HasAtomicMembershipWitnesses (L.ground A.P) (L.ground A.R) (L.ground N) L.genericSet := by
  intro σ hσ τ hτ p hp hpM
  obtain ⟨x, hx, rfl⟩ := L.ground.endExtension N σ hσ
  obtain ⟨y, hy, rfl⟩ := L.ground.endExtension N τ hτ
  obtain ⟨q, hq, rfl⟩ := L.ground.endExtension A.P p (L.generic_subset p hp)
  have hqM := (L.ground.atomicMembership_mem_iff A.P A.R x y q).mpr hpM
  obtain ⟨ν, s, hνs, hs, r, hr, hrE⟩ := external_atomicMembership_witness A.order A.generic
    ⟨q, (L.generic_mem q).mp hp, hqM⟩
  exact ⟨L.ground r, (L.generic_mem r).mpr hr, L.ground ν, L.ground s,
    by rw [← L.ground.map_kpair, L.ground.mem_iff]; exact hνs,
    (L.generic_mem s).mpr hs, (L.ground.atomicEquality_mem_iff _ _ _ _ _).mp hrE⟩

theorem equality_decisions (N : V) :
    HasAtomicEqualityDecisions (L.ground A.P) (L.ground A.R) (L.ground N) L.genericSet := by
  intro σ hσ τ hτ
  obtain ⟨x, hx, rfl⟩ := L.ground.endExtension N σ hσ
  obtain ⟨y, hy, rfl⟩ := L.ground.endExtension N τ hτ
  obtain ⟨p, hp, hpD⟩ := A.generic.2 _ (atomicEqualityDecisions_dense A.order x y)
  refine ⟨L.ground p, (L.generic_mem p).mpr hp, ?_⟩
  rw [← L.ground.map_atomicEqualityDecisions, L.ground.mem_iff]
  exact hpD

end ForcingRealization
end ZFVP
