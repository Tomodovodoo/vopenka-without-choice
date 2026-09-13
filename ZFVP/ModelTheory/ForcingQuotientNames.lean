import ZFVP.ModelTheory.ForcingQuotientTruth
import ZFVP.SetTheory.AtomicWitnesses
import ZFVP.SetTheory.AtomicSeparation

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem external_atomicMembership_witness {P R σ τ : V} {G : Set V}
    (hR : IsForcingPreorder P R) (hG : IsExternalForcingGeneric P R G)
    (hm : GenericMeets G (atomicMembership P R σ τ)) :
    ∃ ν s, ⟨ν, s⟩ₖ ∈ τ ∧ s ∈ G ∧ GenericMeets G (atomicEquality P R σ ν) := by
  obtain ⟨p, hpG, hpM⟩ := hm
  obtain ⟨r, hrG, hrW⟩ := externalForcingGeneric_meets_denseBelow hR hG hpG
    (atomicMembershipWitnesses_dense hpM)
  obtain ⟨_, ν, s, hνs, hrs, hrE⟩ := (mem_atomicMembershipWitnesses_iff _ _ _ _ _).mp hrW
  exact ⟨ν, s, hνs, hG.1.2.2.1 r hrG s (forcingOrder_right_mem hR hrs) hrs, r, hrG, hrE⟩

theorem forcingQuotientMk_mem_subname_iff (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (σ τ : ForcingName P) :
    forcingQuotientMk P R G hR hG.1 σ ∈ forcingQuotientMk P R G hR hG.1 τ ↔
      ∃ ν : ForcingName P, ∃ s ∈ G, ⟨ν.val, s⟩ₖ ∈ τ.val ∧
        forcingQuotientMk P R G hR hG.1 σ = forcingQuotientMk P R G hR hG.1 ν := by
  rw [forcingQuotientMk_mem_iff]
  constructor
  · intro hm
    obtain ⟨ν, s, hνs, hsG, he⟩ := external_atomicMembership_witness hR hG hm
    let ν' : ForcingName P := ⟨ν, forcingName_subname τ.property hνs⟩
    exact ⟨ν', s, hsG, hνs, (forcingQuotientMk_eq_iff _ _ _ _ _ _ _).mpr he⟩
  · rintro ⟨ν, s, hsG, hνs, he⟩
    have hE := (forcingQuotientMk_eq_iff _ _ _ _ _ _ _).mp he
    have hm : GenericMeets G (atomicMembership P R ν.val τ.val) :=
      ⟨s, hsG, atomicMembership_of_pair hR (hG.1.1 s hsG) hνs⟩
    exact genericMeets_membership_subst_left hR hG.1 (atomicEquality_symm P R σ.val ν.val ▸ hE) hm

theorem forcingQuotient_extensionality (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (x y : ForcingQuotient P R G hR hG.1)
    (he : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  unfold IsExternalForcingGeneric at hG
  obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 x
  obtain ⟨τ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 y
  obtain ⟨p, hpG, hpD⟩ := hG.2 _ (atomicEqualityDecisions_dense hR σ.val τ.val)
  rcases (mem_atomicEqualityDecisions_iff _ _ _ _ _).mp hpD with hpE | hpL | hpR
  · exact (forcingQuotientMk_eq_iff _ _ _ _ _ _ _).mpr ⟨p, hpG, hpE⟩
  · obtain ⟨_, υ, s, hυs, hps, hpN⟩ := (mem_atomicSeparation_iff _ _ _ _ _).mp hpL
    have hsG := hG.1.2.2.1 p hpG s (forcingOrder_right_mem hR hps) hps
    let υ' : ForcingName P := ⟨υ, forcingName_subname σ.property hυs⟩
    have hleft : forcingQuotientMk P R G hR hG.1 υ' ∈ forcingQuotientMk P R G hR hG.1 σ :=
      (forcingQuotientMk_mem_iff _ _ _ _ _ _ _).mpr
        ⟨s, hsG, atomicMembership_of_pair hR (hG.1.1 s hsG) hυs⟩
    have hm := (forcingQuotientMk_mem_iff _ _ _ _ _ _ _).mp ((he _).mp hleft)
    have hn : GenericMeets G (forcingNegation P R (atomicMembership P R υ τ.val)) := ⟨p, hpG, hpN⟩
    exact False.elim ((genericMeets_negation hR hG (atomicMembership_subset _ _ _ _)
      (atomicMembership_regular hR υ τ.val).2.1).mp hn hm)
  · obtain ⟨_, υ, s, hυs, hps, hpN⟩ := (mem_atomicSeparation_iff _ _ _ _ _).mp hpR
    have hsG := hG.1.2.2.1 p hpG s (forcingOrder_right_mem hR hps) hps
    let υ' : ForcingName P := ⟨υ, forcingName_subname τ.property hυs⟩
    have hright : forcingQuotientMk P R G hR hG.1 υ' ∈ forcingQuotientMk P R G hR hG.1 τ :=
      (forcingQuotientMk_mem_iff _ _ _ _ _ _ _).mpr
        ⟨s, hsG, atomicMembership_of_pair hR (hG.1.1 s hsG) hυs⟩
    have hm := (forcingQuotientMk_mem_iff _ _ _ _ _ _ _).mp ((he _).mpr hright)
    have hn : GenericMeets G (forcingNegation P R (atomicMembership P R υ σ.val)) := ⟨p, hpG, hpN⟩
    exact False.elim ((genericMeets_negation hR hG (atomicMembership_subset _ _ _ _)
      (atomicMembership_regular hR υ σ.val).2.1).mp hn hm)

theorem forcingQuotient_empty (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) :
    ∀ x : ForcingQuotient P R G hR hG,
      x ∉ forcingQuotientMk P R G hR hG ⟨∅, empty_forcingName P⟩ := by
  intro x hx
  obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG x
  obtain ⟨p, _, hp⟩ := (forcingQuotientMk_mem_iff _ _ _ _ _ _ _).mp hx
  rw [atomicMembership_empty hR] at hp
  exact not_mem_empty hp

end ZFVP
