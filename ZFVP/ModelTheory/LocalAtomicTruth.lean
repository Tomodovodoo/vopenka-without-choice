import ZFVP.ModelTheory.LocalAtomicSoundness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The filter meets each equality decision set for the named local domain. -/
def HasAtomicEqualityDecisions (P R N G : V) : Prop :=
  ∀ σ ∈ N, ∀ τ ∈ N, ∃ p ∈ G, p ∈ atomicEqualityDecisions P R σ τ

theorem local_atomicEquality_truth {P R N G σ τ : V}
    (hR : IsForcingPreorder P R) (hN : IsSubnameClosed N) (hG : IsForcingFilter P R G)
    (hD : HasAtomicEqualityDecisions P R N G) (hσ : σ ∈ N) (hτ : τ ∈ N)
    (heval : nameValue G σ = nameValue G τ) : ∃ p ∈ G, p ∈ atomicEquality P R σ τ := by
  have h := projectedRank_induction (nameClosure σ) (fun x : V ↦ x) (by definability)
    (fun x ↦ x ∈ N → ∀ y ∈ N, nameValue G x = nameValue G y →
      ∃ q ∈ G, q ∈ atomicEquality P R x y) (by definability) ?_
  · exact h σ (mem_nameClosure_self σ) hσ τ hτ heval
  intro x hx ih hxN y hyN hxy
  obtain ⟨p, hpG, hpD⟩ := hD x hxN y hyN
  rcases (mem_atomicEqualityDecisions_iff _ _ _ _ _).mp hpD with hpE | hpL | hpR
  · exact ⟨p, hpG, hpE⟩
  · obtain ⟨_, υ, s, hυs, hps, hpN⟩ := (mem_atomicSeparation_iff _ _ _ _ _).mp hpL
    have hsG := hG.2.2.1 p hpG s (forcingOrder_right_mem hR hps) hps
    have hvx : nameValue G υ ∈ nameValue G x := (mem_nameValue_iff _ _ _).mpr ⟨υ, s, hsG, hυs, rfl⟩
    rw [hxy] at hvx
    obtain ⟨ν, t, htG, hνt, hv⟩ := (mem_nameValue_iff _ _ _).mp hvx
    have hυN := hN x hxN υ (mem_domain_of_kpair_mem hυs)
    have hνN := hN y hyN ν (mem_domain_of_kpair_mem hνt)
    obtain ⟨r, hrG, hrE⟩ := ih υ (nameClosure_closed σ x hx υ (mem_domain_of_kpair_mem hυs))
      (rank_subname_lt hυs) hυN ν hνN hv
    obtain ⟨q, hqG, hqM⟩ := forcingFilter_membership_of_pair_equal hR hG hrG htG hrE hνt
    exact False.elim (forcingFilter_negMembership_excludes hR hG hpG hqG hpN hqM)
  · obtain ⟨_, ν, t, hνt, hpt, hpN⟩ := (mem_atomicSeparation_iff _ _ _ _ _).mp hpR
    have htG := hG.2.2.1 p hpG t (forcingOrder_right_mem hR hpt) hpt
    have hvy : nameValue G ν ∈ nameValue G y := (mem_nameValue_iff _ _ _).mpr ⟨ν, t, htG, hνt, rfl⟩
    rw [← hxy] at hvy
    obtain ⟨υ, s, hsG, hυs, hv⟩ := (mem_nameValue_iff _ _ _).mp hvy
    have hυN := hN x hxN υ (mem_domain_of_kpair_mem hυs)
    have hνN := hN y hyN ν (mem_domain_of_kpair_mem hνt)
    obtain ⟨r, hrG, hrE⟩ := ih υ (nameClosure_closed σ x hx υ (mem_domain_of_kpair_mem hυs))
      (rank_subname_lt hυs) hυN ν hνN hv.symm
    obtain ⟨q, hqG, hqM⟩ := forcingFilter_membership_of_pair_equal hR hG hrG hsG
      (atomicEquality_symm P R υ ν ▸ hrE) hυs
    exact False.elim (forcingFilter_negMembership_excludes hR hG hpG hqG hpN hqM)

theorem local_atomicMembership_truth {P R N G σ τ : V}
    (hR : IsForcingPreorder P R) (hN : IsSubnameClosed N) (hG : IsForcingFilter P R G)
    (hD : HasAtomicEqualityDecisions P R N G) (hσ : σ ∈ N) (hτ : τ ∈ N)
    (hm : nameValue G σ ∈ nameValue G τ) : ∃ p ∈ G, p ∈ atomicMembership P R σ τ := by
  obtain ⟨ν, s, hsG, hνs, he⟩ := (mem_nameValue_iff _ _ _).mp hm
  have hνN := hN τ hτ ν (mem_domain_of_kpair_mem hνs)
  obtain ⟨r, hrG, hrE⟩ := local_atomicEquality_truth hR hN hG hD hσ hνN he
  exact forcingFilter_membership_of_pair_equal hR hG hrG hsG hrE hνs

theorem local_atomicEquality_iff {P R N G σ τ : V}
    (hR : IsForcingPreorder P R) (hN : IsSubnameClosed N) (hG : IsForcingFilter P R G)
    (hW : HasAtomicMembershipWitnesses P R N G) (hD : HasAtomicEqualityDecisions P R N G)
    (hσ : σ ∈ N) (hτ : τ ∈ N) :
    nameValue G σ = nameValue G τ ↔ ∃ p ∈ G, p ∈ atomicEquality P R σ τ :=
  ⟨local_atomicEquality_truth hR hN hG hD hσ hτ,
    fun ⟨_, hpG, hp⟩ ↦ local_atomicEquality_sound hR hN hG hW hσ hτ hpG hp⟩

theorem local_atomicMembership_iff {P R N G σ τ : V}
    (hR : IsForcingPreorder P R) (hN : IsSubnameClosed N) (hG : IsForcingFilter P R G)
    (hW : HasAtomicMembershipWitnesses P R N G) (hD : HasAtomicEqualityDecisions P R N G)
    (hσ : σ ∈ N) (hτ : τ ∈ N) :
    nameValue G σ ∈ nameValue G τ ↔ ∃ p ∈ G, p ∈ atomicMembership P R σ τ :=
  ⟨local_atomicMembership_truth hR hN hG hD hσ hτ,
    fun ⟨_, hpG, hp⟩ ↦ local_atomicMembership_sound hR hN hG hW hσ hτ hpG hp⟩

end ZFVP
