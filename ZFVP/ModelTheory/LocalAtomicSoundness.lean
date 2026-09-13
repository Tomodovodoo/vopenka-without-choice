import ZFVP.ModelTheory.GroundAtomicTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Local atomic witnesses needed to interpret a set of names. -/
def HasAtomicMembershipWitnesses (P R N G : V) : Prop :=
  ∀ σ ∈ N, ∀ τ ∈ N, ∀ p ∈ G, p ∈ atomicMembership P R σ τ →
    ∃ r ∈ G, ∃ ν s, ⟨ν, s⟩ₖ ∈ τ ∧ s ∈ G ∧ r ∈ atomicEquality P R σ ν

theorem local_atomicEquality_sound {P R N G σ τ p : V}
    (hR : IsForcingPreorder P R) (hN : IsSubnameClosed N) (hG : IsForcingFilter P R G)
    (hW : HasAtomicMembershipWitnesses P R N G)
    (hσ : σ ∈ N) (hτ : τ ∈ N) (hpG : p ∈ G) (hp : p ∈ atomicEquality P R σ τ) :
    nameValue G σ = nameValue G τ := by
  have h := projectedRank_induction (nameClosure σ) (fun x : V ↦ x) (by definability)
    (fun x ↦ x ∈ N → ∀ y ∈ N, ∀ q ∈ G, q ∈ atomicEquality P R x y →
      nameValue G x = nameValue G y) (by definability) ?_
  · exact h σ (mem_nameClosure_self σ) hσ τ hτ p hpG hp
  intro x hx ih hxN y hyN q hqG hqE
  apply SetTheory.mem_ext_iff.mpr
  intro z
  constructor
  · intro hz
    obtain ⟨υ, s, hsG, hυs, rfl⟩ := (mem_nameValue_iff _ _ _).mp hz
    have hυN := hN x hxN υ (mem_domain_of_kpair_mem hυs)
    obtain ⟨r, hrG, hrq, hrs⟩ := hG.2.2.2 q hqG s hsG
    have hrP := hG.1 r hrG
    have hrE := atomicEquality_mono hR hqE hrP hrq
    have hrM := ((atomicEquality_iff_membership _ _ _ _ _ hR).mp hrE).2.1
      υ s hυs r hrP (hR.2.1 r hrP) hrs
    obtain ⟨v, hvG, ν, t, hνt, htG, he⟩ := hW υ hυN y hyN r hrG hrM
    have hνN := hN y hyN ν (mem_domain_of_kpair_mem hνt)
    have hv := ih υ (nameClosure_closed σ x hx υ (mem_domain_of_kpair_mem hυs))
      (rank_subname_lt hυs) hυN ν hνN v hvG he
    exact (mem_nameValue_iff _ _ _).mpr ⟨ν, t, htG, hνt, hv⟩
  · intro hz
    obtain ⟨ν, t, htG, hνt, rfl⟩ := (mem_nameValue_iff _ _ _).mp hz
    have hνN := hN y hyN ν (mem_domain_of_kpair_mem hνt)
    obtain ⟨r, hrG, hrq, hrt⟩ := hG.2.2.2 q hqG t htG
    have hrP := hG.1 r hrG
    have hrE := atomicEquality_mono hR hqE hrP hrq
    have hrM := ((atomicEquality_iff_membership _ _ _ _ _ hR).mp hrE).2.2
      ν t hνt r hrP (hR.2.1 r hrP) hrt
    obtain ⟨v, hvG, υ, s, hυs, hsG, he⟩ := hW ν hνN x hxN r hrG hrM
    have hυN := hN x hxN υ (mem_domain_of_kpair_mem hυs)
    have hv := ih υ (nameClosure_closed σ x hx υ (mem_domain_of_kpair_mem hυs))
      (rank_subname_lt hυs) hυN ν hνN v hvG (atomicEquality_symm P R ν υ ▸ he)
    exact (mem_nameValue_iff _ _ _).mpr ⟨υ, s, hsG, hυs, hv.symm⟩

theorem local_atomicMembership_sound {P R N G σ τ p : V}
    (hR : IsForcingPreorder P R) (hN : IsSubnameClosed N) (hG : IsForcingFilter P R G)
    (hW : HasAtomicMembershipWitnesses P R N G)
    (hσ : σ ∈ N) (hτ : τ ∈ N) (hpG : p ∈ G) (hp : p ∈ atomicMembership P R σ τ) :
    nameValue G σ ∈ nameValue G τ := by
  obtain ⟨r, hrG, ν, s, hνs, hsG, he⟩ := hW σ hσ τ hτ p hpG hp
  have hνN := hN τ hτ ν (mem_domain_of_kpair_mem hνs)
  exact (mem_nameValue_iff _ _ _).mpr ⟨ν, s, hsG, hνs,
    local_atomicEquality_sound hR hN hG hW hσ hνN hrG he⟩

end ZFVP
