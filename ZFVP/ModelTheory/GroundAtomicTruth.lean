import ZFVP.ModelTheory.GroundAtomicSoundness
import ZFVP.SetTheory.AtomicSeparation

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingFilter_membership_of_pair_equal {P R G σ ν τ r s : V}
    (hR : IsForcingPreorder P R) (hG : IsForcingFilter P R G) (hrG : r ∈ G) (hsG : s ∈ G)
    (he : r ∈ atomicEquality P R σ ν) (hνs : ⟨ν, s⟩ₖ ∈ τ) :
    ∃ q ∈ G, q ∈ atomicMembership P R σ τ := by
  obtain ⟨q, hqG, hqr, hqs⟩ := hG.2.2.2 r hrG s hsG
  have hqP := hG.1 q hqG
  have hm := atomicMembership_mono hR (atomicMembership_of_pair hR (hG.1 s hsG) hνs) hqP hqs
  have he' := atomicEquality_mono hR he hqP hqr
  exact ⟨q, hqG, atomicMembership_subst_left hR (atomicEquality_symm P R σ ν ▸ he') hm⟩

theorem forcingFilter_negMembership_excludes {P R G σ τ p q : V}
    (hR : IsForcingPreorder P R) (hG : IsForcingFilter P R G) (hpG : p ∈ G) (hqG : q ∈ G)
    (hpN : p ∈ forcingNegation P R (atomicMembership P R σ τ))
    (hqM : q ∈ atomicMembership P R σ τ) : False := by
  obtain ⟨r, hrG, hrp, hrq⟩ := hG.2.2.2 p hpG q hqG
  exact ((mem_forcingNegation_iff _ _ _ _).mp hpN).2 r (hG.1 r hrG) hrp
    (atomicMembership_mono hR hqM (hG.1 r hrG) hrq)

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingNegation_val (P R A : SetDomain U) :
    (forcingNegation P R A).val = forcingNegation P.val R.val A.val := by
  unfold forcingNegation
  apply sep_val U
  intro p _
  apply forall_mem_val_iff U P
  intro q
  simp only [← kpair_mem_val_iff U]
  rfl

theorem atomicSeparation_val (P R σ τ : SetDomain U) :
    (atomicSeparation P R σ τ).val = atomicSeparation P.val R.val σ.val τ.val := by
  unfold atomicSeparation
  apply sep_val U
  intro p _
  apply exists_pair_mem_val_iff U σ
  intro υ s
  rw [← atomicMembership_val U, ← forcingNegation_val U]
  simp only [← kpair_mem_val_iff U]
  rfl

theorem atomicEqualityDecisions_val (P R σ τ : SetDomain U) :
    (atomicEqualityDecisions P R σ τ).val = atomicEqualityDecisions P.val R.val σ.val τ.val := by
  unfold atomicEqualityDecisions
  rw [union_val U, union_val U, atomicEquality_val U, atomicSeparation_val U, atomicSeparation_val U]

theorem ground_atomicEquality_truth (P R σ τ : SetDomain U) {G : V}
    (hR : IsForcingPreorder P.val R.val) (hG : IsGroundForcingGeneric U P.val R.val G)
    (heval : nameValue G σ.val = nameValue G τ.val) :
    ∃ p ∈ G, p ∈ atomicEquality P.val R.val σ.val τ.val := by
  have h := projectedRank_induction (nameClosure σ.val) (fun x : V ↦ x) (by definability)
    (fun x ↦ x ∈ U → ∀ y ∈ U, nameValue G x = nameValue G y →
      ∃ q ∈ G, q ∈ atomicEquality P.val R.val x y) (by definability) ?_
  · exact h σ.val (mem_nameClosure_self σ.val) σ.property τ.val τ.property heval
  intro x hx ih hxU y hyU hxy
  let x' : SetDomain U := ⟨x, hxU⟩
  let y' : SetDomain U := ⟨y, hyU⟩
  have hDU := (atomicEqualityDecisions P R x' y').property
  rw [atomicEqualityDecisions_val U] at hDU
  obtain ⟨p, hpG, hpD⟩ := hG.2 _ hDU (atomicEqualityDecisions_dense hR x y)
  rcases (mem_atomicEqualityDecisions_iff _ _ _ _ _).mp hpD with hpE | hpL | hpR
  · exact ⟨p, hpG, hpE⟩
  · obtain ⟨_, υ, s, hυs, hps, hpN⟩ := (mem_atomicSeparation_iff _ _ _ _ _).mp hpL
    have hsG := hG.1.2.2.1 p hpG s (forcingOrder_right_mem hR hps) hps
    have hvx : nameValue G υ ∈ nameValue G x := (mem_nameValue_iff _ _ _).mpr ⟨υ, s, hsG, hυs, rfl⟩
    rw [hxy] at hvx
    obtain ⟨ν, t, htG, hνt, hv⟩ := (mem_nameValue_iff _ _ _).mp hvx
    have hυU := (kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hυs hxU)).1
    have hνU := (kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hνt hyU)).1
    obtain ⟨r, hrG, hrE⟩ := ih υ (nameClosure_closed σ.val x hx υ (mem_domain_of_kpair_mem hυs))
      (rank_subname_lt hυs) hυU ν hνU hv
    obtain ⟨q, hqG, hqM⟩ := forcingFilter_membership_of_pair_equal hR hG.1 hrG htG hrE hνt
    exact False.elim (forcingFilter_negMembership_excludes hR hG.1 hpG hqG hpN hqM)
  · obtain ⟨_, ν, t, hνt, hpt, hpN⟩ := (mem_atomicSeparation_iff _ _ _ _ _).mp hpR
    have htG := hG.1.2.2.1 p hpG t (forcingOrder_right_mem hR hpt) hpt
    have hvy : nameValue G ν ∈ nameValue G y := (mem_nameValue_iff _ _ _).mpr ⟨ν, t, htG, hνt, rfl⟩
    rw [← hxy] at hvy
    obtain ⟨υ, s, hsG, hυs, hv⟩ := (mem_nameValue_iff _ _ _).mp hvy
    have hυU := (kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hυs hxU)).1
    have hνU := (kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hνt hyU)).1
    obtain ⟨r, hrG, hrE⟩ := ih υ (nameClosure_closed σ.val x hx υ (mem_domain_of_kpair_mem hυs))
      (rank_subname_lt hυs) hυU ν hνU hv.symm
    obtain ⟨q, hqG, hqM⟩ := forcingFilter_membership_of_pair_equal hR hG.1 hrG hsG
      (atomicEquality_symm P.val R.val υ ν ▸ hrE) hυs
    exact False.elim (forcingFilter_negMembership_excludes hR hG.1 hpG hqG hpN hqM)

theorem ground_atomicMembership_truth (P R σ τ : SetDomain U) {G : V}
    (hR : IsForcingPreorder P.val R.val) (hG : IsGroundForcingGeneric U P.val R.val G)
    (hm : nameValue G σ.val ∈ nameValue G τ.val) :
    ∃ p ∈ G, p ∈ atomicMembership P.val R.val σ.val τ.val := by
  obtain ⟨ν, s, hsG, hνs, he⟩ := (mem_nameValue_iff _ _ _).mp hm
  have hνU := (kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hνs τ.property)).1
  let ν' : SetDomain U := ⟨ν, hνU⟩
  obtain ⟨r, hrG, hrE⟩ := ground_atomicEquality_truth U P R σ ν' hR hG he
  exact forcingFilter_membership_of_pair_equal hR hG.1 hrG hsG hrE hνs

theorem ground_atomicEquality_iff (P R σ τ : SetDomain U) {G : V}
    (hR : IsForcingPreorder P.val R.val) (hG : IsGroundForcingGeneric U P.val R.val G) :
    nameValue G σ.val = nameValue G τ.val ↔ ∃ p ∈ G, p ∈ atomicEquality P.val R.val σ.val τ.val :=
  ⟨ground_atomicEquality_truth U P R σ τ hR hG,
    fun ⟨_, hpG, hp⟩ ↦ ground_atomicEquality_sound U P R σ τ hR hG hpG hp⟩

theorem ground_atomicMembership_iff (P R σ τ : SetDomain U) {G : V}
    (hR : IsForcingPreorder P.val R.val) (hG : IsGroundForcingGeneric U P.val R.val G) :
    nameValue G σ.val ∈ nameValue G τ.val ↔ ∃ p ∈ G, p ∈ atomicMembership P.val R.val σ.val τ.val :=
  ⟨ground_atomicMembership_truth U P R σ τ hR hG,
    fun ⟨_, hpG, hp⟩ ↦ ground_atomicMembership_sound U P R σ τ hR hG hpG hp⟩

end TransitiveZF
end ZFVP
