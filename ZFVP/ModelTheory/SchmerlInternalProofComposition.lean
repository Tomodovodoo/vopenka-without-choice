import ZFVP.ModelTheory.SchmerlInternalCountableProofUnion
import ZFVP.ModelTheory.SchmerlInternalSubstitutionIdentities

/-! Syntactic composition of internal proofs. Replaced hypotheses may have
arbitrary internal contexts; no model or satisfiability premise is used. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalDerivation_closed_node {L Δ F J n φ d : V}
    (hF : IsFragment L F) (hFc : IsInternallyCountable F)
    (hJ : IsFragment L J) (hJc : IsInternallyCountable J) (hΔ : Δ ⊆ J)
    (hd : IsInternalProofNode L ∅ F ∅ d) (hl : kpair.π₁ d = ⟨n, φ⟩ₖ) :
    ∃ c, IsInternalDerivationCode L Δ n φ c := by
  apply internalDerivation_of_axiom (hF.union hJ) (internallyCountable_union hFc hJc)
    (fun x hx ↦ mem_union_iff.mpr (Or.inr (hΔ x hx))) _ hl
  exact hd.mono (by simp) (fun _ hx ↦ mem_union_iff.mpr (Or.inl hx)) (fun _ hx ↦ hx)

theorem IsInternalDerivationCode.substitute_in {L Γ H F s φ c : V}
    (h : IsInternalDerivationCode L Γ (stateSource s) φ c)
    (hH : IsFragment L H) (hs : IsSubstitutionState L ∅ ∅ s)
    (hφ : ⟨stateSource s, φ⟩ₖ ∈ H) (hF : IsFragment L F)
    (hFc : IsInternallyCountable F) (ht : ⟨stateTarget s, substituteCode L H s φ⟩ₖ ∈ F) :
    ∃ z, IsInternalDerivationCode L Γ (stateTarget s) (substituteCode L H s φ) z := by
  obtain ⟨G, D, p, rfl, hGc, hDc, hP, hp, hl⟩ := h
  let d := booleanProofNode (stateTarget s) (substituteCode L H s φ) 9 ⟨H, ⟨s, p⟩ₖ⟩ₖ
  have hGF : G ⊆ G ∪ F := fun _ hx ↦ mem_union_iff.mpr (Or.inl hx)
  have hP' := hP.weaken (hP.1.union hF) (fun _ hx ↦ hx)
    (fun x hx ↦ hGF x (hP.2.1 x hx)) hGF
  have hnode : IsInternalProofNode L Γ (G ∪ F) (insert d D) d := by
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨H, s, φ, p, hH, hs, hφ,
      mem_union_iff.mpr (Or.inr ht), mem_insert.mpr (Or.inr hp), hl, rfl⟩))))
  exact ⟨⟨G ∪ F, ⟨insert d D, d⟩ₖ⟩ₖ, G ∪ F, insert d D, d, rfl,
    internallyCountable_union hGc hFc, internallyCountable_insert hDc d,
    hP'.insert hnode, by simp, booleanProofNode_label _ _ _ _⟩

/-- Substitution can be specified in any valid fragment containing the source.
Its countability is unnecessary: the existing proof supplies a countable one. -/
theorem IsInternalDerivationCode.substitute_from {L Γ H s φ c : V}
    (h : IsInternalDerivationCode L Γ (stateSource s) φ c)
    (hH : IsFragment L H) (hs : IsSubstitutionState L ∅ ∅ s)
    (hφ : ⟨stateSource s, φ⟩ₖ ∈ H) :
    ∃ z, IsInternalDerivationCode L Γ (stateTarget s) (substituteCode L H s φ) z := by
  obtain ⟨F, D, d, he, hFc, hDc, hP, hd, hl⟩ := h
  have hφF : ⟨stateSource s, φ⟩ₖ ∈ F := by
    simpa only [hl] using (hP.2.2 d hd).label_mem
  have hcode : kpair.π₁ c = F := by simp only [he, kpair.π₁_kpair]
  obtain ⟨z, hz⟩ := (show IsInternalDerivationCode L Γ (stateSource s) φ c from
    ⟨F, D, d, he, hFc, hDc, hP, hd, hl⟩).substitute hs
  rw [hcode, substituteCode_fragment_eq hP.1 hH hφF hφ] at hz
  exact ⟨z, hz⟩

theorem IsInternalProof.cut {L Γ Δ F J D : V} (h : IsInternalProof L Γ F D)
    (hFc : IsInternallyCountable F) (hJ : IsFragment L J)
    (hJc : IsInternallyCountable J) (hΔ : Δ ⊆ J) (hAC : InternalChoice V)
    (hΓ : ∀ n φ, ⟨n, φ⟩ₖ ∈ Γ → ∃ c, IsInternalDerivationCode L Δ n φ c) :
    ∀ d ∈ D, ∃ c, IsInternalDerivationCode L Δ
      (kpair.π₁ (kpair.π₁ d)) (kpair.π₂ (kpair.π₁ d)) c := by
  apply projectedRank_induction D id (by definability)
    (fun d ↦ ∃ c, IsInternalDerivationCode L Δ
      (kpair.π₁ (kpair.π₁ d)) (kpair.π₂ (kpair.π₁ d)) c) (by definability)
  intro d hd ih
  have hleaf {n φ d : V} (ha : IsInternalProofNode L ∅ F ∅ d)
      (hl : kpair.π₁ d = ⟨n, φ⟩ₖ) := internalDerivation_closed_node h.1 hFc hJ hJc hΔ ha hl
  rcases h.2.2 d hd with hc | ⟨n, φ, hφ, rfl, ha⟩ | ⟨n, φ, hφ, rfl, ha⟩ |
    ⟨n, φ, hφ, rfl, ha⟩ | hs | ⟨n, φ, hφ, rfl, ha⟩ | ⟨n, φ, hφ, rfl, ha⟩ |
    ⟨n, φ, hφ, rfl, ha⟩ | ⟨n, φ, hφ, rfl, ha⟩
  · rcases hc with hb | ⟨n, φ, hφ, rfl, ha⟩ | ⟨n, φ, p, hφ, hp, rfl, hl⟩
    · obtain ⟨n, φ, hφ, hb⟩ := hb
      rcases hb with ⟨rfl, hφΓ⟩ | ⟨rfl, ha⟩ | ⟨p, hp, q, hq, ψ, rfl, hlp, hlq⟩ |
        ⟨f, g, hf, hfd, hg, hgd, rfl, rfl, hchildren⟩
      · simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using hΓ n φ hφΓ
      · exact hleaf (Or.inl (Or.inl ⟨n, φ, hφ, Or.inr (Or.inl ⟨rfl, ha⟩)⟩)) (by simp)
      · obtain ⟨c, hc⟩ := ih p hp (booleanProofNode_premise_rank (rank_kpair_left_lt p q))
        obtain ⟨e, he⟩ := ih q hq (booleanProofNode_premise_rank (rank_kpair_right_lt p q))
        simp only [hlp, kpair.π₁_kpair, kpair.π₂_kpair] at hc
        simp only [hlq, kpair.π₁_kpair, kpair.π₂_kpair] at he
        simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using hc.mp he
      · simp only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair]
        apply internalDerivation_conjunction hAC hf hfd
        intro i hi
        let := hg
        have hr : rank (g ‘ i) ∈ rank g := rank_lt_of_mem_range
          (mem_range_of_kpair_mem (kpair_value_mem (hgd.symm ▸ hi)))
        simpa only [(hchildren i hi).2, kpair.π₁_kpair, kpair.π₂_kpair] using
          ih (g ‘ i) (hchildren i hi).1 (booleanProofNode_premise_rank hr)
    · exact hleaf (Or.inl (Or.inr (Or.inl ⟨n, φ, hφ, rfl, ha⟩))) (by simp)
    · have hr : rank p ∈ rank (booleanProofNode n (allCode φ) 5 p) :=
        IsOrdinal.toIsTransitive.mem_trans (rank_kpair_right_lt (5 : V) p)
          (rank_kpair_right_lt ⟨n, allCode φ⟩ₖ ⟨(5 : V), p⟩ₖ)
      obtain ⟨c, hc⟩ := ih p hp hr
      simp only [hl, kpair.π₁_kpair, kpair.π₂_kpair] at hc
      simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using
        hc.generalization h.1 hFc hφ
  · exact hleaf (Or.inr (Or.inl ⟨n, φ, hφ, rfl, ha⟩)) (by simp)
  · exact hleaf (Or.inr (Or.inr (Or.inl ⟨n, φ, hφ, rfl, ha⟩))) (by simp)
  · exact hleaf (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, φ, hφ, rfl, ha⟩)))) (by simp)
  · obtain ⟨H, s, φ, p, hH, hs, hφ, ht, hp, hl, rfl⟩ := hs
    have hr : rank p ∈ rank ⟨H, ⟨s, p⟩ₖ⟩ₖ :=
      IsOrdinal.toIsTransitive.mem_trans (rank_kpair_right_lt s p) (rank_kpair_right_lt H ⟨s, p⟩ₖ)
    obtain ⟨c, hc⟩ := ih p hp (booleanProofNode_premise_rank hr)
    simp only [hl, kpair.π₁_kpair, kpair.π₂_kpair] at hc
    simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using
      hc.substitute_in hH hs hφ h.1 hFc ht
  · exact hleaf (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, φ, hφ, rfl, ha⟩)))))) (by simp)
  · exact hleaf (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, φ, hφ, rfl, ha⟩))))))) (by simp)
  · exact hleaf (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, φ, hφ, rfl, ha⟩)))))))) (by simp)
  · exact hleaf (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, φ, hφ, rfl, ha⟩)))))))) (by simp)

theorem IsInternalDerivationCode.cut {L Γ Δ J n φ c : V}
    (h : IsInternalDerivationCode L Γ n φ c) (hJ : IsFragment L J)
    (hJc : IsInternallyCountable J) (hΔ : Δ ⊆ J) (hAC : InternalChoice V)
    (hΓ : ∀ k ψ, ⟨k, ψ⟩ₖ ∈ Γ → ∃ e, IsInternalDerivationCode L Δ k ψ e) :
    ∃ z, IsInternalDerivationCode L Δ n φ z := by
  obtain ⟨F, D, d, _, hFc, _, hP, hd, hl⟩ := h
  simpa only [hl, kpair.π₁_kpair, kpair.π₂_kpair] using hP.cut hFc hJ hJc hΔ hAC hΓ d hd

end ZFVP.Infinitary.Internal
