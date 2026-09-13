import ZFVP.ModelTheory.SchmerlInternalClosedDeduction

/-! Full internal deduction by definable rank induction, including every rule
and internal countable branching. The discharged assumption is a sentence. -/
namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsInternalProof.deduction {L Γ F D χ : V}
    (h : IsInternalProof L (SetTheory.insert ⟨(0 : V), χ⟩ₖ Γ) F D)
    (hFc : IsInternallyCountable F) (hAC : InternalChoice V) :
    ∀ d ∈ D, ∃ c, IsInternalDerivationCode L Γ
      (kpair.π₁ (kpair.π₁ d)) (impCode χ (kpair.π₂ (kpair.π₁ d))) c := by
  have hΓF : Γ ⊆ F := fun t ht ↦ h.2.1 t (mem_insert.mpr (Or.inr ht))
  have hχ : ⟨(0 : V), χ⟩ₖ ∈ F := h.2.1 _ (mem_insert.mpr (Or.inl rfl))
  apply projectedRank_induction D id (by definability)
    (fun d ↦ ∃ c, IsInternalDerivationCode L Γ
      (kpair.π₁ (kpair.π₁ d)) (impCode χ (kpair.π₂ (kpair.π₁ d))) c) (by definability)
  intro d hd ih
  have hleaf {n φ d : V} (ha : IsInternalProofNode L ∅ F ∅ d)
      (hl : kpair.π₁ d = ⟨n, φ⟩ₖ) :
      ∃ c, IsInternalDerivationCode L Γ n (impCode χ φ) c := by
    have ht : ⟨n, φ⟩ₖ ∈ F := by simpa only [hl] using ha.label_mem
    have hn := (h.1.node ht).1
    obtain ⟨c, hc⟩ := internalDerivation_closed_node h.1 hFc h.1 hFc hΓF ha hl
    exact hc.weaken_imp (sentenceLiftFragment_valid h.1 hn)
      (sentenceLiftFragment_countable hFc) (sentence_mem_lift h.1 hn hχ)
  rcases h.2.2 d hd with hc | ⟨n, φ, hφ, rfl, ha⟩ | ⟨n, φ, hφ, rfl, ha⟩ |
    ⟨n, φ, hφ, rfl, ha⟩ | hs | ⟨n, φ, hφ, rfl, ha⟩ | ⟨n, φ, hφ, rfl, ha⟩ |
    ⟨n, φ, hφ, rfl, ha⟩ | ⟨n, φ, hφ, rfl, ha⟩
  · rcases hc with hb | ⟨n, φ, hφ, rfl, ha⟩ | ⟨n, φ, p, hφ, hp, rfl, hl⟩
    · obtain ⟨n, φ, hφ, hb⟩ := hb
      rcases hb with ⟨rfl, hφΓ⟩ | ⟨rfl, ha⟩ | ⟨p, hp, q, hq, ψ, rfl, hlp, hlq⟩ |
        ⟨f, g, hf, hfd, hg, hgd, rfl, rfl, hchildren⟩
      · simp only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair]
        rcases mem_insert.mp hφΓ with he | hφΓ
        · obtain ⟨rfl, rfl⟩ := kpair_inj he
          exact internalDerivation_identity h.1 hFc hΓF hφ
        · obtain ⟨c, hc⟩ := internalDerivation_hypothesis h.1 hFc hΓF hφΓ
          exact hc.weaken_imp (sentenceLiftFragment_valid h.1 (h.1.node hφ).1)
            (sentenceLiftFragment_countable hFc) (sentence_mem_lift h.1 (h.1.node hφ).1 hχ)
      · exact hleaf (Or.inl (Or.inl ⟨n, φ, hφ, Or.inr (Or.inl ⟨rfl, ha⟩)⟩)) (by simp)
      · obtain ⟨c, hc⟩ := ih p hp (booleanProofNode_premise_rank (rank_kpair_left_lt p q))
        obtain ⟨e, he⟩ := ih q hq (booleanProofNode_premise_rank (rank_kpair_right_lt p q))
        simp only [hlp, kpair.π₁_kpair, kpair.π₂_kpair] at hc
        simp only [hlq, kpair.π₁_kpair, kpair.π₂_kpair] at he
        simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using hc.imp_mp he
      · simp only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair]
        apply internalDerivation_imp_conjunction hAC hf hfd
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
        hc.imp_generalize_closed h.1 hFc hΓF hχ (h.1.node hφ).1
  · exact hleaf (Or.inr (Or.inl ⟨n, φ, hφ, rfl, ha⟩)) (by simp)
  · exact hleaf (Or.inr (Or.inr (Or.inl ⟨n, φ, hφ, rfl, ha⟩))) (by simp)
  · exact hleaf (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, φ, hφ, rfl, ha⟩)))) (by simp)
  · obtain ⟨H, s, φ, p, hH, hs, hφ, ht, hp, hl, rfl⟩ := hs
    have hr : rank p ∈ rank ⟨H, ⟨s, p⟩ₖ⟩ₖ :=
      IsOrdinal.toIsTransitive.mem_trans (rank_kpair_right_lt s p) (rank_kpair_right_lt H ⟨s, p⟩ₖ)
    obtain ⟨c, hc⟩ := ih p hp (booleanProofNode_premise_rank hr)
    simp only [hl, kpair.π₁_kpair, kpair.π₂_kpair] at hc
    simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using
      hc.imp_substitute_closed h.1 hχ hH hs hφ
  · exact hleaf (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, φ, hφ, rfl, ha⟩)))))) (by simp)
  · exact hleaf (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, φ, hφ, rfl, ha⟩))))))) (by simp)
  · exact hleaf (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, φ, hφ, rfl, ha⟩)))))))) (by simp)
  · exact hleaf (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, φ, hφ, rfl, ha⟩)))))))) (by simp)

theorem IsInternalDerivationCode.deduction {L Γ n χ φ c : V}
    (h : IsInternalDerivationCode L (SetTheory.insert ⟨(0 : V), χ⟩ₖ Γ) n φ c)
    (hAC : InternalChoice V) :
    ∃ z, IsInternalDerivationCode L Γ n (impCode χ φ) z := by
  obtain ⟨F, D, d, _, hFc, _, hP, hd, hl⟩ := h
  simpa only [hl, kpair.π₁_kpair, kpair.π₂_kpair] using hP.deduction hFc hAC d hd

end ZFVP.Infinitary.Internal
