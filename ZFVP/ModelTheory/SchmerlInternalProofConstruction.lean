import ZFVP.ModelTheory.SchmerlInternalFragmentExtension

/-! Constructed countable derivation codes for axioms, modus ponens and universal
generalization. Each result supplies the proof set and its terminal node. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsInternalProof.insert {L Γ F D d : V} (h : IsInternalProof L Γ F D)
    (hd : IsInternalProofNode L Γ F (insert d D) d) : IsInternalProof L Γ F (insert d D) := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro p hp
  rcases mem_insert.mp hp with rfl | hp
  · exact hd
  · exact (h.2.2 p hp).mono (fun _ hx ↦ hx) (fun _ hx ↦ hx)
      (fun _ hx ↦ mem_insert.mpr (Or.inr hx))

theorem internalDerivation_of_axiom {L Γ F n φ d : V} (hF : IsFragment L F)
    (hc : IsInternallyCountable F) (hΓ : Γ ⊆ F)
    (hd : IsInternalProofNode L Γ F ∅ d) (hl : kpair.π₁ d = ⟨n, φ⟩ₖ) :
    ∃ c, IsInternalDerivationCode L Γ n φ c := by
  refine ⟨⟨F, ⟨{d}, d⟩ₖ⟩ₖ, F, {d}, d, rfl, hc, internallyCountable_singleton d,
    ⟨hF, hΓ, ?_⟩, by simp, hl⟩
  intro p hp
  have hp' : p = d := by simpa using hp
  subst p
  exact hd.mono (fun _ hx ↦ hx) (fun _ hx ↦ hx) (by simp)

theorem IsInternalDerivationCode.mp {L Γ n φ ψ c e : V}
    (h : IsInternalDerivationCode L Γ n (impCode φ ψ) c)
    (k : IsInternalDerivationCode L Γ n φ e) : ∃ z, IsInternalDerivationCode L Γ n ψ z := by
  obtain ⟨F, D, p, rfl, hFc, hDc, hP, hp, hlp⟩ := h
  obtain ⟨G, E, q, rfl, hGc, hEc, hQ, hq, hlq⟩ := k
  let d := booleanProofNode n ψ 2 ⟨p, q⟩ₖ
  have hP' := hP.union hQ
  have hψ : ⟨n, ψ⟩ₖ ∈ F ∪ G := by
    have hi := (hP.2.2 p hp).label_mem
    rw [hlp] at hi
    exact mem_union_iff.mpr (Or.inl (hP.1.imp_right_mem hi))
  have hnode : IsInternalProofNode L Γ (F ∪ G) (insert d (D ∪ E)) d := by
    apply Or.inl
    apply Or.inl
    refine ⟨n, ψ, hψ, Or.inr (Or.inr (Or.inl ⟨p, ?_, q, ?_, φ, rfl, hlp, hlq⟩))⟩
    · exact mem_insert.mpr (Or.inr (mem_union_iff.mpr (Or.inl hp)))
    · exact mem_insert.mpr (Or.inr (mem_union_iff.mpr (Or.inr hq)))
  refine ⟨⟨F ∪ G, ⟨insert d (D ∪ E), d⟩ₖ⟩ₖ, F ∪ G, insert d (D ∪ E), d,
    rfl, internallyCountable_union hFc hGc,
    internallyCountable_insert (internallyCountable_union hDc hEc) d,
    hP'.insert hnode, by simp, ?_⟩
  exact booleanProofNode_label _ _ _ _

theorem IsInternalDerivationCode.generalization {L Γ F n φ c : V}
    (h : IsInternalDerivationCode L Γ (succ n) φ c) (hF : IsFragment L F)
    (hFc : IsInternallyCountable F) (hφ : ⟨n, allCode φ⟩ₖ ∈ F) :
    ∃ z, IsInternalDerivationCode L Γ n (allCode φ) z := by
  obtain ⟨G, D, p, rfl, hGc, hDc, hP, hp, hl⟩ := h
  let d := booleanProofNode n (allCode φ) 5 p
  have hGP : G ⊆ G ∪ F := fun _ hx ↦ mem_union_iff.mpr (Or.inl hx)
  have hP' := hP.weaken (hP.1.union hF) (fun _ hx ↦ hx)
    (fun x hx ↦ hGP x (hP.2.1 x hx)) hGP
  have hnode : IsInternalProofNode L Γ (G ∪ F) (insert d D) d := by
    exact Or.inl (Or.inr (Or.inr ⟨n, φ, p, mem_union_iff.mpr (Or.inr hφ),
      mem_insert.mpr (Or.inr hp), rfl, hl⟩))
  refine ⟨⟨G ∪ F, ⟨insert d D, d⟩ₖ⟩ₖ, G ∪ F, insert d D, d, rfl,
    internallyCountable_union hGc hFc, internallyCountable_insert hDc d,
    hP'.insert hnode, by simp, ?_⟩
  exact booleanProofNode_label _ _ _ _

theorem IsInternalDerivationCode.generalize {L Γ n φ c : V}
    (h : IsInternalDerivationCode L Γ (succ n) φ c) :
    ∃ z, IsInternalDerivationCode L Γ n (allCode φ) z := by
  obtain ⟨F, D, p, he, hFc, hDc, hP, hp, hl⟩ := h
  have hφ := (hP.2.2 p hp).label_mem
  rw [hl] at hφ
  have hn : n ∈ (ω : V) := IsTransitive.ω.mem_trans (by simp) (hP.1.node hφ).1
  exact IsInternalDerivationCode.generalization ⟨F, D, p, he, hFc, hDc, hP, hp, hl⟩
    (allFragment_valid hP.1 hn hφ) (allFragment_countable hFc) (allFragment_mem F n φ)

theorem IsInternalDerivationCode.substitute {L Γ s φ c : V}
    (h : IsInternalDerivationCode L Γ (stateSource s) φ c)
    (hs : IsSubstitutionState L ∅ ∅ s) :
    ∃ z, IsInternalDerivationCode L Γ (stateTarget s)
      (substituteCode L (kpair.π₁ c) s φ) z := by
  obtain ⟨F, D, p, rfl, hFc, hDc, hP, hp, hl⟩ := h
  simp only [kpair.π₁_kpair]
  have hφ := (hP.2.2 p hp).label_mem
  rw [hl] at hφ
  let H := F ∪ substitutionFragment L F s
  let d := booleanProofNode (stateTarget s) (substituteCode L F s φ) 9 ⟨F, ⟨s, p⟩ₖ⟩ₖ
  have hFH : F ⊆ H := fun _ hx ↦ mem_union_iff.mpr (Or.inl hx)
  have hH : IsFragment L H := hP.1.union (substitutionFragment_valid hP.1 hs)
  have hP' := hP.weaken hH (fun _ hx ↦ hx) (fun x hx ↦ hFH x (hP.2.1 x hx)) hFH
  have hnode : IsInternalProofNode L Γ H (insert d D) d := by
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨F, s, φ, p, hP.1, hs, hφ, ?_, ?_, hl, rfl⟩))))
    · exact mem_union_iff.mpr (Or.inr (substituteCode_mem hφ))
    · exact mem_insert.mpr (Or.inr hp)
  refine ⟨⟨H, ⟨insert d D, d⟩ₖ⟩ₖ, H, insert d D, d, rfl,
    internallyCountable_union hFc (substitutionFragment_countable hFc),
    internallyCountable_insert hDc d, hP'.insert hnode, by simp, ?_⟩
  exact booleanProofNode_label _ _ _ _

end ZFVP.Infinitary.Internal
