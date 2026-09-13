import ZFVP.ModelTheory.SchmerlInternalBooleanProofs

/-! Membership end extensions preserve the actual internal Boolean proof
codes and their entire omega-indexed premise families. This is syntactic
transport and needs no cardinal-preservation or standard-omega hypothesis. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace EndExtension
variable (j : MembershipEndExtension V W)

theorem map_booleanProofNode (n φ tag data : V) :
    j (booleanProofNode n φ tag data) = booleanProofNode (j n) (j φ) (j tag) (j data) := by
  simp only [booleanProofNode, j.map_kpair]

theorem booleanProofNode_map {Γ F D d : V} (h : IsBooleanProofNode Γ F D d) :
    IsBooleanProofNode (j Γ) (j F) (j D) (j d) := by
  obtain ⟨n, φ, hφ, h⟩ := h
  refine ⟨j n, j φ, ?_, ?_⟩
  · rw [← j.map_kpair, j.mem_iff]
    exact hφ
  rcases h with ⟨rfl, hΓ⟩ | ⟨rfl, hax⟩ | ⟨p, hp, q, hq, ψ, rfl, hlp, hlq⟩ |
    ⟨f, g, hf, hfd, hg, hgd, rfl, hφ, hc⟩
  · refine Or.inl ⟨?_, ?_⟩
    · simp only [map_booleanProofNode, (show j (0 : V) = (0 : W) from j.map_numeral 0), j.map_empty]
    · rw [← j.map_kpair, j.mem_iff]
      exact hΓ
  · exact Or.inr (Or.inl ⟨by
      simp only [map_booleanProofNode, (show j (1 : V) = (1 : W) from j.map_numeral 1), j.map_empty], booleanAxiom_map j hax⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨j p, (j.mem_iff p D).mpr hp,
      j q, (j.mem_iff q D).mpr hq, j ψ, ?_, ?_, ?_⟩))
    · simp only [map_booleanProofNode, (show j (2 : V) = (2 : W) from j.map_numeral 2), j.map_kpair]
    · rw [← j.map_first, hlp, j.map_kpair, map_impCode]
    · rw [← j.map_first, hlq, j.map_kpair]
  · let := hf
    let := hg
    refine Or.inr (Or.inr (Or.inr ⟨j f, j g, j.map_function f, ?_,
      j.map_function g, ?_, ?_, ?_, ?_⟩))
    · rw [← j.map_domain, hfd, j.map_omega]
    · rw [← j.map_domain, hgd, j.map_omega]
    · simp only [map_booleanProofNode, (show j (3 : V) = (3 : W) from j.map_numeral 3)]
    · rw [hφ, map_conjCode]
    · intro i hi
      rw [← j.map_omega] at hi
      obtain ⟨k, hk, rfl⟩ := j.endExtension ω i hi
      obtain ⟨hm, hl⟩ := hc k hk
      constructor
      · rw [← j.map_value_total, j.mem_iff]
        exact hm
      · rw [← j.map_value_total, ← j.map_first, hl, j.map_kpair, j.map_value_total]

theorem booleanProof_map {L Γ F D : V} (h : IsBooleanProof L Γ F D) :
    IsBooleanProof (j L) (j Γ) (j F) (j D) := by
  refine ⟨fragment_map j h.1, (j.subset_iff Γ F).mpr h.2.1, ?_⟩
  intro d hd
  obtain ⟨p, hp, rfl⟩ := j.endExtension D d hd
  exact booleanProofNode_map j (h.2.2 p hp)

theorem booleanDerivationCode_map {L Γ n φ c : V} (h : IsBooleanDerivationCode L Γ n φ c) :
    IsBooleanDerivationCode (j L) (j Γ) (j n) (j φ) (j c) := by
  obtain ⟨F, D, d, rfl, hF, hD, hp, hd, hl⟩ := h
  refine ⟨j F, j D, j d, ?_, ?_, ?_, booleanProof_map j hp,
    (j.mem_iff d D).mpr hd, ?_⟩
  · simp only [j.map_kpair]
  · simpa only [IsInternallyCountable, j.map_omega] using j.map_cardLE hF
  · simpa only [IsInternallyCountable, j.map_omega] using j.map_cardLE hD
  · rw [← j.map_first, hl, j.map_kpair]

end EndExtension
end ZFVP.Infinitary.Internal

