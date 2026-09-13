import ZFVP.ModelTheory.SchmerlInternalQuantifierDerivation
import ZFVP.ModelTheory.SchmerlInternalSentenceSubstitution

/-! Sentence assumptions across the full internal quantifier and substitution rules. -/
namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sentence_mem_lift {L F n χ : V} (hF : IsFragment L F) (hn : n ∈ (ω : V))
    (hχ : ⟨(0 : V), χ⟩ₖ ∈ F) : ⟨n, χ⟩ₖ ∈ sentenceLiftFragment L F n := by
  simpa only [sentenceLiftCode_eq hF hn hχ] using (sentenceLiftCode_mem (L := L) (n := n) hχ)

theorem IsInternalDerivationCode.imp_generalize_closed {L Γ K n χ ψ c : V}
    (h : IsInternalDerivationCode L Γ (succ n) (impCode χ ψ) c)
    (hK : IsFragment L K) (hKc : IsInternallyCountable K)
    (hΓ : Γ ⊆ K) (hχ : ⟨(0 : V), χ⟩ₖ ∈ K) (hn : n ∈ (ω : V)) :
    ∃ z, IsInternalDerivationCode L Γ n (impCode χ (allCode ψ)) z := by
  have hA := sentenceLiftFragment_valid hK hn
  have hAc := sentenceLiftFragment_countable (L := L) (n := n) hKc
  have hχA := sentence_mem_lift hK hn hχ
  have hJ := hK.union hA
  have hχJ : ⟨n, χ⟩ₖ ∈ K ∪ sentenceLiftFragment L K n := mem_union_iff.mpr (Or.inr hχA)
  have hfix : weakenCode L (K ∪ sentenceLiftFragment L K n) n χ = χ := by
    simpa only [sentenceLiftCode_eq hK hn hχ, sentenceLiftCode_eq hK (ω_succ_closed hn) hχ] using
      weakenCode_sentenceLift hK hJ hn hχ (by simpa only [sentenceLiftCode_eq hK hn hχ] using hχJ)
  have h' : IsInternalDerivationCode L Γ (succ n)
      (impCode (weakenCode L (K ∪ sentenceLiftFragment L K n) n χ) ψ) c := by rw [hfix]; exact h
  exact h'.imp_generalize hJ (internallyCountable_union hKc hAc)
    (fun t ht ↦ mem_union_iff.mpr (Or.inl (hΓ t ht))) hχJ

theorem IsInternalDerivationCode.imp_substitute_closed {L Γ K H s χ ψ c : V}
    (h : IsInternalDerivationCode L Γ (stateSource s) (impCode χ ψ) c)
    (hK : IsFragment L K) (hχ : ⟨(0 : V), χ⟩ₖ ∈ K)
    (hH : IsFragment L H) (hs : IsSubstitutionState L ∅ ∅ s)
    (hψ : ⟨stateSource s, ψ⟩ₖ ∈ H) :
    ∃ z, IsInternalDerivationCode L Γ (stateTarget s) (impCode χ (substituteCode L H s ψ)) z := by
  obtain ⟨F, D, d, he, hFc, hDc, hP, hd, hl⟩ := h
  have ht : ⟨stateSource s, impCode χ ψ⟩ₖ ∈ F := by
    simpa only [hl] using (hP.2.2 d hd).label_mem
  have hfix : substituteCode L F s χ = χ := by
    simpa only [sentenceLiftCode_eq hK hs.1 hχ, sentenceLiftCode_eq hK hs.2.1 hχ] using
      substituteCode_sentenceLift hK hP.1 hs hχ
        (by simpa only [sentenceLiftCode_eq hK hs.1 hχ] using hP.1.imp_left_mem ht)
  obtain ⟨z, hz⟩ := (show IsInternalDerivationCode L Γ (stateSource s) (impCode χ ψ) c from
    ⟨F, D, d, he, hFc, hDc, hP, hd, hl⟩).imp_substitute hP.1 hs ht
  rw [hfix, substituteCode_fragment_eq hP.1 hH (hP.1.imp_right_mem ht) hψ] at hz
  exact ⟨z, hz⟩

end ZFVP.Infinitary.Internal
