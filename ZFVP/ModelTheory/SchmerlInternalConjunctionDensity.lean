import ZFVP.ModelTheory.SchmerlInternalConsistencyExtension

/-! The negative-conjunction witness step for internal sentence theories.
The index ranges over the model's entire omega, and the contradiction uses
an actual internally countable conjunction derivation. -/
namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A derived negative conjunction has a consistently adjoinable negative instance. -/
theorem IsInternallyConsistentTheory.neg_conjunction_density_of_derivable {L Γ F f c : V}
    (h : IsInternallyConsistentTheory L Γ) (hF : IsFragment L F)
    (hFc : IsInternallyCountable F) (hΓF : Γ ⊆ F)
    (hf : ⟨(0 : V), conjCode f⟩ₖ ∈ F) (hAC : InternalChoice V)
    (hn : IsInternalDerivationCode L Γ 0 (negCode (conjCode f)) c) :
    ∃ i ∈ (ω : V), IsInternallyConsistentTheory L (insert ⟨(0 : V), negCode (f ‘ i)⟩ₖ Γ) := by
  classical
  by_contra hnone
  have hbad : ∀ i ∈ (ω : V), ¬IsInternallyConsistentTheory L (insert ⟨(0 : V), negCode (f ‘ i)⟩ₖ Γ) := by
    intro i hi hc
    exact hnone ⟨i, hi, hc⟩
  have hd : ∀ i ∈ (ω : V), ∃ d, IsInternalDerivationCode L Γ 0 (f ‘ i) d := by
    intro i hi
    obtain ⟨ψ, d, e, hp, hn⟩ := not_internallyConsistentTheory_iff.mp (hbad i hi)
    exact internalDerivation_reductio hF hFc hΓF ((hF.conj_data hf).2.2 i hi) hAC hp hn
  obtain ⟨d, hd⟩ := internalDerivation_conjunction hAC (hF.conj_data hf).1 (hF.conj_data hf).2.1 hd
  exact h (conjCode f) d c hd hn

/-- The Henkin witness step when the negative conjunction is already an assumption. -/
theorem IsInternallyConsistentTheory.neg_conjunction_density {L Γ F f : V}
    (h : IsInternallyConsistentTheory L Γ) (hF : IsFragment L F)
    (hFc : IsInternallyCountable F) (hΓF : Γ ⊆ F)
    (hf : ⟨(0 : V), negCode (conjCode f)⟩ₖ ∈ Γ) (hAC : InternalChoice V) :
    ∃ i ∈ (ω : V), IsInternallyConsistentTheory L (insert ⟨(0 : V), negCode (f ‘ i)⟩ₖ Γ) := by
  obtain ⟨c, hc⟩ := internalDerivation_hypothesis hF hFc hΓF hf
  exact h.neg_conjunction_density_of_derivable hF hFc hΓF (hF.neg_mem (hΓF _ hf)) hAC hc

/-- The witness extension and its valid countable ambient fragment are explicit. -/
theorem IsInternallyConsistentTheory.exists_neg_conjunction_extension {L Γ F f : V}
    (h : IsInternallyConsistentTheory L Γ) (hF : IsFragment L F)
    (hFc : IsInternallyCountable F) (hΓF : Γ ⊆ F)
    (hf : ⟨(0 : V), negCode (conjCode f)⟩ₖ ∈ Γ) (hAC : InternalChoice V) :
    ∃ i ∈ (ω : V),
      IsFunction f ∧ domain f = (ω : V) ∧
      Γ ⊆ insert ⟨(0 : V), negCode (f ‘ i)⟩ₖ Γ ∧
      insert ⟨(0 : V), negCode (f ‘ i)⟩ₖ Γ ⊆ insert ⟨(0 : V), negCode (f ‘ i)⟩ₖ F ∧
      IsFragment L (insert ⟨(0 : V), negCode (f ‘ i)⟩ₖ F) ∧
      IsInternallyCountable (insert ⟨(0 : V), negCode (f ‘ i)⟩ₖ F) ∧
      IsInternallyConsistentTheory L (insert ⟨(0 : V), negCode (f ‘ i)⟩ₖ Γ) := by
  obtain ⟨i, hi, hc⟩ := h.neg_conjunction_density hF hFc hΓF hf hAC
  have hdata := hF.conj_data (hF.neg_mem (hΓF _ hf))
  refine ⟨i, hi, hdata.1, hdata.2.1, fun t ht ↦ mem_insert.mpr (Or.inr ht), ?_,
    hF.insert_neg (hdata.2.2 i hi), internallyCountable_insert hFc _, hc⟩
  intro t ht
  rcases mem_insert.mp ht with rfl | ht
  · exact mem_insert.mpr (Or.inl rfl)
  · exact mem_insert.mpr (Or.inr (hΓF t ht))

end ZFVP.Infinitary.Internal
