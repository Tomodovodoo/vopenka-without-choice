import ZFVP.ModelTheory.NaturalSequentPropositionalRules

/-! Soundness of the eigenvariable and witness rules for arbitrary internal natural formula codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem NaturalSequentValid.all_rule {M c Γ : V} (hM : IsStructureCode membershipLanguageCode M)
    (hc : c ∈ (ω : V)) (hΓ : Γ ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement true).evalSet c) 1) (hΓv : naturalSequentFits true 0 Γ)
    (h : NaturalSequentValid M (succ (naturalSquarePair
      (proofRewriteCode.evalSet (naturalSquarePair 1 (naturalSquarePair 0 c)))
      (proofRewriteSequent.evalSet (naturalSquarePair 0 Γ))))) :
    NaturalSequentValid M (succ (naturalSquarePair (succ (naturalSquarePair 6 c)) Γ)) := by
  classical
  intro e he
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  have h1 : (1 : V) ∈ (ω : V) := by simp
  have hbody : decodedNaturalFormula c ∈ formulaSet membershipLanguageCode ω (succ (0 : V)) := by
    rw [internalSucc_zero]
    exact decodedNaturalFormula_valid true hc h1 hv
  have hb : (∅ : V) ∈ structureDomain M ^ (0 : V) := by simp [mem_function_iff, zero_def]
  rw [naturalSequentHolds_cons M e (ω_succ_closed (naturalSquarePair_natural
    (show (6 : V) ∈ (ω : V) from ofNat_mem_ω 6) hc)) hΓ]
  by_cases hΓe : NaturalSequentHolds M e Γ
  · exact Or.inr hΓe
  · apply Or.inl
    rw [decodedNaturalFormula_all hc, satisfies_all hM.language h0 hbody hb]
    intro x hx
    have hp := h (omegaAssignmentPrepend e x) (omegaAssignmentPrepend_mem he hx)
    rw [naturalSequentHolds_cons _ _
      (evalSet_natural _ (naturalSquarePair_natural h1 (naturalSquarePair_natural h0 hc)))
      (evalSet_natural _ (naturalSquarePair_natural h0 hΓ))] at hp
    rcases hp with hp | hp
    · have hsat := (satisfies_proofRewrite_eigen_prepend hM he hx hc hv).mp hp
      simpa only [internalSucc_zero] using hsat
    · exact False.elim (hΓe ((naturalSequentHolds_shift_prepend hM he hx hΓ hΓv).mp hp))

theorem NaturalSequentValid.exists_rule {M c Γ k : V} (hM : IsStructureCode membershipLanguageCode M)
    (hc : c ∈ (ω : V)) (hΓ : Γ ∈ (ω : V)) (hk : k ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement true).evalSet c) 1)
    (h : NaturalSequentValid M (succ (naturalSquarePair
      (proofRewriteCode.evalSet (naturalSquarePair (succ (succ k)) (naturalSquarePair 0 c))) Γ))) :
    NaturalSequentValid M (succ (naturalSquarePair (succ (naturalSquarePair 7 c)) Γ)) := by
  intro e he
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  have hbody : decodedNaturalFormula c ∈ formulaSet membershipLanguageCode ω (succ (0 : V)) := by
    rw [internalSucc_zero]
    exact decodedNaturalFormula_valid true hc (by simp) hv
  have hb : (∅ : V) ∈ structureDomain M ^ (0 : V) := by simp [mem_function_iff, zero_def]
  rw [naturalSequentHolds_cons M e (ω_succ_closed (naturalSquarePair_natural
    (show (7 : V) ∈ (ω : V) from ofNat_mem_ω 7) hc)) hΓ]
  have hp := h e he
  rw [naturalSequentHolds_cons _ _
    (evalSet_natural _ (naturalSquarePair_natural (ω_succ_closed (ω_succ_closed hk)) (naturalSquarePair_natural h0 hc))) hΓ] at hp
  rcases hp with hp | hp
  · apply Or.inl
    rw [decodedNaturalFormula_exs hc, satisfies_exists hM.language h0 hbody hb]
    refine ⟨e ‘ k, function_value_mem he hk, ?_⟩
    have hsat := (satisfies_proofRewrite_witness hM he hc hk hv).mp hp
    simpa only [internalSucc_zero] using hsat
  · exact Or.inr hp

end ZFVP
