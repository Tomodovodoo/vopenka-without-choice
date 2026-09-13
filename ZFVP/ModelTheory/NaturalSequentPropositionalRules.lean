import ZFVP.ModelTheory.NaturalSequentSemantics
import ZFVP.ModelTheory.InternalNegationProgram
import ZFVP.Syntax.NegationSemantics

/-! Soundness of the propositional natural-code LK rules on all internal formula codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem satisfies_natural_negation (M e : V) {c : V} (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement true).evalSet c) 0) :
    Satisfies membershipLanguageCode ω M e 0 (decodedNaturalFormula (negateCode.evalSet c)) ∅ ↔
      ¬ Satisfies membershipLanguageCode ω M e 0 (decodedNaturalFormula c) ∅ := by
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  have hφ : decodedNaturalFormula c ∈ formulaSet (membershipLanguageCode : V) ω 0 :=
    decodedNaturalFormula_valid true hc h0 hv
  rw [decodedNaturalFormula_negateCode true hc h0 hv]
  exact satisfies_negateFormula membershipLanguageCode_valid hφ (by simp [mem_function_iff, zero_def])

theorem satisfies_natural_or (M e : V) {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V))
    (hva : requirementFits ((formulaRequirement true).evalSet a) 0)
    (hvb : requirementFits ((formulaRequirement true).evalSet b) 0) :
    Satisfies membershipLanguageCode ω M e 0 (decodedNaturalFormula (succ (naturalSquarePair 5 (naturalSquarePair a b)))) ∅ ↔
      Satisfies membershipLanguageCode ω M e 0 (decodedNaturalFormula a) ∅ ∨
        Satisfies membershipLanguageCode ω M e 0 (decodedNaturalFormula b) ∅ := by
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  rw [decodedNaturalFormula_or ha hb]
  exact satisfies_or membershipLanguageCode_valid h0 (decodedNaturalFormula_valid true ha h0 hva)
    (decodedNaturalFormula_valid true hb h0 hvb) (by simp [mem_function_iff, zero_def])

theorem satisfies_natural_and (M e : V) {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V))
    (hva : requirementFits ((formulaRequirement true).evalSet a) 0)
    (hvb : requirementFits ((formulaRequirement true).evalSet b) 0) :
    Satisfies membershipLanguageCode ω M e 0 (decodedNaturalFormula (succ (naturalSquarePair 4 (naturalSquarePair a b)))) ∅ ↔
      Satisfies membershipLanguageCode ω M e 0 (decodedNaturalFormula a) ∅ ∧
        Satisfies membershipLanguageCode ω M e 0 (decodedNaturalFormula b) ∅ := by
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  rw [decodedNaturalFormula_and ha hb]
  exact satisfies_and membershipLanguageCode_valid h0 (decodedNaturalFormula_valid true ha h0 hva)
    (decodedNaturalFormula_valid true hb h0 hvb) (by simp [mem_function_iff, zero_def])

theorem NaturalSequentValid.eta (M : V) {c : V} (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement true).evalSet c) 0) :
    NaturalSequentValid M (succ (naturalSquarePair c (succ (naturalSquarePair (negateCode.evalSet c) 0)))) := by
  classical
  intro e _
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  have hneg := evalSet_natural negateCode hc
  rw [naturalSequentHolds_cons M e hc (ω_succ_closed (naturalSquarePair_natural hneg h0)),
    naturalSequentHolds_cons M e hneg h0, satisfies_natural_negation M e hc hv]
  exact (Classical.em _).imp_right Or.inl

theorem NaturalSequentValid.truth (M : V) :
    NaturalSequentValid M (succ (naturalSquarePair (succ (naturalSquarePair 2 0)) 0)) := by
  intro e _
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  rw [naturalSequentHolds_cons M e (ω_succ_closed (naturalSquarePair_natural (show (2 : V) ∈ (ω : V) from ofNat_mem_ω 2) h0)) h0,
    decodedNaturalFormula_verum h0]
  exact Or.inl ((satisfies_truth membershipLanguageCode_valid h0).mpr (by simp [mem_function_iff, zero_def]))

theorem NaturalSequentValid.cut {M c Γ Δ : V} (hc : c ∈ (ω : V)) (hΓ : Γ ∈ (ω : V)) (hΔ : Δ ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement true).evalSet c) 0)
    (hpos : NaturalSequentValid M (succ (naturalSquarePair c Γ)))
    (hneg : NaturalSequentValid M (succ (naturalSquarePair (negateCode.evalSet c) Δ))) :
    NaturalSequentValid M (listAppend.evalSet (naturalSquarePair Δ Γ)) := by
  intro e he
  rw [naturalSequentHolds_append M e hΓ hΔ]
  rcases (naturalSequentHolds_cons M e hc hΓ).mp (hpos e he) with hp | hp
  · rcases (naturalSequentHolds_cons M e (evalSet_natural negateCode hc) hΔ).mp (hneg e he) with hn | hn
    · exact False.elim ((satisfies_natural_negation M e hc hv).mp hn hp)
    · exact Or.inr hn
  · exact Or.inl hp

theorem NaturalSequentValid.or_rule {M a b Γ : V}
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hΓ : Γ ∈ (ω : V))
    (hva : requirementFits ((formulaRequirement true).evalSet a) 0)
    (hvb : requirementFits ((formulaRequirement true).evalSet b) 0)
    (h : NaturalSequentValid M (succ (naturalSquarePair a (succ (naturalSquarePair b Γ))))) :
    NaturalSequentValid M (succ (naturalSquarePair (succ (naturalSquarePair 5 (naturalSquarePair a b))) Γ)) := by
  intro e he
  rw [naturalSequentHolds_cons M e (ω_succ_closed (naturalSquarePair_natural (show (5 : V) ∈ (ω : V) from ofNat_mem_ω 5)
    (naturalSquarePair_natural ha hb))) hΓ, satisfies_natural_or M e ha hb hva hvb]
  have hp := h e he
  rw [naturalSequentHolds_cons M e ha (ω_succ_closed (naturalSquarePair_natural hb hΓ)),
    naturalSequentHolds_cons M e hb hΓ] at hp
  exact or_assoc.mpr hp

theorem NaturalSequentValid.and_rule {M a b Γ : V}
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hΓ : Γ ∈ (ω : V))
    (hva : requirementFits ((formulaRequirement true).evalSet a) 0)
    (hvb : requirementFits ((formulaRequirement true).evalSet b) 0)
    (hp : NaturalSequentValid M (succ (naturalSquarePair a Γ)))
    (hq : NaturalSequentValid M (succ (naturalSquarePair b Γ))) :
    NaturalSequentValid M (succ (naturalSquarePair (succ (naturalSquarePair 4 (naturalSquarePair a b))) Γ)) := by
  intro e he
  rw [naturalSequentHolds_cons M e (ω_succ_closed (naturalSquarePair_natural (show (4 : V) ∈ (ω : V) from ofNat_mem_ω 4)
    (naturalSquarePair_natural ha hb))) hΓ, satisfies_natural_and M e ha hb hva hvb]
  rcases (naturalSequentHolds_cons M e ha hΓ).mp (hp e he) with hpa | hΓ'
  · rcases (naturalSequentHolds_cons M e hb hΓ).mp (hq e he) with hqb | hΓ'
    · exact Or.inl ⟨hpa, hqb⟩
    · exact Or.inr hΓ'
  · exact Or.inr hΓ'

end ZFVP
