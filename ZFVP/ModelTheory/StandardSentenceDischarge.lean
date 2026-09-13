import ZFVP.ModelTheory.StandardSentenceCoding
import ZFVP.Syntax.ClosedEncodingInvariance

/-! Discharging a spare variable while retaining a closed conclusion. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem shiftCodedSequent_sentence (φ : SetTheorySentence) :
    shiftCodedSequent (0 : V) {encodeMembershipFormula φ} = {encodeMembershipFormula φ} := by
  have h := encodeClosedSequent_bShift (V := V) [φ]
  have hz : ((0 : ℕ) : V) = (0 : V) := rfl
  simpa only [List.map_cons, List.map_nil, encodeClosedSequent_cons, encodeClosedSequent_nil,
    SetTheory.insert_empty_eq, encodeMembershipFormula_closed_rew, hz] using h.symm

theorem StandardCodedProvable.sentence_zero {T : V} {φ : SetTheorySentence}
    (h : StandardCodedProvable T 1 {encodeMembershipFormula φ})
    {ψ : SetTheorySemisentence 1}
    (hex : StandardCodedProvable T 0 {encodeMembershipFormula (∃¹ ψ)}) :
    StandardCodedProvable T 0 {encodeMembershipFormula φ} := by
  have hz : ((0 : ℕ) : V) = (0 : V) := rfl
  have ho : ((1 : ℕ) : V) = (1 : V) := rfl
  have hs : succ (0 : V) = (1 : V) := by simpa only [hz, ho] using (num_succ_def (V := V) 0).symm
  have hv1 : IsCodedSequent (1 : V) (insert (encodeMembershipFormula (∼ψ)) {encodeMembershipFormula φ}) := by
    simpa only [encodeClosedSequent_cons, encodeClosedSequent_nil, SetTheory.insert_empty_eq,
      encodeMembershipFormula_closed_rew, ho] using
      encodeClosedSequent_valid (V := V) [∼ψ, Rew.bShift ▹ φ]
  have hp := h.weaken hv1 (by intro x hx; simp [hx])
  have hp' : StandardCodedProvable T (succ (0 : V))
      (insert (encodeMembershipFormula (∼ψ)) (shiftCodedSequent 0 {encodeMembershipFormula φ})) := by
    simpa only [shiftCodedSequent_sentence, hs] using hp
  have hv0 : IsCodedSequent (0 : V) (insert (allCode (encodeMembershipFormula (∼ψ))) {encodeMembershipFormula φ}) := by
    simpa only [encodeClosedSequent_cons, encodeClosedSequent_nil, SetTheory.insert_empty_eq,
      encodeMembershipFormula_all, hz] using encodeClosedSequent_valid (V := V) [∀¹ ∼ψ, φ]
  have hn := hp'.all hv0 (by simpa only [encodeClosedSequent_cons, encodeClosedSequent_nil,
    SetTheory.insert_empty_eq, hz] using (encodeClosedSequent_valid (V := V) [φ]).2.2)
    (by simpa only [ho, hs] using encodeMembershipFormula_mem (V := V) (∼ψ))
  have hn' : StandardCodedProvable T 0
      (insert (negateFormula membershipLanguageCode ∅ 0 (encodeMembershipFormula (∃¹ ψ)))
        {encodeMembershipFormula φ}) := by
    have he := encodeMembershipFormula_neg (V := V) (∃¹ ψ)
    change allCode (encodeMembershipFormula (∼ψ)) = _ at he
    rw [hz] at he
    rw [← he]
    exact hn
  have he' : StandardCodedProvable T 0 (insert (encodeMembershipFormula (∃¹ ψ)) ∅) := by
    simpa only [SetTheory.insert_empty_eq] using hex
  have hv : IsCodedSequent (0 : V) (∅ ∪ {encodeMembershipFormula φ}) := by
    simpa only [encodeClosedSequent_cons, encodeClosedSequent_nil, SetTheory.insert_empty_eq,
      empty_union, hz] using encodeClosedSequent_valid (V := V) [φ]
  simpa only [empty_union] using he'.cut hn' hv (encodeMembershipFormula_mem (∃¹ ψ))

end ZFVP
