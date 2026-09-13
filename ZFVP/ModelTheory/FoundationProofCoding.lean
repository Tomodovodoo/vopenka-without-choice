import ZFVP.ModelTheory.FoundationTheoryCoding
import ZFVP.ModelTheory.StandardSentenceDischarge

/-! Represented theory proofs translate to finite internal proofs of the same sentence. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem strip_coded_theory_premises_context (T : V) (Γ : List SetTheorySentence)
    (Δ : Sequent ℒₛₑₜ) (k : ℕ) :
    (∀ φ ∈ Γ, StandardCodedProvable T 0 {encodeMembershipFormula φ}) →
    StandardCodedProvable T (((k + 1 : ℕ) : V)) (encodeFiniteSequent k (∼Sequent.embed Γ ++ Δ)) →
    StandardCodedProvable T (((k + 1 : ℕ) : V)) (encodeFiniteSequent k Δ) := by
  induction Γ with
  | nil => intro _ hp; simpa [Sequent.embed] using hp
  | cons φ Γ ih =>
    intro hax hp
    have ha := (hax φ (by simp)).lift_sentence k
    have ha' : StandardCodedProvable T (((k + 1 : ℕ) : V))
        (insert (encodeMembershipFormula (finiteVariableClosure k (φ : SetTheoryProposition))) ∅) := by
      simpa only [SetTheory.insert_empty_eq] using ha
    have hp' : StandardCodedProvable T (((k + 1 : ℕ) : V))
        (insert (negateFormula membershipLanguageCode ∅ (((k + 1 : ℕ) : V))
          (encodeMembershipFormula (finiteVariableClosure k (φ : SetTheoryProposition))))
          (encodeFiniteSequent k (∼Sequent.embed Γ ++ Δ))) := by
      simpa only [Sequent.embed_cons, List.tilde_def, List.map_cons, List.cons_append,
        encodeFiniteSequent_cons, finiteVariableClosure_neg, encodeMembershipFormula_neg, Nat.add_zero] using hp
    have hv : IsCodedSequent (((k + 1 : ℕ) : V)) (∅ ∪ encodeFiniteSequent k (∼Sequent.embed Γ ++ Δ)) := by
      simpa using encodeFiniteSequent_valid (V := V) k (∼Sequent.embed Γ ++ Δ)
    apply ih (fun ψ hψ ↦ hax ψ (List.mem_cons_of_mem φ hψ))
    simpa using ha'.cut hp' hv (encodeMembershipFormula_mem _)

theorem standardCodedProvable_of_foundation_provable {S : Theory ℒₛₑₜ} {T : V} {φ : SetTheorySentence}
    (hS : S ⊢ φ)
    (hax : ∀ χ ∈ S, StandardCodedProvable T 0 {encodeMembershipFormula χ})
    {ψ : SetTheorySemisentence 1} (hex : StandardCodedProvable T 0 {encodeMembershipFormula (∃¹ ψ)}) :
    StandardCodedProvable T 0 {encodeMembershipFormula φ} := by
  obtain ⟨Γ, hΓ, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp hS
  have hp := foundationDerivation_coded T d 0
  have hp' := hp.weaken (encodeFiniteSequent_valid (V := V) 0 (∼Sequent.embed Γ ++ [(φ : SetTheoryProposition)]))
    (encodeFiniteSequent_mono 0 (by intro χ hχ; simpa only [List.mem_cons, List.mem_append,
      List.mem_singleton, List.not_mem_nil, or_false, false_or, or_comm] using hχ))
  have hr := strip_coded_theory_premises_context T Γ [(φ : SetTheoryProposition)] 0
    (fun χ hχ ↦ hax χ (hΓ χ hχ)) hp'
  have ho : ((0 + 1 : ℕ) : V) = (1 : V) := rfl
  have hr' : StandardCodedProvable T 1 {encodeMembershipFormula φ} := by
    simpa only [encodeFiniteSequent_cons, encodeFiniteSequent_nil, SetTheory.insert_empty_eq,
      encodeMembershipFormula_finiteVariableClosure_embed, ho] using hr
  exact hr'.sentence_zero hex

theorem coded_proof_of_foundation_provable {S : Theory ℒₛₑₜ} {T : V} {φ : SetTheorySentence}
    (hS : S ⊢ φ)
    (hax : ∀ χ ∈ S, StandardCodedProvable T 0 {encodeMembershipFormula χ})
    {ψ : SetTheorySemisentence 1} (hex : StandardCodedProvable T 0 {encodeMembershipFormula (∃¹ ψ)}) :
    ∃ p, IsOpenCodedSequentProof T p 0 {encodeMembershipFormula φ} :=
  (standardCodedProvable_of_foundation_provable hS hax hex).to_internal

end ZFVP
