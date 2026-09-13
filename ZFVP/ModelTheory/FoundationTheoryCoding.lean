import ZFVP.ModelTheory.StandardSentenceCoding

/-! Standard theory refutations produce internal proof codes once their axioms are represented. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem strip_coded_theory_premises (T : V) (Γ : List SetTheorySentence) (k : ℕ) :
    (∀ φ ∈ Γ, StandardCodedProvable T 0 {encodeMembershipFormula φ}) →
    StandardCodedProvable T (((k + 1 : ℕ) : V)) (encodeFiniteSequent k (∼Sequent.embed Γ)) →
    StandardCodedProvable T (((k + 1 : ℕ) : V)) ∅ := by
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
          (encodeFiniteSequent k (∼Sequent.embed Γ))) := by
      simpa only [Sequent.embed_cons, List.tilde_def, List.map_cons, encodeFiniteSequent_cons,
        finiteVariableClosure_neg, encodeMembershipFormula_neg, Nat.add_zero] using hp
    have hv : IsCodedSequent (((k + 1 : ℕ) : V)) (∅ ∪ encodeFiniteSequent k (∼Sequent.embed Γ)) := by
      simpa using encodeFiniteSequent_valid (V := V) k (∼Sequent.embed Γ)
    apply ih (fun ψ hψ ↦ hax ψ (List.mem_cons_of_mem φ hψ))
    simpa using ha'.cut hp' hv (encodeMembershipFormula_mem _)

theorem coded_refutation_of_foundation_inconsistent {S : Theory ℒₛₑₜ} {T : V}
    (hS : Entailment.Inconsistent S)
    (hax : ∀ φ ∈ S, StandardCodedProvable T 0 {encodeMembershipFormula φ})
    {ψ : SetTheorySemisentence 1} (hex : StandardCodedProvable T 0 {encodeMembershipFormula (∃¹ ψ)}) :
    ∃ p, IsOpenCodedSequentProof T p 0 ∅ := by
  obtain ⟨Γ, hΓ, ⟨d⟩⟩ := Theory.Proof.inconsistent_iff.mp hS
  have hp := foundationDerivation_coded T d 0
  have hr := strip_coded_theory_premises T Γ 0 (fun φ hφ ↦ hax φ (hΓ φ hφ)) hp
  exact (hr.refutation_zero hex).to_internal

theorem OpenCodedSequentConsistent.foundation_consistent {S : Theory ℒₛₑₜ} {T : V}
    (hT : OpenCodedSequentConsistent T)
    (hax : ∀ φ ∈ S, StandardCodedProvable T 0 {encodeMembershipFormula φ})
    {ψ : SetTheorySemisentence 1} (hex : StandardCodedProvable T 0 {encodeMembershipFormula (∃¹ ψ)}) :
    Entailment.Consistent S := by
  apply Entailment.not_inconsistent_iff_consistent.mp
  intro hS
  exact hT (coded_refutation_of_foundation_inconsistent hS hax hex)

end ZFVP
