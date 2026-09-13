import ZFVP.ModelTheory.FoundationProofCoding
import ZFVP.Syntax.ZFVPOpenAxiomSet
import ZFVP.Syntax.TemplateInstantiation

/-! Standard sentence instances of the internal ZF+VP axiom generators. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def fixedZFTheory : Theory ℒₛₑₜ :=
  {Axiom.empty, Axiom.extentionality, Axiom.pairing, Axiom.union,
    Axiom.power, Axiom.infinity, Axiom.foundation, equalityBasisSentence}

inductive GeneratedZFVPAxiom : SetTheorySentence → Prop
  | fixed {φ : SetTheorySentence} : φ ∈ fixedZFTheory → GeneratedZFVPAxiom φ
  | separation (k : ℕ) (φ : SetTheorySemisentence (k + 1)) :
      GeneratedZFVPAxiom (∀¹* separationTemplate.instantiateTail k φ)
  | replacement (k : ℕ) (φ : SetTheorySemisentence (k + 2)) :
      GeneratedZFVPAxiom (∀¹* replacementTemplate.instantiateTail k φ)
  | vopenka (φ : SetTheorySemisentence 2) :
      GeneratedZFVPAxiom (vopenkaTemplate.instantiate φ)

def generatedZFVPTheory : Theory ℒₛₑₜ := GeneratedZFVPAxiom

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem fixedZFTheory_encode {φ : SetTheorySentence} (hφ : φ ∈ fixedZFTheory) :
    encodeMembershipFormula φ ∈ (fixedZFSentenceCodes : V) := by
  simp only [fixedZFTheory, Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
  rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [fixedZFSentenceCodes]

theorem fixedZFTheory_coded {φ : SetTheorySentence} (hφ : φ ∈ fixedZFTheory) :
    StandardCodedProvable (zfVPOpenAxiomCodes : V) 0 {encodeMembershipFormula φ} :=
  .axiom (by simp) (encodeSentence_valid φ)
    ((mem_zfVPOpenAxiomCodes_iff _ _).mpr (Or.inl (Or.inl ⟨rfl, fixedZFTheory_encode hφ⟩)))

theorem generatedZFVPTheory_coded {φ : SetTheorySentence} (hφ : φ ∈ generatedZFVPTheory) :
    StandardCodedProvable (zfVPOpenAxiomCodes : V) 0 {encodeMembershipFormula φ} := by
  cases hφ with
  | fixed h => exact fixedZFTheory_coded h
  | separation k φ =>
    apply StandardCodedProvable.allClosure
    have hvalid : IsMembershipFormulaCode (succ (k : V)) (encodeMembershipFormula φ) := by
      simpa only [IsMembershipFormulaCode, num_succ_def] using (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem (V := V) φ)
    have hax : IsZFVPOpenAxiom (k : V) (separationCode (k : V) (encodeMembershipFormula φ)) :=
      Or.inl (Or.inr (Or.inl ⟨by simp, encodeMembershipFormula φ, hvalid, rfl⟩))
    have hp := StandardCodedProvable.axiom (by simp) hax.valid ((mem_zfVPOpenAxiomCodes_iff _ _).mpr hax)
    simpa only [separationCode, MembershipTemplate.compileTail_encode, Nat.add_zero] using hp
  | replacement k φ =>
    apply StandardCodedProvable.allClosure
    have hvalid : IsMembershipFormulaCode (succ (succ (k : V))) (encodeMembershipFormula φ) := by
      simpa only [IsMembershipFormulaCode, num_succ_def] using (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem (V := V) φ)
    have hax : IsZFVPOpenAxiom (k : V) (replacementCode (k : V) (encodeMembershipFormula φ)) :=
      Or.inl (Or.inr (Or.inr ⟨by simp, encodeMembershipFormula φ, hvalid, rfl⟩))
    have hp := StandardCodedProvable.axiom (by simp) hax.valid ((mem_zfVPOpenAxiomCodes_iff _ _).mpr hax)
    simpa only [replacementCode, MembershipTemplate.compileTail_encode, Nat.add_zero] using hp
  | vopenka φ =>
    have hvalid : IsMembershipFormulaCode (2 : V) (encodeMembershipFormula φ) :=
      (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem φ)
    have hax : IsZFVPOpenAxiom (0 : V) (vopenkaCode (encodeMembershipFormula φ)) :=
      Or.inr ⟨rfl, (mem_vopenkaAxiomCodes_iff _).mpr ⟨encodeMembershipFormula φ, hvalid, rfl⟩⟩
    have hp := StandardCodedProvable.axiom (by simp) hax.valid ((mem_zfVPOpenAxiomCodes_iff _ _).mpr hax)
    simpa only [vopenkaCode, MembershipTemplate.compile_encode] using hp

theorem generatedZFVPTheory_provable_coded {φ : SetTheorySentence} (hφ : generatedZFVPTheory ⊢ φ) :
    StandardCodedProvable (zfVPOpenAxiomCodes : V) 0 {encodeMembershipFormula φ} := by
  apply standardCodedProvable_of_foundation_provable hφ (fun _ h ↦ generatedZFVPTheory_coded h)
  exact fixedZFTheory_coded (φ := Axiom.empty) (by simp [fixedZFTheory])

theorem OpenCodedSequentConsistent.generatedZFVP_consistent
    (hT : OpenCodedSequentConsistent (zfVPOpenAxiomCodes : V)) :
    Entailment.Consistent generatedZFVPTheory := by
  apply hT.foundation_consistent (fun _ h ↦ generatedZFVPTheory_coded h)
  exact fixedZFTheory_coded (φ := Axiom.empty) (by simp [fixedZFTheory])

end ZFVP
