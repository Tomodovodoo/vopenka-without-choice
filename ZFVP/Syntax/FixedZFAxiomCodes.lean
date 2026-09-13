import ZFVP.Syntax.ZFSchemaCodes
import ZFVP.ModelTheory.OpenCodedSequentSoundness

/-! The seven fixed ZF axioms and a finite equality basis as sentence codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def equalityBasisSentence : SetTheorySentence :=
  “(∀ x, x = x) ∧ (∀ x y, x = y → y = x) ∧
    (∀ x y z, x = y → y = z → x = z) ∧
    (∀ x y u v, x = y → u = v → (x ∈ u ↔ y ∈ v))”

theorem eval_equalityBasisSentence {W : Type*} [SetStructure W] :
    equalityBasisSentence.Evalb (![] : Fin 0 → W) := by
  simp only [equalityBasisSentence, Semiformula.Evalb]
  simp
  intro x y z he
  subst y
  rfl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def fixedZFSentenceCodes : V :=
  {encodeMembershipFormula Axiom.empty, encodeMembershipFormula Axiom.extentionality,
    encodeMembershipFormula Axiom.pairing, encodeMembershipFormula Axiom.union,
    encodeMembershipFormula Axiom.power, encodeMembershipFormula Axiom.infinity,
    encodeMembershipFormula Axiom.foundation, encodeMembershipFormula equalityBasisSentence}

theorem mem_fixedZFSentenceCodes_iff (ψ : V) : ψ ∈ (fixedZFSentenceCodes : V) ↔
    ψ = encodeMembershipFormula Axiom.empty ∨ ψ = encodeMembershipFormula Axiom.extentionality ∨
    ψ = encodeMembershipFormula Axiom.pairing ∨ ψ = encodeMembershipFormula Axiom.union ∨
    ψ = encodeMembershipFormula Axiom.power ∨ ψ = encodeMembershipFormula Axiom.infinity ∨
    ψ = encodeMembershipFormula Axiom.foundation ∨ ψ = encodeMembershipFormula equalityBasisSentence := by
  simp [fixedZFSentenceCodes]

theorem encodeSentence_valid (ψ : SetTheorySentence) :
    IsMembershipFormulaCode (0 : V) (encodeMembershipFormula ψ) :=
  (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem ψ)

theorem fixedZFSentenceCodes_valid {ψ : V} (hψ : ψ ∈ (fixedZFSentenceCodes : V)) :
    IsMembershipFormulaCode (0 : V) ψ := by
  rcases (mem_fixedZFSentenceCodes_iff ψ).mp hψ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact encodeSentence_valid _

theorem setSentenceTrue_iff_code {U : V} (hU : IsNonempty U) (ψ : SetTheorySentence) :
    SetSentenceTrue ψ U ↔ MembershipSatisfies U 0 (encodeMembershipFormula ψ) ∅ := by
  let : Nonempty (SetDomain U) := by
    obtain ⟨x, hx⟩ := hU.nonempty
    exact ⟨⟨x, hx⟩⟩
  rw [setSentenceTrue_iff_models]
  have he := membershipSatisfies_encode hU ψ (![] : Fin 0 → SetDomain U)
  have hzero : ((0 : ℕ) : V) = (0 : V) := rfl
  rw [hzero] at he
  simpa only [models_iff, Semiformula.Realize, Semiformula.Evalb, standardTuple] using he.symm

theorem InternalFixedZFAxioms.satisfies_codes {U : V} (hU : InternalFixedZFAxioms U) :
    SatisfiesSentenceCodes U fixedZFSentenceCodes := by
  refine ⟨hU.1, fun ψ hψ ↦ ⟨fixedZFSentenceCodes_valid hψ, ?_⟩⟩
  rcases (mem_fixedZFSentenceCodes_iff ψ).mp hψ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (setSentenceTrue_iff_code hU.1 _).mp hU.2.1
  · exact (setSentenceTrue_iff_code hU.1 _).mp hU.2.2.1
  · exact (setSentenceTrue_iff_code hU.1 _).mp hU.2.2.2.1
  · exact (setSentenceTrue_iff_code hU.1 _).mp hU.2.2.2.2.1
  · exact (setSentenceTrue_iff_code hU.1 _).mp hU.2.2.2.2.2.1
  · exact (setSentenceTrue_iff_code hU.1 _).mp hU.2.2.2.2.2.2.1
  · exact (setSentenceTrue_iff_code hU.1 _).mp hU.2.2.2.2.2.2.2
  · exact (membershipSatisfies_encode hU.1 equalityBasisSentence (![] : Fin 0 → SetDomain U)).mpr
      eval_equalityBasisSentence

theorem internalFixedZFAxioms_iff_satisfies_codes (U : V) :
    InternalFixedZFAxioms U ↔ SatisfiesSentenceCodes U fixedZFSentenceCodes := by
  constructor
  · exact InternalFixedZFAxioms.satisfies_codes
  · intro h
    have hs (ψ : SetTheorySentence) (hψ : encodeMembershipFormula ψ ∈ (fixedZFSentenceCodes : V)) :
        SetSentenceTrue ψ U := (setSentenceTrue_iff_code h.1 ψ).mpr (h.2 _ hψ).2
    refine ⟨h.1, hs _ ?_, hs _ ?_, hs _ ?_, hs _ ?_, hs _ ?_, hs _ ?_, hs _ ?_⟩
    all_goals simp [fixedZFSentenceCodes]

end ZFVP
