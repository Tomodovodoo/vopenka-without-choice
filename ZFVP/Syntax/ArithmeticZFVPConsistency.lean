import ZFVP.Syntax.NaturalZFVPProof
import Foundation.FirstOrder.Arithmetic.R0.Representation
import ZFVP.ModelTheory.ProtoRankBerkeleyCodedConsistency
import ZFVP.ModelTheory.ZFVPProofRepresentation

/-! An arithmetic consistency sentence for the verified recursive ZF+VP presentation.
The truth theorem here concerns the standard natural numbers. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

noncomputable def arithmeticZFVPRefutationFormula : ArithmeticSemisentence 1 :=
  codeOfREPred (fun e ↦ NaturalZFVPProof (Encodable.encode (⊥ : SetTheorySentence)) e)

noncomputable def arithmeticZFVPConsistencySentence : ArithmeticSentence :=
  ∀¹ ∼arithmeticZFVPRefutationFormula

theorem arithmeticZFVPRefutationFormula_sigmaOne :
    Hierarchy 𝚺 1 arithmeticZFVPRefutationFormula := by
  simp [arithmeticZFVPRefutationFormula, codeOfREPred, codeOfPartrec']

theorem arithmeticZFVPConsistencySentence_piOne :
    Hierarchy 𝚷 1 arithmeticZFVPConsistencySentence := by
  exact arithmeticZFVPRefutationFormula_sigmaOne.neg.all

theorem eval_arithmeticZFVPRefutationFormula (e : ℕ) :
    arithmeticZFVPRefutationFormula.Evalb ![e] ↔
      NaturalZFVPProof (Encodable.encode (⊥ : SetTheorySentence)) e := by
  exact codeOfREPred_spec ((naturalZFVPProof_primrec.comp
    (Primrec.const (Encodable.encode (⊥ : SetTheorySentence))) Primrec.id).computablePred.to_re)

theorem eval_arithmeticZFVPConsistencySentence :
    arithmeticZFVPConsistencySentence.Evalb (![] : Fin 0 → ℕ) ↔ Entailment.Consistent zfVPTheory := by
  rw [← naturalZFVPConsistent_iff]
  simp only [arithmeticZFVPConsistencySentence, Semiformula.Evalb, Semiformula.eval_all, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
  change (∀ e : ℕ, ¬arithmeticZFVPRefutationFormula.Evalb ![e]) ↔ _
  simp only [eval_arithmeticZFVPRefutationFormula, NaturalZFVPConsistent]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsProtoRankBerkeley.naturalZFVP_consistent {ζ δ : V} (hδ : IsProtoRankBerkeley ζ δ) :
    NaturalZFVPConsistent :=
  naturalZFVPConsistent_iff.mpr hδ.codedZFVP_consistent.zfVP_consistent

theorem IsProtoRankBerkeley.arithmeticZFVP_consistent {ζ δ : V} (hδ : IsProtoRankBerkeley ζ δ) :
    arithmeticZFVPConsistencySentence.Evalb (![] : Fin 0 → ℕ) :=
  eval_arithmeticZFVPConsistencySentence.mpr hδ.codedZFVP_consistent.zfVP_consistent

end ZFVP
