import ZFVP.ModelTheory.SchmerlCodedCandidateSemantics

/-! Realize the fixed class sentence in the specializing extension. The
cardinality quantifier is the internal countable-cover quantifier throughout. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl
open ZFVP.Infinitary (Formula)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W)
variable {c g : V}
variable (hc : IsInternalCofinalStrictChain (hartogsNumber (ω : V))
  (codedOrdinals R.code) (codedOrdinalOrder R.code) c)
variable (hg : g ∈ R.carrier ^ R.carrier)

include hc

theorem classBranchClause_of_candidate_definitions
    (hdefs : ∀ b : W, (R.equiv b).val ∈ codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c →
      (∀ i ∈ hartogsNumber (ω : V), ∃ x ∈ codedClassCandidate R.code (hartogsNumber (ω : V)) c g (R.equiv b).val,
        ⟨c ‘ i, (codedClassLevels R.code) ‘ x⟩ₖ ∈ codedOrdinalOrder R.code) →
      ℒₛₑₜ-predicate[W] (fun x ↦ (R.equiv x).val ∈ codedClassCandidate R.code (hartogsNumber (ω : V)) c g (R.equiv b).val)) :
    @Formula.Eval classLanguage W (R.representedClassExpansion hg c) 0 classBranchClause ![] := by
  let D := fun x ↦ (R.equiv x).val ∈ range c
  let f := R.representedColor hg
  let : Structure classLanguage W := classExpansion D f
  apply (eval_branchDefinabilityClause _ _ _ _ _ _ _).mpr
  dsimp only
  intro b hb hdb hcof
  obtain ⟨t, rfl⟩ := (eval_classNodeFormula b).mp ((eval_classOriginal D f classNodeFormula _).mp hb)
  have hdef := hdefs t.code ((R.eval_selectedClassNode hc hg t).mp hdb)
    (R.classCandidate_cofinality hc hg hcof)
  apply Language.DefinablePred.of_iff hdef
  exact fun x ↦ R.eval_classCandidate hc hg x t.code

theorem classRankSelectionWithQ :
    Schmerl.ClassRankSelectionWithQ R.representedQ (fun x ↦ (R.equiv x).val ∈ range c) :=
  ⟨R.cofinalChain_selected_Q hc, fun _ ↦ R.cofinalChain_selected_ordinal hc,
    R.cofinalChain_selected_initial hc, R.cofinalChain_selected_cofinal hc⟩

variable {U : Type*} [SetStructure U] [Nonempty U] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (j : MembershipEndExtension V U)
variable (hκ : j (hartogsNumber (ω : V)) = hartogsNumber (ω : U))
variable (hRubin : IsCodedRubin R.code (hartogsNumber (ω : V)))
variable (hpres : ∀ B : U,
  IsInternalCofinalBranch
    (j (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c))
    (j (codedSelectedClassOrder R.code (hartogsNumber (ω : V)) c))
    (j (hartogsNumber (ω : V))) (j (codedSelectedClassRank R.code (hartogsNumber (ω : V)) c)) B →
  ∃ C : V, IsInternalCofinalBranch (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c)
    (codedSelectedClassOrder R.code (hartogsNumber (ω : V)) c) (hartogsNumber (ω : V))
    (codedSelectedClassRank R.code (hartogsNumber (ω : V)) c) C ∧ j C = B)

include hκ hRubin hpres

theorem endExtension_classBranchClause (hω : HasStandardOmega V) {g' : U}
    (hg' : g' ∈ (R.endExtension j).carrier ^ (R.endExtension j).carrier)
    (hweak : InternallyWeakSpecialization
      (codedSelectedClassNodes (R.endExtension j).code (hartogsNumber (ω : U)) (j c))
      (codedSelectedClassOrder (R.endExtension j).code (hartogsNumber (ω : U)) (j c)) g') :
    @Formula.Eval classLanguage W ((R.endExtension j).representedClassExpansion hg' (j c)) 0 classBranchClause ![] := by
  have hc' : IsInternalCofinalStrictChain (hartogsNumber (ω : U))
      (codedOrdinals (R.endExtension j).code) (codedOrdinalOrder (R.endExtension j).code) (j c) := by
    simpa only [hκ] using R.endExtension_cofinalChain j hc
  apply (R.endExtension j).classBranchClause_of_candidate_definitions hc' hg'
  intro b hb hcof
  have h := R.codedClassCandidate_predicate j hc hRubin hpres hω
    (by simpa only [hκ] using hb) (by simpa only [hκ] using hweak)
    (by simpa only [hκ] using hcof)
  simpa only [hκ] using h

theorem endExtension_classTreeSentenceWithQ (hω : HasStandardOmega V) {f : U}
    (hf : f ∈ (ω : U) ^ codedSelectedClassNodes (R.endExtension j).code (hartogsNumber (ω : U)) (j c))
    (hweak : InternallyWeakSpecialization
      (codedSelectedClassNodes (R.endExtension j).code (hartogsNumber (ω : U)) (j c))
      (codedSelectedClassOrder (R.endExtension j).code (hartogsNumber (ω : U)) (j c)) f) :
    ∃ g' : U, ∃ hg' : g' ∈ (R.endExtension j).carrier ^ (R.endExtension j).carrier,
      @Formula.EvalWithQ classLanguage W ((R.endExtension j).representedClassExpansion hg' (j c))
        (R.endExtension j).representedQ 0 classTreeSentence ![] := by
  let R' := R.endExtension j
  have hc' : IsInternalCofinalStrictChain (hartogsNumber (ω : U))
      (codedOrdinals R'.code) (codedOrdinalOrder R'.code) (j c) := by
    simpa only [hκ] using R.endExtension_cofinalChain j hc
  let g' := codedClassColorGraph R'.carrier (codedSelectedClassNodes R'.code (hartogsNumber (ω : U)) (j c)) (j c) f
  have hg' : g' ∈ R'.carrier ^ R'.carrier := R'.codedClassColorGraph_function hc' hf
  refine ⟨g', hg', ?_⟩
  apply classTreeSentence_of_semanticDataWithQ R'.representedQ
    (fun x ↦ (R'.equiv x).val ∈ range (j c)) (R'.representedColor hg')
    (R'.classRankSelectionWithQ hc') (R'.codedClassColorGraph_not_Q hc' hf)
    (R'.codedClassColorGraph_weak hc' hf hweak)
  exact R.endExtension_classBranchClause hc j hκ hRubin hpres hω hg'
    (R'.codedClassColorGraph_internalWeak hc' hf hweak)

end ZFVP.BinaryRelationRepresentation
