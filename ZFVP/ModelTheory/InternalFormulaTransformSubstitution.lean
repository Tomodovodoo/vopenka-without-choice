import ZFVP.ModelTheory.InternalFormulaTransformEquations
import ZFVP.Syntax.FormulaSubstitutionDefinability
import ZFVP.Syntax.FormulaSubstitutionEquations
import ZFVP.ModelTheory.NaturalFormulaRequirementInduction

/-! A formula transformer agrees with internal substitution whenever its argument program does. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def FormulaTransformArgumentsAgree (arguments : PrimitiveProgram) (allowFree : Bool) (s G : V) : Prop :=
  ∀ {d k r c n : V}, d ∈ (ω : V) → k ∈ (ω : V) → r ∈ (ω : V) → c ∈ (ω : V) → n ∈ (ω : V) →
    requirementFits ((atomicRequirement allowFree).evalSet (naturalSquarePair k (naturalSquarePair r c))) n →
    decodedNaturalArguments (arguments.evalSet (naturalSquarePair s (naturalSquarePair d c))) =
      compose (decodedNaturalArguments c)
        (termSubstitution membershipLanguageCode (naturalSyntaxFreeDomain allowFree) n
          (stateBound (G ‘ d)) (stateFree (G ‘ d)))

theorem decodedNaturalFormula_formulaTransform_rel (arguments : PrimitiveProgram) (allowFree : Bool) {s d k r c n : V}
    (G : V) (hargs : FormulaTransformArgumentsAgree arguments allowFree s G)
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hk : k ∈ (ω : V)) (hr : r ∈ (ω : V)) (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((atomicRequirement allowFree).evalSet (naturalSquarePair k (naturalSquarePair r c))) n) :
    decodedNaturalFormula ((formulaTransformCode arguments).evalSet (naturalSquarePair s
      (naturalSquarePair d (succ (naturalSquarePair 0 (naturalSquarePair k (naturalSquarePair r c))))))) =
      (formulaSubstitutionGraph membershipLanguageCode (naturalSyntaxFreeDomain allowFree) G) ‘
        ⟨⟨n, decodedNaturalFormula (succ (naturalSquarePair 0 (naturalSquarePair k (naturalSquarePair r c))))⟩ₖ, d⟩ₖ := by
  have h2 : (2 : V) ∈ (ω : V) := ofNat_mem_ω 2
  have ha := evalSet_natural arguments (naturalSquarePair_natural hs (naturalSquarePair_natural hd hc))
  rw [evalSet_formulaTransformCode_rel arguments hs hd hk hr hc,
    decodedNaturalFormula_rel (naturalSquarePair_natural h2 (naturalSquarePair_natural hr ha)),
    decodedNaturalFormula_rel (naturalSquarePair_natural hk (naturalSquarePair_natural hr hc))]
  simp only [naturalSquareLeft, naturalSquareRight,
    naturalSquareUnpair_pair h2 (naturalSquarePair_natural hr ha), naturalSquareUnpair_pair hr ha,
    naturalSquareUnpair_pair hk (naturalSquarePair_natural hr hc), naturalSquareUnpair_pair hr hc]
  rw [formulaSubstitutionGraph_atom membershipLanguageCode_valid hn hd
      (decodedNaturalAtomic_valid allowFree hk hr hc hn hv), hargs hd hk hr hc hn hv]

theorem decodedNaturalFormula_formulaTransform_nrel (arguments : PrimitiveProgram) (allowFree : Bool) {s d k r c n : V}
    (G : V) (hargs : FormulaTransformArgumentsAgree arguments allowFree s G)
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hk : k ∈ (ω : V)) (hr : r ∈ (ω : V)) (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((atomicRequirement allowFree).evalSet (naturalSquarePair k (naturalSquarePair r c))) n) :
    decodedNaturalFormula ((formulaTransformCode arguments).evalSet (naturalSquarePair s
      (naturalSquarePair d (succ (naturalSquarePair 1 (naturalSquarePair k (naturalSquarePair r c))))))) =
      (formulaSubstitutionGraph membershipLanguageCode (naturalSyntaxFreeDomain allowFree) G) ‘
        ⟨⟨n, decodedNaturalFormula (succ (naturalSquarePair 1 (naturalSquarePair k (naturalSquarePair r c))))⟩ₖ, d⟩ₖ := by
  have h2 : (2 : V) ∈ (ω : V) := ofNat_mem_ω 2
  have ha := evalSet_natural arguments (naturalSquarePair_natural hs (naturalSquarePair_natural hd hc))
  rw [evalSet_formulaTransformCode_nrel arguments hs hd hk hr hc,
    decodedNaturalFormula_nrel (naturalSquarePair_natural h2 (naturalSquarePair_natural hr ha)),
    decodedNaturalFormula_nrel (naturalSquarePair_natural hk (naturalSquarePair_natural hr hc))]
  simp only [naturalSquareLeft, naturalSquareRight,
    naturalSquareUnpair_pair h2 (naturalSquarePair_natural hr ha), naturalSquareUnpair_pair hr ha,
    naturalSquareUnpair_pair hk (naturalSquarePair_natural hr hc), naturalSquareUnpair_pair hr hc]
  rw [formulaSubstitutionGraph_negAtom membershipLanguageCode_valid hn hd
      (decodedNaturalAtomic_valid allowFree hk hr hc hn hv), hargs hd hk hr hc hn hv]

theorem decodedNaturalFormula_formulaTransform_substitution (arguments : PrimitiveProgram) (allowFree : Bool) {s c n d : V}
    (G : V) (hargs : FormulaTransformArgumentsAgree arguments allowFree s G)
    (hs : s ∈ (ω : V)) (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement allowFree).evalSet c) n) :
    decodedNaturalFormula ((formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d c))) =
      (formulaSubstitutionGraph membershipLanguageCode (naturalSyntaxFreeDomain allowFree) G) ‘
        ⟨⟨n, decodedNaturalFormula c⟩ₖ, d⟩ₖ := by
  have H : ∀ d ∈ (ω : V),
      decodedNaturalFormula ((formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d c))) =
        (formulaSubstitutionGraph membershipLanguageCode (naturalSyntaxFreeDomain allowFree) G) ‘
          ⟨⟨n, decodedNaturalFormula c⟩ₖ, d⟩ₖ := by
    apply naturalFormulaRequirement_induction allowFree
      (fun n c : V ↦ ∀ d ∈ (ω : V),
        decodedNaturalFormula ((formulaTransformCode arguments).evalSet (naturalSquarePair s (naturalSquarePair d c))) =
          (formulaSubstitutionGraph membershipLanguageCode (naturalSyntaxFreeDomain allowFree) G) ‘
            ⟨⟨n, decodedNaturalFormula c⟩ₖ, d⟩ₖ)
      (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hc hn hv
    · intro n a hn ha hv d hd
      have he : naturalSquarePair (naturalSquareLeft a) (naturalSquareRight a) = a :=
        (naturalSquareUnpair_spec ha).2.2
      have he2 : naturalSquarePair (naturalSquareLeft (naturalSquareRight a))
          (naturalSquareRight (naturalSquareRight a)) = naturalSquareRight a :=
        (naturalSquareUnpair_spec (naturalSquareRight_natural a)).2.2
      have hv' : requirementFits ((atomicRequirement allowFree).evalSet
          (naturalSquarePair (naturalSquareLeft a) (naturalSquarePair
            (naturalSquareLeft (naturalSquareRight a)) (naturalSquareRight (naturalSquareRight a))))) n := by
        simpa only [he2, he] using hv
      simpa only [he2, he] using decodedNaturalFormula_formulaTransform_rel arguments allowFree G hargs hs hd
        (naturalSquareLeft_natural a) (naturalSquareLeft_natural _) (naturalSquareRight_natural _) hn hv'
    · intro n a hn ha hv d hd
      have he : naturalSquarePair (naturalSquareLeft a) (naturalSquareRight a) = a :=
        (naturalSquareUnpair_spec ha).2.2
      have he2 : naturalSquarePair (naturalSquareLeft (naturalSquareRight a))
          (naturalSquareRight (naturalSquareRight a)) = naturalSquareRight a :=
        (naturalSquareUnpair_spec (naturalSquareRight_natural a)).2.2
      have hv' : requirementFits ((atomicRequirement allowFree).evalSet
          (naturalSquarePair (naturalSquareLeft a) (naturalSquarePair
            (naturalSquareLeft (naturalSquareRight a)) (naturalSquareRight (naturalSquareRight a))))) n := by
        simpa only [he2, he] using hv
      simpa only [he2, he] using decodedNaturalFormula_formulaTransform_nrel arguments allowFree G hargs hs hd
        (naturalSquareLeft_natural a) (naturalSquareLeft_natural _) (naturalSquareRight_natural _) hn hv'
    · intro n a hn ha d hd
      rw [evalSet_formulaTransformCode_verum arguments hs hd ha, decodedNaturalFormula_verum (by simp),
        decodedNaturalFormula_verum ha, formulaSubstitutionGraph_truth membershipLanguageCode_valid hn hd]
    · intro n a hn ha d hd
      rw [evalSet_formulaTransformCode_falsum arguments hs hd ha, decodedNaturalFormula_falsum (by simp),
        decodedNaturalFormula_falsum ha, formulaSubstitutionGraph_falsity membershipLanguageCode_valid hn hd]
    · intro n a b hn ha hb hva hvb iha ihb d hd
      rw [evalSet_formulaTransformCode_and arguments hs hd ha hb,
        decodedNaturalFormula_and
          (evalSet_natural _ (naturalSquarePair_natural hs (naturalSquarePair_natural hd ha)))
          (evalSet_natural _ (naturalSquarePair_natural hs (naturalSquarePair_natural hd hb))),
        decodedNaturalFormula_and ha hb, formulaSubstitutionGraph_and membershipLanguageCode_valid hn hd
          (decodedNaturalFormula_valid allowFree ha hn hva) (decodedNaturalFormula_valid allowFree hb hn hvb),
        iha d hd, ihb d hd]
    · intro n a b hn ha hb hva hvb iha ihb d hd
      rw [evalSet_formulaTransformCode_or arguments hs hd ha hb,
        decodedNaturalFormula_or
          (evalSet_natural _ (naturalSquarePair_natural hs (naturalSquarePair_natural hd ha)))
          (evalSet_natural _ (naturalSquarePair_natural hs (naturalSquarePair_natural hd hb))),
        decodedNaturalFormula_or ha hb, formulaSubstitutionGraph_or membershipLanguageCode_valid hn hd
          (decodedNaturalFormula_valid allowFree ha hn hva) (decodedNaturalFormula_valid allowFree hb hn hvb),
        iha d hd, ihb d hd]
    · intro n a hn ha hva iha d hd
      rw [evalSet_formulaTransformCode_all arguments hs hd ha,
        decodedNaturalFormula_all
          (evalSet_natural _ (naturalSquarePair_natural hs (naturalSquarePair_natural (ω_succ_closed hd) ha))),
        decodedNaturalFormula_all ha, formulaSubstitutionGraph_all membershipLanguageCode_valid hn hd
          (decodedNaturalFormula_valid allowFree ha (ω_succ_closed hn) hva),
        iha (succ d) (ω_succ_closed hd)]
    · intro n a hn ha hva iha d hd
      rw [evalSet_formulaTransformCode_exs arguments hs hd ha,
        decodedNaturalFormula_exs
          (evalSet_natural _ (naturalSquarePair_natural hs (naturalSquarePair_natural (ω_succ_closed hd) ha))),
        decodedNaturalFormula_exs ha, formulaSubstitutionGraph_exists membershipLanguageCode_valid hn hd
          (decodedNaturalFormula_valid allowFree ha (ω_succ_closed hn) hva),
        iha (succ d) (ω_succ_closed hd)]
  exact H d hd

end ZFVP

