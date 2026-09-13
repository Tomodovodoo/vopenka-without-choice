import ZFVP.ModelTheory.WoodinSparseCodedForcingTruth
import ZFVP.ModelTheory.ForcingRegularGenericEquality
import ZFVP.ModelTheory.WoodinSparseEndpointGenericPresentation
import ZFVP.Syntax.LowRankForcingTruth
import ZFVP.ModelTheory.CountableZFTransfer
import ZFVP.ModelTheory.LocalSparsePrefixForcingFormula
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sparseCodedForcingMembershipFormula (k : ℕ) (pol : LevyPolarity) : SetTheorySemisentence 7 :=
  f“P R δ p n e s. !(lowRankForcingTruthFormula (domainTruthFormula pol k)) P R δ δ p
    (!assignmentPrependFormula (!(numeralFormula 2))
      (!assignmentPrependFormula (!(numeralFormula 1))
        (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) (!sequenceNameFormula (!isEmpty) s))
        (!checkNameFormula (!isEmpty) e))
      (!checkNameFormula (!isEmpty) n))”

def sparseCodedForcingEqualityFormula (k : ℕ) (pol : LevyPolarity) : SetTheorySemisentence 7 :=
  f“Ω P R D n e s. !woodinSupercompactFormula Ω ∧ ¬!choiceFunctionSentence ∧
    P = !value.dfn (!forcingCodePFormula (!woodinSparseStageCodeFormula Ω)) Ω ∧
    R = !value.dfn (!forcingCodeRFormula (!woodinSparseStageCodeFormula Ω)) Ω ∧
    D = !lowRankNameSetValueFormula P Ω ∧ !(sigmaOneLevyCodeFormula pol (k + 1)) n e ∧
    s ∈ !function.dfn D n → ∀ p ∈ P,
      (!(sparseCodedForcingMembershipFormula k pol) P R Ω p n e s ↔
        !sigmaOneInternalForcingFormula P R D n e s p)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sparseCodedForcingMembershipFormula_defined (k : ℕ) (pol : LevyPolarity) :
    Defined (fun v : Fin 7 → V ↦ v 3 ∈ sparseCodedForcingSet (v 0) (v 1) (v 2) k pol (v 4) (v 5) (v 6))
      (sparseCodedForcingMembershipFormula k pol) :=
  ⟨fun v ↦ by
    simp [sparseCodedForcingMembershipFormula, sparseCodedForcingSet, codedForcingArguments,
      standardTuple, Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ]
    constructor
    · intro h; exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    · rintro h a b c d e f rfl rfl rfl rfl rfl rfl; exact h⟩
theorem eval_sparseCodedForcingEqualityFormula (k : ℕ) (pol : LevyPolarity) (v : Fin 7 → V) :
    (sparseCodedForcingEqualityFormula k pol).Evalb v ↔
      (IsWoodinSupercompact (v 0) → ¬InternalChoice V →
        v 1 = (forcingCodeP (woodinSparseStageCode (v 0))) ‘ (v 0) →
        v 2 = (forcingCodeR (woodinSparseStageCode (v 0))) ‘ (v 0) →
        v 3 = lowRankNameSet (v 1) (v 0) →
        IsLevyFormulaCode pol (k + 1) (v 4) (v 5) → v 6 ∈ v 3 ^ v 4 →
        ∀ p ∈ v 1, p ∈ sparseCodedForcingSet (v 1) (v 2) (v 0) k pol (v 4) (v 5) (v 6) ↔
          p ∈ internalForcingSet (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := by
  have he : (sparseCodedForcingEqualityFormula k pol).Evalb v ↔
      (IsWoodinSupercompact (v 0) → ¬InternalChoice V →
        v 1 = (forcingCodeP (woodinSparseStageCode (v 0))) ‘ (v 0) →
        v 2 = (forcingCodeR (woodinSparseStageCode (v 0))) ‘ (v 0) →
        v 3 = lowRankNameSet (v 1) (v 0) →
        IsLevyFormulaCode pol (k + 1) (v 4) (v 5) → v 6 ∈ v 3 ^ v 4 →
        ∀ p ∈ v 1, p ∈ sparseCodedForcingSet (v 1) (v 2) (v 0) k pol (v 4) (v 5) (v 6) ↔
          sigmaOneInternalForcingFormula.Evalb ![v 1,v 2,v 3,v 4,v 5,v 6,p]) := by
    simp [sparseCodedForcingEqualityFormula]
  rw [he]
  apply forall_congr'; intro hΩ
  apply forall_congr'; intro hAC
  apply forall_congr'; intro hP
  apply forall_congr'; intro hR
  apply forall_congr'; intro hD
  apply forall_congr'; intro hφ
  apply forall_congr'; intro hs
  apply forall_congr'; intro p
  apply forall_congr'; intro hp
  exact iff_congr Iff.rfl ((eval_sigmaOneInternalForcingFormula (R := v 2) hφ.membershipCode hs hp).trans
    (mem_internalForcingSet hφ.membershipCode).symm)

theorem woodinSparse_codedForcing_eq_internal_countable [Countable V] {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    {k : ℕ} {pol : LevyPolarity} {n φ s : V}
    (hφ : IsLevyFormulaCode pol (k + 1) n φ)
    (hs : s ∈ lowRankNameSet ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) Ω ^ n) :
    sparseCodedForcingSet ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
      ((forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω) Ω k pol n φ s =
    internalForcingSet ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
      ((forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω)
      (lowRankNameSet ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) Ω) n φ s := by
  let := hΩ.inaccessible.1
  have hvalid := woodinSparseStageCode_valid hΩ hAC (subset_refl Ω)
  have horder := hvalid.system.order.preorder Ω (mem_succ_self Ω)
  have htop := hvalid.system.tops.top Ω (mem_succ_self Ω)
  rw [woodinSparseStageCode_top hΩ hAC (subset_refl Ω)] at htop
  apply IsForcingRegular.eq_of_all_generics horder
    (classForcingFormula_regular _ _ horder _ _)
    (internalForcingSet_regular horder hφ.membershipCode hs)
  intro H hH
  let A : ForcingContext V := {
    P := ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
    R := ((forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω)
    one := ∅
    G := H
    order := horder
    top := htop
    generic := hH }
  obtain ⟨G, hG, hEq⟩ := woodinSparseEndpoint_raw_generic_presentation hΩ hAC A rfl rfl rfl
  have ht := woodinSparse_codedForcing_internalForcing hΩ hAC hG (s := s) hφ
  rw [hEq] at ht
  exact ht hs

/-- Pointwise identification with the actual internally coded forcing relation
in every ZF ground model. Countability is removed by first-order transfer. -/
theorem woodinSparse_codedForcing_eq_internal {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    {k : ℕ} {pol : LevyPolarity} {n φ s : V}
    (hφ : IsLevyFormulaCode pol (k + 1) n φ)
    (hs : s ∈ lowRankNameSet ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) Ω ^ n) :
    sparseCodedForcingSet ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
      ((forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω) Ω k pol n φ s =
    internalForcingSet ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
      ((forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω)
      (lowRankNameSet ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) Ω) n φ s := by
  let P := (forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω
  let R := (forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω
  let D := lowRankNameSet P Ω
  have hc : (sparseCodedForcingEqualityFormula k pol).Evalb ![Ω,P,R,D,n,φ,s] := by
    apply eval_of_countable_zf (sparseCodedForcingEqualityFormula k pol)
    intro W _ _ _ _ v
    rw [eval_sparseCodedForcingEqualityFormula]
    intro hΩ hAC hP hR hD hφ hs p _
    have hs' : v 6 ∈ lowRankNameSet ((forcingCodeP (woodinSparseStageCode (v 0))) ‘ (v 0)) (v 0) ^ v 4 := by
      simpa only [hD, hP] using hs
    have he := woodinSparse_codedForcing_eq_internal_countable hΩ hAC hφ hs'
    simpa only [hD, hP, hR] using (iff_of_eq (congrArg (fun S ↦ p ∈ S) he))
  have hh := (eval_sparseCodedForcingEqualityFormula k pol _).mp hc hΩ hAC rfl rfl rfl hφ hs
  let := hΩ.inaccessible.1
  have horder := (woodinSparseStageCode_valid hΩ hAC (subset_refl Ω)).system.order.preorder Ω (mem_succ_self Ω)
  have hleft := (classForcingFormula_regular (IsLowRankForcingName P Ω) (by definability) horder
    (domainTruthFormula pol k) (codedForcingArguments ∅ n φ s)).1
  apply mem_ext
  intro p
  constructor
  · intro hp
    exact (hh p (hleft p hp)).mp hp
  · intro hp
    exact (hh p (internalForcingSet_subset P R D n φ s p hp)).mpr hp

/-- W05 with a fixed code for the requested polarity and formula, read
condition by condition against the actual internally coded forcing relation. -/
theorem woodinCodedForcingFormula_rank_internal {Ω : V} (hΩ : IsWoodinSupercompact Ω)
    (hAC : ¬InternalChoice V) (k : ℕ) (pol : LevyPolarity) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ p n φ s : SetDomain (hierarchy Ω),
      IsLevyFormulaCode pol (k + 1) n.val φ.val →
      s.val ∈ lowRankNameSet ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) Ω ^ n.val →
      ((woodinCodedForcingFormula k).Evalb ![p, woodinForcingCode pol n φ, s] ↔
        p.val ∈ internalForcingSet
          ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
          ((forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω)
          (lowRankNameSet ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) Ω) n.val φ.val s.val) := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  intro p n φ s hφ hs
  have hsN : IsNameSequence ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) s.val := by
    intro i hi
    exact ((mem_lowRankNameSet _ _ _).mp (function_value_mem hs (domain_eq_of_mem_function hs ▸ hi))).2
  have he := woodinCodedForcingFormula_rank hΩ hAC k pol p n φ s hsN
  rwa [woodinSparse_codedForcing_eq_internal hΩ hAC hφ hs] at he
end ZFVP
