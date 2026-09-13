import ZFVP.ModelTheory.UniformForcingDefinitions
import ZFVP.ModelTheory.WoodinSparseCodedForcingReadout
import ZFVP.ModelTheory.WoodinSparseStandardFormulaTruth
import ZFVP.ModelTheory.WoodinSparseEndpointZFC
import ZFVP.ModelTheory.LocalPartialTruthCorrectness
import ZFVP.SetTheory.EndExtensionLevy

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem sparseCodedForcingSet_truth (A : ForcingContext V) {δ : V}
    (hδ : IsChoicelessInaccessible δ) (hone : A.one = ∅)
    (hcov : ∀ x ∈ hierarchy (A.check δ), ∃ τ : ForcingName A.P,
      τ.val ∈ hierarchy δ ∧ x = A.ofName τ)
    [Nonempty (SetDomain (hierarchy (A.check δ)))]
    [(SetDomain (hierarchy (A.check δ)))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    {k : ℕ} {pol : LevyPolarity} {n φ s : V}
    (hφ : IsLevyFormulaCode pol (k + 1) n φ)
    (hs : s ∈ lowRankNameSet A.P δ ^ n) :
    GenericMeets A.G (sparseCodedForcingSet A.P A.R δ k pol n φ s) ↔
      MembershipSatisfies (hierarchy (A.check δ)) (A.check n) (A.check φ)
        (A.sequenceValue s (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hs)) := by
  let := hδ.1
  let := rankDomain_nonempty hδ.2.1
  let := hδ.rankCriterion.models_zf
  let := hierarchy_transitive δ
  let := hierarchy_transitive (A.check δ)
  let := TransitiveZF.sequenceSupport (hierarchy δ)
  have hn : n ∈ hierarchy δ := IsCodingSupport.natural_mem hφ.context
  have he : φ ∈ hierarchy δ := (kpair_components_mem_transitive
    (levyFormulaFamily_subset_support (k + 1) pol (hierarchy δ) _ hφ)).2
  have hsr : s ∈ hierarchy δ := function_mem_sequenceSupport
    (fun x hx ↦ ((mem_lowRankNameSet A.P δ x).mp hx).1) hφ.context hs
  have ho : A.one ∈ hierarchy δ := by
    rw [hone]
    exact (TransitiveZF.empty_val (hierarchy δ)) ▸ (∅ : SetDomain (hierarchy δ)).property
  let hsN := A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hs
  let v : Fin 3 → ForcingName A.P := ![
    ⟨checkName A.one n, checkName_isName A.top.1 n⟩,
    ⟨checkName A.one φ, checkName_isName A.top.1 φ⟩,
    ⟨sequenceName A.one s, sequenceName_isName A.top.1 hsN⟩]
  have hv : ∀ i, (v i).val ∈ hierarchy δ := by
    exact Fin.cases (hδ.checkName_mem_hierarchy ho hn)
      (fun i ↦ Fin.cases (hδ.checkName_mem_hierarchy ho he)
        (fun i ↦ Fin.cases (hδ.sequenceName_mem_hierarchy ho hsr) (fun j ↦ Fin.elim0 j) i) i)
  let w : Fin 3 → SetDomain (hierarchy (A.check δ)) := fun i ↦
    ⟨A.ofName (v i), A.ofName_mem_checked_hierarchy _ (hv i)⟩
  have ht := A.rankName_formula_truth_of_coverage hcov (domainTruthFormula pol k) v hv
  have hargs : standardTuple (fun i ↦ (v i).val) = codedForcingArguments ∅ n φ s := by
    unfold codedForcingArguments
    congr 1
    funext i
    exact Fin.cases (by change checkName A.one n = checkName ∅ n; rw [hone])
      (fun i ↦ Fin.cases (by change checkName A.one φ = checkName ∅ φ; rw [hone])
        (fun i ↦ Fin.cases (by change sequenceName A.one s = sequenceName ∅ s; rw [hone])
          (fun j ↦ Fin.elim0 j) i) i) i
  rw [hargs] at ht
  change (domainTruthFormula pol k).Evalb w ↔ _ at ht
  have hcheck : IsLevyFormulaCode pol (k + 1) (A.check n) (A.check φ) := by
    have hh := A.checkEmbedding.deltaOne_defined
      (sigmaOneLevyCodeFormula_sigmaOne pol (k + 1))
      (piOneLevyCodeFormula_piOne pol (k + 1))
      (fun b : Fin 2 → V ↦ IsLevyFormulaCode pol (k + 1) (b 0) (b 1))
      (fun b : Fin 2 → A.Model ↦ IsLevyFormulaCode pol (k + 1) (b 0) (b 1)) ![n, φ]
    exact hh.mp hφ
  have hnval : (w 0).val = A.check n := rfl
  have heval : (w 1).val = A.check φ := rfl
  have hsval : (w 2).val = A.sequenceValue s hsN := rfl
  have hwφ := (TransitiveZF.levyCode_iff (hierarchy (A.check δ)) pol (k + 1) (w 0) (w 1)).mpr
    (show IsLevyFormulaCode pol (k + 1) (w 0).val (w 1).val from hcheck)
  have hwf : IsFunction (w 2) ∧ domain (w 2) = w 0 := by
    apply (TransitiveZF.function_on_iff (hierarchy (A.check δ)) (w 2) (w 0)).mpr
    change IsFunction (A.sequenceValue s hsN) ∧ domain (A.sequenceValue s hsN) = A.check n
    exact ⟨inferInstance, (A.sequenceValue_domain s hsN).trans (congrArg A.check (domain_eq_of_mem_function hs))⟩
  have hw := TransitiveZF.domainTruth_iff (hierarchy (A.check δ)) (w 0) (w 1) (w 2) hwφ hwf
  have hwvec : w = ![w 0, w 1, w 2] := by
    funext i
    exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun j ↦ Fin.elim0 j) i) i) i
  have heval : (domainTruthFormula pol k).Evalb w ↔ DomainTruth pol k (w 0) (w 1) (w 2) := by
    conv_lhs => rw [hwvec]
    exact eval_domainTruthFormula pol k (w 0) (w 1) (w 2)
  exact ht.symm.trans (heval.trans hw)

end ForcingContext

variable {Ω : V} [IsOrdinal Ω]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG

/-- The fixed-code relation reads actual internally coded truth at the sparse
endpoint; all name coverage and rank-model hypotheses are discharged. -/
theorem woodinSparse_codedForcing_truth {k : ℕ} {pol : LevyPolarity} {n φ s : V}
    (hφ : IsLevyFormulaCode pol (k + 1) n φ)
    (hs : s ∈ lowRankNameSet (E).P Ω ^ n) :
    GenericMeets (E).G (sparseCodedForcingSet (E).P (E).R Ω k pol n φ s) ↔
      MembershipSatisfies (hierarchy ((E).check Ω)) ((E).check n) ((E).check φ)
        ((E).sequenceValue s ((E).nameSequence_of_mem_function ((E).lowRankNameSet_names Ω) hs)) := by
  let := WoodinSparseEndpointModel.rankModel_nonempty hΩ hAC hG
  let := WoodinSparseEndpointModel.rankModel_models_zf hΩ hAC hG
  exact (E).sparseCodedForcingSet_truth hΩ.inaccessible
    (woodinSparseGenericContext_top hΩ hAC (subset_refl Ω) hG)
    (woodinSparseGenericContext_endpoint_low_name_coverage hΩ hAC hG) hφ hs

/-- The fixed-code relation and the internal forcing relation have the same
truth witnesses in every actual sparse generic. -/
theorem woodinSparse_codedForcing_internalForcing {k : ℕ} {pol : LevyPolarity} {n φ s : V}
    (hφ : IsLevyFormulaCode pol (k + 1) n φ)
    (hs : s ∈ lowRankNameSet (E).P Ω ^ n) :
    GenericMeets (E).G (sparseCodedForcingSet (E).P (E).R Ω k pol n φ s) ↔
      GenericMeets (E).G (internalForcingSet (E).P (E).R (lowRankNameSet (E).P Ω) n φ s) :=
  (woodinSparse_codedForcing_truth hΩ hAC hG hφ hs).trans
    (woodinSparseGenericContext_endpoint_internalGenericTruth hΩ hAC hG hφ.membershipCode hs)

end ZFVP







