import ZFVP.ModelTheory.SingularWeaklyLSCollapseDC
import ZFVP.ModelTheory.CountableZFTransfer
import ZFVP.ModelTheory.ForcingSemanticConsequence
import ZFVP.ModelTheory.ForcingReverseOrderName
import ZFVP.SetTheory.LowenheimSkolemDictionary
import ZFVP.SetTheory.ChoiceDictionary
import ZFVP.SetTheory.FiniteDictionary
import ZFVP.Syntax.ForcingTranslationSemantics

/-! The unrestricted forcing and ZF-derivability forms of Usuba Proposition 3.6.
The fixed sentence describes the actual finite collapse of the rank segment.
Its countable-ground validity transfers by first-order elementarity. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rankCollapseConditionsFormula : SetTheorySemisentence 2 :=
  f“P κ. ∀ p, p ∈ P ↔ p ⊆ !prod.dfn (!isω) (!hierarchyFormula κ) ∧
    !IsFunction.dfn p ∧ !internallyFiniteFormula (!domain.dfn p)”

def singularWeaklyLSForcesDCSentence : SetTheorySentence :=
  f“∀ κ, !weaklyLSCardinalFormula κ → !internalCofinalityFormula κ ∈ κ →
    ∀ P R, !rankCollapseConditionsFormula P κ →
      !piOneReverseInclusionOrderFormula R P → ∀ p ∈ P,
        !(ordinaryForcingTranslation dependentChoiceSentence) P R P P p (!isEmpty)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance rankCollapseConditionsFormula_defined :
    ℒₛₑₜ-function₁[V] (fun κ ↦ collapseConditions (hierarchy κ))
      via rankCollapseConditionsFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [rankCollapseConditionsFormula, collapseConditions, mem_finitePartialFunctions]⟩

theorem eval_singularWeaklyLSForcesDCSentence (v : Fin 0 → V) :
    singularWeaklyLSForcesDCSentence.Evalb v ↔
      ∀ κ : V, IsWeaklyLSCardinal κ → internalCofinality κ ∈ κ →
        ∀ p ∈ collapseConditions (hierarchy κ),
          p ∈ forcingFormula (collapseConditions (hierarchy κ))
            (collapseOrder (hierarchy κ)) dependentChoiceSentence ∅ := by
  let := ordinaryForcingTranslation_defined (V := V) dependentChoiceSentence
  simp [singularWeaklyLSForcesDCSentence, collapseOrder,
    Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ,
    Matrix.empty_eq]
  constructor
  · intro h κ hκ hsing p hp
    exact h κ hκ hsing p hp _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  · intro h κ hκ hsing p hp
    rintro _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    exact h κ hκ hsing _ hp

theorem singularWeaklyLS_forcesDC_countable [Countable V] {κ p : V}
    (hκ : IsWeaklyLSCardinal κ) (hsing : internalCofinality κ ∈ κ)
    (hp : p ∈ collapseConditions (hierarchy κ)) :
    p ∈ forcingFormula (collapseConditions (hierarchy κ))
      (collapseOrder (hierarchy κ)) dependentChoiceSentence ∅ := by
  have ht := forcingFormula_of_all_generics (collapse_poset (hierarchy κ)).1
    (collapse_top (hierarchy κ)) hp dependentChoiceSentence Fin.elim0
    (fun G hG _ ↦ by
      apply (dependentChoiceSentence_defined.iff _).mpr
      exact CollapseModel.dependentChoice_of_singular_weaklyLS hκ hsing hG)
  simpa [standardTuple] using ht

theorem singularWeaklyLSForcesDCSentence_valid (v : Fin 0 → V) :
    singularWeaklyLSForcesDCSentence.Evalb v := by
  apply eval_of_countable_zf singularWeaklyLSForcesDCSentence
  intro W _ _ _ _ w
  apply (eval_singularWeaklyLSForcesDCSentence w).mpr
  intro κ hκ hsing p hp
  exact singularWeaklyLS_forcesDC_countable hκ hsing hp

/-- Every condition forces DC in every ZF ground with the indicated cardinal. -/
theorem singularWeaklyLS_forcesDC {κ p : V}
    (hκ : IsWeaklyLSCardinal κ) (hsing : internalCofinality κ ∈ κ)
    (hp : p ∈ collapseConditions (hierarchy κ)) :
    p ∈ forcingFormula (collapseConditions (hierarchy κ))
      (collapseOrder (hierarchy κ)) dependentChoiceSentence ∅ :=
  (eval_singularWeaklyLSForcesDCSentence (![] : Fin 0 → V)).mp
    (singularWeaklyLSForcesDCSentence_valid _) κ hκ hsing p hp

/-- The generic extension conclusion no longer assumes an externally countable ground. -/
theorem CollapseModel.dependentChoice_of_singular_weaklyLS_unrestricted {κ : V}
    (hκ : IsWeaklyLSCardinal κ) (hsing : internalCofinality κ ∈ κ)
    {G : Set V} (hG : IsExternalForcingGeneric (collapseConditions (hierarchy κ))
      (collapseOrder (hierarchy κ)) G) :
    InternalDependentChoice (collapseContext (hierarchy κ) G hG).Model := by
  let M := collapseContext (hierarchy κ) G hG
  obtain ⟨p, hpG⟩ := hG.1.2.1
  have hp := singularWeaklyLS_forcesDC hκ hsing (hG.1.1 p hpG)
  have ht := (M.formula_truth dependentChoiceSentence Fin.elim0).mpr
    ⟨p, hpG, by simpa [standardTuple, M, collapseContext] using hp⟩
  exact (dependentChoiceSentence_defined.iff _).mp ht

theorem models_singularWeaklyLSForcesDCSentence :
    V↓[ℒₛₑₜ] ⊧ singularWeaklyLSForcesDCSentence := by
  simpa only [models_iff, Semiformula.Realize, Semiformula.Evalb] using
    singularWeaklyLSForcesDCSentence_valid (V := V) ![]

theorem zf_proves_singularWeaklyLS_forcesDC :
    𝗭𝗙 ⊢ singularWeaklyLSForcesDCSentence :=
  provable_of_models 𝗭𝗙 singularWeaklyLSForcesDCSentence
    (fun (M : Type) _ _ _ ↦ models_singularWeaklyLSForcesDCSentence (V := M))

end ZFVP
