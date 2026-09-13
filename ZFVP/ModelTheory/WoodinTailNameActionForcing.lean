import ZFVP.ModelTheory.WoodinTailNameAction
import ZFVP.ModelTheory.ForcingAtomicSemanticConsequence
import ZFVP.ModelTheory.NormalizedTwoStepComparison

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def tailAutomorphismFormula : SetTheorySemisentence 3 :=
  f“Q S f. f ∈ !function.dfn Q Q ∧ !Injective.dfn f ∧ !range.dfn f = Q ∧
    ∀ x ∈ Q, ∀ y ∈ Q,
      (!kpair.dfn x y ∈ S ↔ !kpair.dfn (!value.dfn f x) (!value.dfn f y) ∈ S)”

def tailInversePairFormula : SetTheorySemisentence 4 :=
  f“Q S f g. !tailAutomorphismFormula Q S f ∧ !tailAutomorphismFormula Q S g ∧
    ∀ x ∈ Q, !value.dfn g (!value.dfn f x) = x”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance tailAutomorphismFormula_defined :
    Defined (fun v : Fin 3 → V ↦ IsForcingAutomorphism (v 0) (v 1) (v 2))
      tailAutomorphismFormula := ⟨fun v ↦ by simp [tailAutomorphismFormula, IsForcingAutomorphism]⟩

instance tailInversePairFormula_defined :
    Defined (fun v : Fin 4 → V ↦ IsForcingAutomorphism (v 0) (v 1) (v 2) ∧
      IsForcingAutomorphism (v 0) (v 1) (v 3) ∧ ∀ x ∈ v 0, (v 3) ‘ ((v 2) ‘ x) = x)
      tailInversePairFormula := ⟨fun v ↦ by simp [tailInversePairFormula]⟩

theorem normalizedTailFunctionValueName_forced_inverse_countable [Countable V]
    {P R top : V} (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (Q S f g τ : ForcingName P)
    (hf : top ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![Q.val, S.val, f.val, g.val]))
    (hτ : top ∈ atomicMembership P R τ.val Q.val) :
    top ∈ atomicEquality P R
      (normalizedTailFunctionValueName P R top g.val
        (normalizedTailFunctionValueName P R top f.val τ.val)) τ.val := by
  apply atomicEquality_of_all_generics hR ht ht.1
    ⟨_, normalizedTailFunctionValueName_isName hR ht.1⟩ τ
  intro G hG htG
  let A : ForcingContext V := ⟨P, R, top, G, hR, ht, hG⟩
  have h := (Defined.eval_iff _).mp
    ((A.formula_truth tailInversePairFormula ![Q, S, f, g]).mpr ⟨top, htG, hf⟩)
  have hm : A.ofName τ ∈ A.ofName Q :=
    (forcingQuotientMk_mem_iff P R G hR hG.1 τ Q).mpr ⟨top, htG, hτ⟩
  exact A.normalizedTailFunctionValueName_inverse_value f g τ
    (IsFunction.of_mem h.1.1) (IsFunction.of_mem h.2.1.1) htG (h.2.2 _ hm)

end ZFVP
