import ZFVP.SetTheory.ForcingAutomorphisms
import ZFVP.ModelTheory.ForcingUniqueName
import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.ModelTheory.ForcingLeastRankNameBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def tailFunctionValueForcing (P R f τ σ : V) : V :=
  forcingFormula P R functionValueFormula (standardTuple ![f, τ, σ])

instance tailFunctionValueForcing_definable (P R f : V) :
    ℒₛₑₜ-function₂[V] (tailFunctionValueForcing P R f) := by
  unfold tailFunctionValueForcing
  simp only [standardTuple]
  definability

/-- Apply a named function to a named argument without selecting a witness name. -/
noncomputable def tailFunctionValueName (P R f τ : V) : V :=
  forcingUniqueName P R (tailFunctionValueForcing P R f) (by infer_instance) τ

instance tailFunctionValueName_definable (P R f : V) :
    ℒₛₑₜ-function₁[V] (tailFunctionValueName P R f) := by
  unfold tailFunctionValueName
  infer_instance

theorem tailFunctionValueName_isName (P R f τ : V) :
    IsForcingName P (tailFunctionValueName P R f τ) :=
  forcingUniqueName_isName _ _ _ _ _

noncomputable def normalizedTailFunctionValueName (P R top f τ : V) : V :=
  forcingLeastRankName P R top (tailFunctionValueName P R f τ)

theorem normalizedTailFunctionValueName_isName {P R top f τ : V}
    (hR : IsForcingPreorder P R) (ht : top ∈ P) :
    IsForcingName P (normalizedTailFunctionValueName P R top f τ) :=
  forcingLeastRankName_isName hR ht (tailFunctionValueName_isName _ _ _ _)

theorem normalizedTailFunctionValueName_normalized {P R top f τ : V}
    (hR : IsForcingPreorder P R) (ht : top ∈ P) :
    forcingLeastRankName P R top (normalizedTailFunctionValueName P R top f τ) =
      normalizedTailFunctionValueName P R top f τ :=
  forcingLeastRankName_idempotent hR ht (tailFunctionValueName_isName _ _ _ _)

/-- A forced bound on the image value suffices for the normalized tail pool rank. -/
theorem normalizedTailFunctionValueName_mem_hierarchy {P R top f τ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hb : top ∈ forcingFormula P R nameInHierarchyFormula
      (standardTuple ![tailFunctionValueName P R f τ, checkName top δ])) :
    normalizedTailFunctionValueName P R top f τ ∈ hierarchy δ :=
  forcingLeastRankName_mem_of_forced_rank hR ht hδ hP ht.1
    (tailFunctionValueName_isName _ _ _ _) hb

namespace ForcingContext

theorem tailFunctionValueForcing_truth (A : ForcingContext V)
    (f τ σ : ForcingName A.P) :
    GenericMeets A.G (tailFunctionValueForcing A.P A.R f.val τ.val σ.val) ↔
      IsFunction (A.ofName f) ∧ (A.ofName f) ‘ (A.ofName τ) = A.ofName σ :=
  (A.formula_truth functionValueFormula ![f, τ, σ]).symm.trans (eval_functionValueFormula _)

theorem tailFunctionValueName_value (A : ForcingContext V)
    (f τ : ForcingName A.P) (hf : IsFunction (A.ofName f)) :
    A.ofName ⟨tailFunctionValueName A.P A.R f.val τ.val,
      tailFunctionValueName_isName _ _ _ _⟩ = (A.ofName f) ‘ (A.ofName τ) := by
  apply A.uniqueName_value (tailFunctionValueForcing A.P A.R f.val) (by infer_instance)
    τ.val (fun x ↦ IsFunction (A.ofName f) ∧ (A.ofName f) ‘ (A.ofName τ) = x)
  · exact fun σ ↦ A.tailFunctionValueForcing_truth f τ σ
  · exact fun x y hx hy ↦ hx.2.symm.trans hy.2
  · exact ⟨hf, rfl⟩

theorem normalizedTailFunctionValueName_value (A : ForcingContext V)
    (f τ : ForcingName A.P) (hf : IsFunction (A.ofName f)) (ht : A.one ∈ A.G) :
    A.ofName ⟨normalizedTailFunctionValueName A.P A.R A.one f.val τ.val,
      normalizedTailFunctionValueName_isName A.order A.top.1⟩ =
      (A.ofName f) ‘ (A.ofName τ) := by
  exact (A.leastRankName_value ht ⟨tailFunctionValueName A.P A.R f.val τ.val,
    tailFunctionValueName_isName _ _ _ _⟩).trans (A.tailFunctionValueName_value f τ hf)

/-- Named inverses compose to the original tail value in every generic extension. -/
theorem normalizedTailFunctionValueName_inverse_value (A : ForcingContext V)
    (f g τ : ForcingName A.P) (hf : IsFunction (A.ofName f))
    (hg : IsFunction (A.ofName g)) (ht : A.one ∈ A.G)
    (hi : (A.ofName g) ‘ ((A.ofName f) ‘ (A.ofName τ)) = A.ofName τ) :
    A.ofName ⟨normalizedTailFunctionValueName A.P A.R A.one g.val
      (normalizedTailFunctionValueName A.P A.R A.one f.val τ.val),
      normalizedTailFunctionValueName_isName A.order A.top.1⟩ = A.ofName τ := by
  let σ : ForcingName A.P :=
    ⟨normalizedTailFunctionValueName A.P A.R A.one f.val τ.val,
      normalizedTailFunctionValueName_isName A.order A.top.1⟩
  exact (A.normalizedTailFunctionValueName_value g σ hg ht).trans
    ((congrArg (fun x ↦ (A.ofName g) ‘ x)
      (A.normalizedTailFunctionValueName_value f τ hf ht)).trans hi)

theorem normalizedTailFunctionValueName_automorphism_inverse (A : ForcingContext V)
    (f g τ : ForcingName A.P) {Q S : A.Model}
    (hf : IsForcingAutomorphism Q S (A.ofName f))
    (hg : A.ofName g = converseGraph (A.ofName f))
    (hτ : A.ofName τ ∈ Q) (ht : A.one ∈ A.G) :
    A.ofName ⟨normalizedTailFunctionValueName A.P A.R A.one g.val
      (normalizedTailFunctionValueName A.P A.R A.one f.val τ.val),
      normalizedTailFunctionValueName_isName A.order A.top.1⟩ = A.ofName τ := by
  have hgfun : IsFunction (A.ofName g) := by
    rw [hg]
    exact IsFunction.of_mem (forcingAutomorphism_inverse hf).1
  apply A.normalizedTailFunctionValueName_inverse_value f g τ
    (IsFunction.of_mem hf.1) hgfun ht
  rw [hg]
  exact converseGraph_value_value hf.1 hf.2.1 hτ

theorem normalizedTailFunctionValueName_automorphism_order (A : ForcingContext V)
    (f τ σ : ForcingName A.P) {Q S : A.Model}
    (hf : IsForcingAutomorphism Q S (A.ofName f))
    (hτ : A.ofName τ ∈ Q) (hσ : A.ofName σ ∈ Q) (ht : A.one ∈ A.G) :
    ⟨A.ofName ⟨normalizedTailFunctionValueName A.P A.R A.one f.val τ.val,
        normalizedTailFunctionValueName_isName A.order A.top.1⟩,
      A.ofName ⟨normalizedTailFunctionValueName A.P A.R A.one f.val σ.val,
        normalizedTailFunctionValueName_isName A.order A.top.1⟩⟩ₖ ∈ S ↔
      ⟨A.ofName τ, A.ofName σ⟩ₖ ∈ S := by
  rw [A.normalizedTailFunctionValueName_value f τ (IsFunction.of_mem hf.1) ht,
    A.normalizedTailFunctionValueName_value f σ (IsFunction.of_mem hf.1) ht]
  exact (hf.2.2.2 _ hτ _ hσ).symm

end ForcingContext
end ZFVP


