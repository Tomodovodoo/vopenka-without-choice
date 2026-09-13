import ZFVP.ModelTheory.SaturatedTwoStepTransfer
import ZFVP.ModelTheory.WoodinCollapseUnionName
import ZFVP.ModelTheory.WoodinPrefixNameFormulas
import ZFVP.ModelTheory.ForcingSmallInaccessible
import ZFVP.SetTheory.WoodinCollapseClosedCut

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def saturatedWoodinPrefixPosetNameFormula : SetTheorySemisentence 6 :=
  f“Q P R o κ δ. ∀ U W, !(parameterRecursionFormula forcingNameHierarchyStepFormula) U P δ →
    !woodinPrefixPosetNameFormula W P R o κ δ → !forcingSaturatedNameFormula Q P R U W”

def saturatedWoodinPrefixOrderNameFormula : SetTheorySemisentence 6 :=
  f“S P R o κ δ. ∀ Q, !saturatedWoodinPrefixPosetNameFormula Q P R o κ δ → !reverseInclusionOrderNameFormula S P R Q”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def saturatedWoodinPrefixPosetName (P R one κ δ : V) : V :=
  forcingSaturatedName P R (forcingNameHierarchy P δ) (woodinPrefixPosetName P R one κ δ)

noncomputable def saturatedWoodinPrefixOrderName (P R one κ δ : V) : V :=
  reverseInclusionOrderName P R (saturatedWoodinPrefixPosetName P R one κ δ)

private theorem forall_three_eq {β : Type*} (a b c : β) (F : β → β → β → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩

private theorem forall_four_eq {β : Type*} (a b c d : β) (F : β → β → β → β → Prop) :
    (∀ u v w x, u = a → v = b → w = c → x = d → F u v w x) ↔ F a b c d :=
  ⟨fun h ↦ h a b c d rfl rfl rfl rfl, fun h u v w x hu hv hw hx ↦ by subst u v w x; exact h⟩

private theorem forall_five_eq {β : Type*} (a b c d e : β) (F : β → β → β → β → β → Prop) :
    (∀ u v w x y, u = a → v = b → w = c → x = d → y = e → F u v w x y) ↔ F a b c d e :=
  ⟨fun h ↦ h a b c d e rfl rfl rfl rfl rfl,
    fun h u v w x y hu hv hw hx hy ↦ by subst u v w x y; exact h⟩

private theorem forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

instance saturatedWoodinPrefixPosetNameFormula_defined :
    ℒₛₑₜ-function₅[V] saturatedWoodinPrefixPosetName via saturatedWoodinPrefixPosetNameFormula :=
  ⟨fun v ↦ by
    simp [saturatedWoodinPrefixPosetNameFormula, saturatedWoodinPrefixPosetName,
      Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ,
      forall_three_eq, forall_five_eq, forall_six_eq]⟩

instance saturatedWoodinPrefixOrderNameFormula_defined :
    ℒₛₑₜ-function₅[V] saturatedWoodinPrefixOrderName via saturatedWoodinPrefixOrderNameFormula :=
  ⟨fun v ↦ by
    simp [saturatedWoodinPrefixOrderNameFormula, saturatedWoodinPrefixOrderName,
      Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ, forall_four_eq, forall_six_eq]⟩

instance saturatedWoodinPrefixPosetName_definable : Language.DefinableFunction ℒₛₑₜ
    (fun v : Fin 5 → V ↦ saturatedWoodinPrefixPosetName (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  saturatedWoodinPrefixPosetNameFormula_defined.to_definable

instance saturatedWoodinPrefixOrderName_definable : Language.DefinableFunction ℒₛₑₜ
    (fun v : Fin 5 → V ↦ saturatedWoodinPrefixOrderName (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  saturatedWoodinPrefixOrderNameFormula_defined.to_definable

theorem saturatedWoodinPrefixPosetName_isName (P R one κ δ : V) :
    IsForcingName P (saturatedWoodinPrefixPosetName P R one κ δ) := forcingSaturatedName_isName _ _ _ _

theorem saturatedWoodinPrefixOrderName_isName (P R one κ δ : V) :
    IsForcingName P (saturatedWoodinPrefixOrderName P R one κ δ) := reverseInclusionOrderName_isName _ _ _

theorem saturatedWoodinPrefixPosetName_mem_hierarchy {P R one κ δ θ : V}
    (hθ : IsChoicelessInaccessible θ) (hP : P ∈ hierarchy θ) (hδ : δ ∈ θ) :
    saturatedWoodinPrefixPosetName P R one κ δ ∈ hierarchy θ := by
  let := hθ.1
  exact subset_mem_hierarchy_limit hθ.rankCriterion.2.2.1
    (prod_mem_hierarchy_limit hθ.rankCriterion.2.2.1 (forcingNameHierarchy_mem_hierarchy hθ hP hδ) hP)
    (forcingSaturatedName_subset _ _ _ _)

namespace ForcingContext

noncomputable def saturatedWoodinPosetName (A : ForcingContext V) (κ δ : V) : ForcingName A.P :=
  ⟨saturatedWoodinPrefixPosetName A.P A.R A.one κ δ, saturatedWoodinPrefixPosetName_isName _ _ _ _ _⟩

noncomputable def saturatedWoodinOrderName (A : ForcingContext V) (κ δ : V) : ForcingName A.P :=
  ⟨saturatedWoodinPrefixOrderName A.P A.R A.one κ δ, saturatedWoodinPrefixOrderName_isName _ _ _ _ _⟩

theorem saturatedWoodinPosetName_value (A : ForcingContext V) {κ δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hκ : κ ⊆ δ) :
    A.ofName (A.saturatedWoodinPosetName κ δ) = woodinCollapse (A.check κ) (A.check δ) := by
  let := hδ.1
  let cκ : ForcingName A.P := ⟨checkName A.one κ, checkName_isName A.top.1 _⟩
  let cδ : ForcingName A.P := ⟨checkName A.one δ, checkName_isName A.top.1 _⟩
  let : IsOrdinal (A.ofName cδ) := by change IsOrdinal (A.check δ); infer_instance
  have hc : A.ofName (A.collapseName cκ cδ) = woodinCollapse (A.check κ) (A.check δ) :=
    A.collapseName_value_of_ordinal cκ cδ
  have hcover : A.ofName (A.collapseName cκ cδ) ⊆ hierarchy (A.check δ) := by
    rw [hc]
    exact fun _ hp ↦ woodinCollapse_condition_mem_hierarchy (A.check_inaccessible_of_small hδ hP).regular
      ((A.checkEmbedding.subset_iff _ _).mpr hκ) hp
  exact (A.saturatedName_value_of_hierarchy δ (A.collapseName cκ cδ) hcover).trans hc

theorem saturatedWoodinOrderName_value (A : ForcingContext V) {κ δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hκ : κ ⊆ δ) :
    A.ofName (A.saturatedWoodinOrderName κ δ) = woodinCollapseOrder (A.check κ) (A.check δ) := by
  change A.ofName (A.reverseOrderName (A.saturatedWoodinPosetName κ δ)) = _
  rw [A.reverseOrderName_value, A.saturatedWoodinPosetName_value hδ hP hκ]
  rfl

end ForcingContext

theorem saturatedWoodinPrefix_union_bound {P R one κ δ α p f : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P)
    (hακ : α ∈ κ) (hαδ : α ∈ internalCofinality δ) (h0δ : (∅ : V) ∈ δ)
    (hκ : p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hDC : p ∈ forcingFormula P R dependentChoiceAtFormula (standardTuple ![checkName one α]))
    (hf : IsForcingDirectedFamily (twoStepConditions P R (saturatedWoodinPrefixPosetName P R one κ δ) ∅)
      (twoStepOrder P R (saturatedWoodinPrefixPosetName P R one κ δ) (saturatedWoodinPrefixOrderName P R one κ δ) ∅) α f)
    (hpbelow : ∀ i ∈ α, ⟨p, kpair.π₁ (f ‘ i)⟩ₖ ∈ R) :
    twoStepUnionBound α p f ∈ twoStepConditions P R (saturatedWoodinPrefixPosetName P R one κ δ) ∅ ∧
      ∀ i ∈ α, ⟨twoStepUnionBound α p f, f ‘ i⟩ₖ ∈
        twoStepOrder P R (saturatedWoodinPrefixPosetName P R one κ δ) (saturatedWoodinPrefixOrderName P R one κ δ) ∅ := by
  let Q : ForcingName P := ⟨woodinPrefixPosetName P R one κ δ, woodinCollapseName_isName _ _ _ _⟩
  let N : ForcingName P := ⟨saturatedWoodinPrefixPosetName P R one κ δ, saturatedWoodinPrefixPosetName_isName _ _ _ _ _⟩
  let S : ForcingName P := ⟨saturatedWoodinPrefixOrderName P R one κ δ, saturatedWoodinPrefixOrderName_isName _ _ _ _ _⟩
  exact saturated_twoStep_union_bound hR htop Q S hαδ
    ((mem_forcingNameHierarchy P δ ∅).mpr ⟨∅, h0δ, by simp⟩) hp
    (woodinPrefix_forces_unionClosedAt hR htop hp hακ hκ hDC)
    (reverseInclusionOrderName_forces hR htop hp N) hf hpbelow

end ZFVP
