import ZFVP.ModelTheory.SaturatedWoodinPrefix
import ZFVP.SetTheory.ForcingIterandFormula

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def saturatedWoodinIterandFormula : SetTheorySemisentence 5 :=
  f“P R o κ δ. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !choicelessInaccessibleFormula δ ∧ P ∈ !hierarchyFormula δ ∧ κ ⊆ δ ∧
    (∀ p ∈ P, !(checkedUnaryForcingFormula regularCardinalFormula) P R o p κ) →
    ∀ Q S, !saturatedWoodinPrefixPosetNameFormula Q P R o κ δ →
      !saturatedWoodinPrefixOrderNameFormula S P R o κ δ → !forcingIterandFormula P R Q S (!isEmpty)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem saturatedWoodinPrefix_iterand_countable [Countable V] {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ])) :
    IsForcingIterand P R (saturatedWoodinPrefixPosetName P R one κ δ)
      (saturatedWoodinPrefixOrderName P R one κ δ) ∅ := by
  let Q : ForcingName P := ⟨saturatedWoodinPrefixPosetName P R one κ δ, saturatedWoodinPrefixPosetName_isName _ _ _ _ _⟩
  let S : ForcingName P := ⟨saturatedWoodinPrefixOrderName P R one κ δ, saturatedWoodinPrefixOrderName_isName _ _ _ _ _⟩
  let t : ForcingName P := ⟨∅, empty_forcingName P⟩
  refine ⟨Q.property, S.property, t.property,
    fun p hp ↦ reverseInclusionOrderName_preorder hR htop hp Q, ?_⟩
  intro p hp
  apply forcingFormula_of_all_generics hR htop hp forcingTopFormula ![Q, S, t]
  intro G hG hpG
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  let cκ : ForcingName P := ⟨checkName one κ, checkName_isName htop.1 _⟩
  have hk : IsRegularCardinal (A.check κ) :=
    (Defined.eval_iff _).mp ((A.formula_truth regularCardinalFormula ![cκ]).mpr ⟨p, hpG, hκ p hp⟩)
  have ht : A.ofName t = ∅ := by
    apply mem_ext
    intro x
    rw [A.mem_ofName_iff]
    simp [t]
  apply (Defined.eval_iff _).mpr
  change IsForcingTop (A.ofName Q) (A.ofName S) (A.ofName t)
  rw [show A.ofName Q = woodinCollapse (A.check κ) (A.check δ) from A.saturatedWoodinPosetName_value hδ hP hκδ,
    show A.ofName S = woodinCollapseOrder (A.check κ) (A.check δ) from A.saturatedWoodinOrderName_value hδ hP hκδ, ht]
  exact woodinCollapse_top (hk.2.1 ∅ (by simp)) _

private theorem forall_three_eq {β : Type*} (a b c : β) (F : β → β → β → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩

private theorem forall_five_eq {β : Type*} (a b c d e : β) (F : β → β → β → β → β → Prop) :
    (∀ u v w x y, u = a → v = b → w = c → x = d → y = e → F u v w x y) ↔ F a b c d e :=
  ⟨fun h ↦ h a b c d e rfl rfl rfl rfl rfl,
    fun h u v w x y hu hv hw hx hy ↦ by subst u v w x y; exact h⟩

private theorem forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

theorem eval_saturatedWoodinIterandFormula (v : Fin 5 → V) : saturatedWoodinIterandFormula.Evalb v ↔
    (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsChoicelessInaccessible (v 4) → v 0 ∈ hierarchy (v 4) → v 3 ⊆ v 4 →
      (∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) regularCardinalFormula (standardTuple ![checkName (v 2) (v 3)])) →
      IsForcingIterand (v 0) (v 1) (saturatedWoodinPrefixPosetName (v 0) (v 1) (v 2) (v 3) (v 4))
        (saturatedWoodinPrefixOrderName (v 0) (v 1) (v 2) (v 3) (v 4)) ∅) := by
  simp [saturatedWoodinIterandFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff,
    Fin.forall_fin_succ, forall_three_eq, forall_five_eq, forall_six_eq]

private theorem saturatedWoodinIterand_valid (v : Fin 5 → V) : saturatedWoodinIterandFormula.Evalb v := by
  apply eval_of_countable_zf saturatedWoodinIterandFormula
  intro W _ _ _ _ w
  exact (eval_saturatedWoodinIterandFormula w).mpr
    (fun hR htop hδ hP hκδ hκ ↦ saturatedWoodinPrefix_iterand_countable hR htop hδ hP hκδ hκ)

private theorem saturatedWoodinIterand_transfer (v : Fin 5 → V)
    (hR : IsForcingPreorder (v 0) (v 1)) (htop : IsForcingTop (v 0) (v 1) (v 2))
    (hδ : IsChoicelessInaccessible (v 4)) (hP : v 0 ∈ hierarchy (v 4)) (hκδ : v 3 ⊆ v 4)
    (hκ : ∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) regularCardinalFormula (standardTuple ![checkName (v 2) (v 3)])) :
    IsForcingIterand (v 0) (v 1) (saturatedWoodinPrefixPosetName (v 0) (v 1) (v 2) (v 3) (v 4))
      (saturatedWoodinPrefixOrderName (v 0) (v 1) (v 2) (v 3) (v 4)) ∅ :=
  (eval_saturatedWoodinIterandFormula v).mp (saturatedWoodinIterand_valid v) hR htop hδ hP hκδ hκ

theorem saturatedWoodinPrefix_iterand {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ])) :
    IsForcingIterand P R (saturatedWoodinPrefixPosetName P R one κ δ)
      (saturatedWoodinPrefixOrderName P R one κ δ) ∅ :=
  saturatedWoodinIterand_transfer ![P, R, one, κ, δ] hR htop hδ hP hκδ hκ

end ZFVP
