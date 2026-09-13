import ZFVP.ModelTheory.SaturatedTwoStepBounds

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def binaryForcingTruthFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 5 :=
  f“p P R x y. !(ordinaryForcingTranslation φ) P R P P p
    (!assignmentPrependFormula (!(numeralFormula 1))
      (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) y) x)”

@[irreducible] def saturatedTwoStepBoundFormula : SetTheorySemisentence 10 :=
  f“P R o Q S δ α t p f. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingNameFormula P Q ∧ !forcingNameFormula P S ∧ !IsOrdinal.dfn δ ∧ α ∈ !internalCofinalityFormula δ →
    ∀ U N C T B, !(parameterRecursionFormula forcingNameHierarchyStepFormula) U P δ →
      !forcingSaturatedNameFormula N P R U Q → !twoStepConditionsFormula C P R N t →
      !twoStepOrderFormula T P R N S t → !twoStepUnionBoundFormula B α p f →
      t ∈ U → p ∈ P →
      !(binaryForcingTruthFormula forcingUnionClosedAtFormula) p P R Q (!checkNameFormula o α) →
      !(binaryForcingTruthFormula piOneReverseInclusionOrderFormula) p P R S N →
      !forcingDirectedFamilyFormula C T α f →
      (∀ i ∈ α, !kpair.dfn p (!kpair.π₁.dfn (!value.dfn f i)) ∈ R) →
      B ∈ C ∧ ∀ i ∈ α, !kpair.dfn B (!value.dfn f i) ∈ T”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance binaryForcingTruthFormula_defined (φ : SetTheorySemisentence 2) :
    Defined (fun v : Fin 5 → V ↦ v 0 ∈ forcingFormula (v 1) (v 2) φ
      (standardTuple ![v 3, v 4])) (binaryForcingTruthFormula φ) :=
  ⟨fun v ↦ by
    simp [binaryForcingTruthFormula, standardTuple, Semiformula.eval_nestFormulae,
      Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
    constructor
    · intro h
      exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    · rintro h a b c d e f rfl rfl rfl rfl rfl rfl
      exact h⟩

private theorem forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

private theorem forall_three_eq {β : Type*} (a b c : β) (F : β → β → β → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩

private theorem forall_five_eq {β : Type*} (a b c d e : β) (F : β → β → β → β → β → Prop) :
    (∀ u v w x y, u = a → v = b → w = c → x = d → y = e → F u v w x y) ↔ F a b c d e :=
  ⟨fun h ↦ h a b c d e rfl rfl rfl rfl rfl,
    fun h u v w x y hu hv hw hx hy ↦ by subst u v w x y; exact h⟩

private theorem forall_four_eq {β : Type*} (a b c d : β) (F : β → β → β → β → Prop) :
    (∀ u v w x, u = a → v = b → w = c → x = d → F u v w x) ↔ F a b c d :=
  ⟨fun h ↦ h a b c d rfl rfl rfl rfl, fun h u v w x hu hv hw hx ↦ by subst u v w x; exact h⟩

theorem eval_saturatedTwoStepBoundFormula (v : Fin 10 → V) : saturatedTwoStepBoundFormula.Evalb v ↔
    (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsForcingName (v 0) (v 3) → IsForcingName (v 0) (v 4) → IsOrdinal (v 5) →
      v 6 ∈ internalCofinality (v 5) →
      ∀ U N C T B, U = forcingNameHierarchy (v 0) (v 5) →
        N = forcingSaturatedName (v 0) (v 1) U (v 3) → C = twoStepConditions (v 0) (v 1) N (v 7) →
        T = twoStepOrder (v 0) (v 1) N (v 4) (v 7) → B = twoStepUnionBound (v 6) (v 8) (v 9) →
        v 7 ∈ U → v 8 ∈ v 0 →
        v 8 ∈ forcingFormula (v 0) (v 1) forcingUnionClosedAtFormula (standardTuple ![v 3, checkName (v 2) (v 6)]) →
        v 8 ∈ forcingFormula (v 0) (v 1) piOneReverseInclusionOrderFormula (standardTuple ![v 4, N]) →
        IsForcingDirectedFamily C T (v 6) (v 9) →
        (∀ i ∈ v 6, ⟨v 8, kpair.π₁ ((v 9) ‘ i)⟩ₖ ∈ v 1) →
        B ∈ C ∧ ∀ i ∈ v 6, ⟨B, (v 9) ‘ i⟩ₖ ∈ T) := by
  simp [saturatedTwoStepBoundFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff,
    Fin.forall_fin_succ, forall_six_eq, forall_three_eq, forall_five_eq, forall_four_eq]

private theorem saturatedTwoStepBound_valid (v : Fin 10 → V) : saturatedTwoStepBoundFormula.Evalb v := by
  apply eval_of_countable_zf saturatedTwoStepBoundFormula
  intro W _ _ _ _ w
  apply (eval_saturatedTwoStepBoundFormula w).mpr
  intro hR htop hQ hS hδ hα U N C T B hU hN hC hT hB ht hp hclosed horder hf hpbelow
  subst U N C T B
  let := hδ
  exact saturated_twoStep_union_bound_countable hR htop ⟨w 3, hQ⟩ ⟨w 4, hS⟩ hα ht hp hclosed horder hf hpbelow

private theorem saturatedTwoStepBound_transfer (v : Fin 10 → V)
    (hR : IsForcingPreorder (v 0) (v 1)) (htop : IsForcingTop (v 0) (v 1) (v 2))
    (hQ : IsForcingName (v 0) (v 3)) (hS : IsForcingName (v 0) (v 4)) (hδ : IsOrdinal (v 5))
    (hα : v 6 ∈ internalCofinality (v 5))
    (ht : v 7 ∈ forcingNameHierarchy (v 0) (v 5)) (hp : v 8 ∈ v 0)
    (hclosed : v 8 ∈ forcingFormula (v 0) (v 1) forcingUnionClosedAtFormula (standardTuple ![v 3, checkName (v 2) (v 6)]))
    (horder : v 8 ∈ forcingFormula (v 0) (v 1) piOneReverseInclusionOrderFormula
      (standardTuple ![v 4, forcingSaturatedName (v 0) (v 1) (forcingNameHierarchy (v 0) (v 5)) (v 3)]))
    (hf : IsForcingDirectedFamily
      (twoStepConditions (v 0) (v 1) (forcingSaturatedName (v 0) (v 1) (forcingNameHierarchy (v 0) (v 5)) (v 3)) (v 7))
      (twoStepOrder (v 0) (v 1) (forcingSaturatedName (v 0) (v 1) (forcingNameHierarchy (v 0) (v 5)) (v 3)) (v 4) (v 7)) (v 6) (v 9))
    (hpbelow : ∀ i ∈ v 6, ⟨v 8, kpair.π₁ ((v 9) ‘ i)⟩ₖ ∈ v 1) :
    twoStepUnionBound (v 6) (v 8) (v 9) ∈
      twoStepConditions (v 0) (v 1) (forcingSaturatedName (v 0) (v 1) (forcingNameHierarchy (v 0) (v 5)) (v 3)) (v 7) ∧
      ∀ i ∈ v 6, ⟨twoStepUnionBound (v 6) (v 8) (v 9), (v 9) ‘ i⟩ₖ ∈
        twoStepOrder (v 0) (v 1) (forcingSaturatedName (v 0) (v 1) (forcingNameHierarchy (v 0) (v 5)) (v 3)) (v 4) (v 7) :=
  (eval_saturatedTwoStepBoundFormula v).mp (saturatedTwoStepBound_valid v) hR htop hQ hS hδ hα
    _ _ _ _ _ rfl rfl rfl rfl rfl ht hp hclosed horder hf hpbelow

theorem saturated_twoStep_union_bound {P R one δ α p t f : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (Q S : ForcingName P)
    (hα : α ∈ internalCofinality δ) (ht : t ∈ forcingNameHierarchy P δ) (hp : p ∈ P)
    (hclosed : p ∈ forcingFormula P R forcingUnionClosedAtFormula (standardTuple ![Q.val, checkName one α]))
    (hS : p ∈ forcingFormula P R piOneReverseInclusionOrderFormula
      (standardTuple ![S.val, forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val]))
    (hf : IsForcingDirectedFamily
      (twoStepConditions P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val) t)
      (twoStepOrder P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val) S.val t) α f)
    (hpbelow : ∀ i ∈ α, ⟨p, kpair.π₁ (f ‘ i)⟩ₖ ∈ R) :
    twoStepUnionBound α p f ∈ twoStepConditions P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val) t ∧
      ∀ i ∈ α, ⟨twoStepUnionBound α p f, f ‘ i⟩ₖ ∈
        twoStepOrder P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val) S.val t :=
  saturatedTwoStepBound_transfer ![P, R, one, Q.val, S.val, δ, α, t, p, f]
    hR htop Q.property S.property (show IsOrdinal δ from inferInstance) hα ht hp hclosed hS hf hpbelow

end ZFVP
