import ZFVP.ModelTheory.ForcingCanonicalNormalization

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingCanonicalNameCorrectFormula : SetTheorySemisentence 7 :=
  f“P R o d t p n. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !choicelessInaccessibleFormula d ∧ P ∈ !hierarchyFormula d ∧
    !forcingNameFormula P t ∧ p ∈ P ∧
    !(binaryForcingTruthFormula nameInHierarchyFormula) p P R t (!checkNameFormula o d) ∧
    !forcingCanonicalNameFormula n P R o d t → p ∈ !atomicEqualityFormula P R n t”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingCanonicalName_forces_countable [Countable V] {P R one δ p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hp : p ∈ P)
    (τ : ForcingName P)
    (hτ : p ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName one δ])) :
    p ∈ atomicEquality P R (forcingCanonicalName P R one δ τ.val) τ.val := by
  apply atomicEquality_of_all_generics hR ht hp
    ⟨forcingCanonicalName P R one δ τ.val, forcingCanonicalName_isName _ _ _ _ _⟩ τ
  intro G hG hpG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  apply A.canonicalName_value hδ hP τ
  exact (Defined.eval_iff _).mp ((A.formula_truth nameInHierarchyFormula
    ![τ, ⟨checkName one δ, checkName_isName ht.1 δ⟩]).mpr ⟨p, hpG, hτ⟩)

private theorem forall_six_eq {T : Type*} (a b c d e f : T) (F : T → T → T → T → T → T → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔
      F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

theorem eval_forcingCanonicalNameCorrectFormula (v : Fin 7 → V) :
    forcingCanonicalNameCorrectFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsChoicelessInaccessible (v 3) → v 0 ∈ hierarchy (v 3) → IsForcingName (v 0) (v 4) →
        v 5 ∈ v 0 → v 5 ∈ forcingFormula (v 0) (v 1) nameInHierarchyFormula
          (standardTuple ![v 4, checkName (v 2) (v 3)]) →
        v 6 = forcingCanonicalName (v 0) (v 1) (v 2) (v 3) (v 4) →
        v 5 ∈ atomicEquality (v 0) (v 1) (v 6) (v 4)) := by
  simp [forcingCanonicalNameCorrectFormula]
  simp [Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq]

private theorem forcingCanonicalNameCorrect_valid (v : Fin 7 → V) :
    forcingCanonicalNameCorrectFormula.Evalb v := by
  apply eval_of_countable_zf forcingCanonicalNameCorrectFormula
  intro W _ _ _ _ w
  apply (eval_forcingCanonicalNameCorrectFormula w).mpr
  intro hR ht hδ hP hτ hp hf he
  rw [he]
  exact forcingCanonicalName_forces_countable hR ht hδ hP hp ⟨w 4, hτ⟩ hf

theorem forcingCanonicalName_forces {P R one δ p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hp : p ∈ P)
    (τ : ForcingName P)
    (hτ : p ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName one δ])) :
    p ∈ atomicEquality P R (forcingCanonicalName P R one δ τ.val) τ.val :=
  (eval_forcingCanonicalNameCorrectFormula
    ![P, R, one, δ, τ.val, p, forcingCanonicalName P R one δ τ.val]).mp
      (forcingCanonicalNameCorrect_valid _) hR ht hδ hP τ.property hp hτ rfl

theorem saturated_twoStep_canonicalName {P R one δ p Q t : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hp : p ∈ P)
    (τ : ForcingName P)
    (hτ : p ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName one δ]))
    (hm : p ∈ atomicMembership P R τ.val Q) :
    ⟨p, forcingCanonicalName P R one δ τ.val⟩ₖ ∈
      twoStepConditions P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q) t := by
  have hn := forcingCanonicalName_mem hR ht hδ hP τ.val
  have hname := forcingCanonicalName_isName P R one δ τ.val
  have he := forcingCanonicalName_forces hR ht hδ hP hp τ hτ
  have hmem := ((atomicEquality_membership_iff hR he Q).1).mpr hm
  exact (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hp,
    mem_union_iff.mpr (Or.inl (forcingSaturatedName_mem_domain hn hp hname hmem)),
    forcingSaturatedName_forces_member hR hn hp hname hmem⟩

end ZFVP
