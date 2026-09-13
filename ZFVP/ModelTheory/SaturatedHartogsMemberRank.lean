import ZFVP.ModelTheory.SaturatedHartogsSpecification
import ZFVP.ModelTheory.CanonicalNormalizationForcing
import ZFVP.ModelTheory.ForcingSemanticConsequence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def saturatedHartogsMemberRankFormula : SetTheorySemisentence 6 :=
  f“P R o γ δ τ. !forcingPreorderFormula P R → !forcingTopFormula P R o →
    !choicelessInaccessibleFormula δ → P ∈ !hierarchyFormula δ → γ ∈ δ →
    !forcingNameFormula P τ →
    ∀ Q, !saturatedHartogsPosetNameFormula Q P R o γ δ →
    o ∈ !atomicMembershipFormula P R τ Q →
    !(binaryForcingTruthFormula nameInHierarchyFormula) o P R τ (!checkNameFormula o δ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem saturatedHartogs_member_forces_rank_countable [Countable V]
    {P R top γ δ : V} (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hγ : γ ∈ δ)
    (τ : ForcingName P)
    (hτ : top ∈ atomicMembership P R τ.val (saturatedHartogsPosetName P R top γ δ)) :
    top ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName top δ]) := by
  apply forcingFormula_of_all_generics hR ht ht.1 nameInHierarchyFormula
    ![τ, ⟨checkName top δ, checkName_isName ht.1 δ⟩]
  intro G hG htG
  let A : ForcingContext V := ⟨P, R, top, G, hR, ht, hG⟩
  apply (Defined.eval_iff _).mpr
  change A.ofName τ ∈ hierarchy (A.check δ)
  have hm : A.ofName τ ∈ A.ofName (A.saturatedHartogsCollapseName γ δ) :=
    (forcingQuotientMk_mem_iff P R G hR hG.1 τ (A.saturatedHartogsCollapseName γ δ)).mpr ⟨top, htG, hτ⟩
  rw [A.saturatedHartogsCollapseName_value hδ hP hγ] at hm
  let := hδ.1
  exact woodinCollapse_condition_mem_hierarchy (A.check_inaccessible_of_small hδ hP).regular
    (IsOrdinal.toIsTransitive.transitive _ (A.hartogs_checked_mem hδ hP hγ)) hm

private theorem rank_forall_three_eq {β : Type*} (a b c : β) (F : β → β → β → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩

private theorem rank_forall_five_eq {β : Type*} (a b c d e : β) (F : β → β → β → β → β → Prop) :
    (∀ u v w x y, u = a → v = b → w = c → x = d → y = e → F u v w x y) ↔ F a b c d e :=
  ⟨fun h ↦ h a b c d e rfl rfl rfl rfl rfl,
    fun h u v w x y hu hv hw hx hy ↦ by subst u v w x y; exact h⟩

private theorem rank_forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

theorem eval_saturatedHartogsMemberRankFormula (v : Fin 6 → V) :
    saturatedHartogsMemberRankFormula.Evalb v ↔
    (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsChoicelessInaccessible (v 4) → v 0 ∈ hierarchy (v 4) → v 3 ∈ v 4 →
      IsForcingName (v 0) (v 5) →
      v 2 ∈ atomicMembership (v 0) (v 1) (v 5)
        (saturatedHartogsPosetName (v 0) (v 1) (v 2) (v 3) (v 4)) →
      v 2 ∈ forcingFormula (v 0) (v 1) nameInHierarchyFormula
        (standardTuple ![v 5, checkName (v 2) (v 4)])) := by
  simp [saturatedHartogsMemberRankFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ, rank_forall_three_eq, rank_forall_five_eq, rank_forall_six_eq]

theorem saturatedHartogs_member_forces_rank
    {P R top γ δ : V} (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hγ : γ ∈ δ)
    (τ : ForcingName P)
    (hτ : top ∈ atomicMembership P R τ.val (saturatedHartogsPosetName P R top γ δ)) :
    top ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName top δ]) := by
  have h := eval_of_countable_zf saturatedHartogsMemberRankFormula (by
    intro W _ _ _ _ v
    apply (eval_saturatedHartogsMemberRankFormula v).mpr
    intro hR ht hδ hP hγ hname hmem
    exact saturatedHartogs_member_forces_rank_countable hR ht hδ hP hγ ⟨v 5, hname⟩ hmem)
      ![P, R, top, γ, δ, τ.val]
  exact (eval_saturatedHartogsMemberRankFormula _).mp h hR ht hδ hP hγ τ.property hτ

end ZFVP








