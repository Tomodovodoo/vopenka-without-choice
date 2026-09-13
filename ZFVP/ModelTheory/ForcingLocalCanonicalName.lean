import ZFVP.ModelTheory.ForcingRestrictedName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingLocalCanonicalNameFormula : SetTheorySemisentence 7 :=
  f“n P R o d p t. ∀ c, !forcingCanonicalNameFormula c P R o d t →
    !forcingRestrictedNameFormula n P R p c”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingLocalCanonicalName (P R one δ p τ : V) : V :=
  forcingRestrictedName P R p (forcingCanonicalName P R one δ τ)

private theorem forall_six_eq {T : Type*} (a b c d e f : T) (F : T → T → T → T → T → T → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔
      F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

instance forcingLocalCanonicalNameFormula_defined :
    Defined (fun v : Fin 7 → V ↦
      v 0 = forcingLocalCanonicalName (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
      forcingLocalCanonicalNameFormula :=
  ⟨fun v ↦ by
    simp [forcingLocalCanonicalNameFormula, forcingLocalCanonicalName]
    simp [Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq]⟩

instance forcingLocalCanonicalName_definable :
    Language.DefinableFunction ℒₛₑₜ
      (fun v : Fin 6 → V ↦ forcingLocalCanonicalName (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  forcingLocalCanonicalNameFormula_defined.to_definable

theorem forcingLocalCanonicalName_isName (P R one δ p τ : V) :
    IsForcingName P (forcingLocalCanonicalName P R one δ p τ) :=
  forcingRestrictedName_isName (forcingCanonicalName_isName _ _ _ _ _)

theorem forcingLocalCanonicalName_mem {P R one δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (p τ : V) :
    forcingLocalCanonicalName P R one δ p τ ∈ forcingNameHierarchy P δ := by
  let := hδ.1
  exact forcingRestrictedName_mem (forcingCanonicalName_mem hR ht hδ hP τ)

theorem forcingLocalCanonicalName_forces {P R one δ p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hp : p ∈ P)
    (τ : ForcingName P)
    (hτ : p ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName one δ])) :
    p ∈ atomicEquality P R (forcingLocalCanonicalName P R one δ p τ.val) τ.val := by
  exact atomicEquality_trans hR _ _ _ p
    (forcingRestrictedName_forces hR hp _) (forcingCanonicalName_forces hR ht hδ hP hp τ hτ)

theorem forcingRestrictedSaturatedName_empty {P R p U τ : V}
    (hR : IsForcingPreorder P R) (he : p ∈ atomicEquality P R τ ∅) :
    forcingRestrictedName P R p (forcingSaturatedName P R U τ) = ∅ := by
  apply subset_empty_iff_eq_empty.mp
  intro z hz
  obtain ⟨σ, _, r, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨hr, hrp, q, _, hσq, hrq⟩ := (pair_mem_forcingRestrictedName _ _ _ _ _ _).mp hz
  have hm := ((pair_mem_forcingSaturatedName _ _ _ _ _ _).mp hσq).2.2.2
  have hbad := atomicMembership_subst_right hR (atomicEquality_mono hR he hr hrp)
    (atomicMembership_mono hR hm hr hrq)
  rw [atomicMembership_empty hR σ] at hbad
  exact False.elim (not_mem_empty hbad)

theorem forcingLocalCanonicalName_empty_of_forced {P R one δ p τ : V}
    (hR : IsForcingPreorder P R) (he : p ∈ atomicEquality P R τ ∅) :
    forcingLocalCanonicalName P R one δ p τ = ∅ :=
  forcingRestrictedSaturatedName_empty hR he

theorem forcingLocalCanonicalName_forces_below {P R one δ p q : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hp : p ∈ P) (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R) (τ : ForcingName P)
    (hτ : q ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName one δ])) :
    q ∈ atomicEquality P R (forcingLocalCanonicalName P R one δ p τ.val) τ.val := by
  exact atomicEquality_trans hR _ _ _ q
    (atomicEquality_mono hR (forcingRestrictedName_forces hR hp _) hq hqp)
    (forcingCanonicalName_forces hR ht hδ hP hq τ hτ)

theorem saturated_twoStep_localCanonicalName_below {P R one δ p q Q t : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hp : p ∈ P) (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R) (τ : ForcingName P)
    (hτ : q ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName one δ]))
    (hm : q ∈ atomicMembership P R τ.val Q) :
    ⟨q, forcingLocalCanonicalName P R one δ p τ.val⟩ₖ ∈
      twoStepConditions P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q) t := by
  have hn := forcingLocalCanonicalName_mem hR ht hδ hP p τ.val
  have hname := forcingLocalCanonicalName_isName P R one δ p τ.val
  have he := forcingLocalCanonicalName_forces_below hR ht hδ hP hp hq hqp τ hτ
  have hmem := ((atomicEquality_membership_iff hR he Q).1).mpr hm
  exact (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hq,
    mem_union_iff.mpr (Or.inl (forcingSaturatedName_mem_domain hn hq hname hmem)),
    forcingSaturatedName_forces_member hR hn hq hname hmem⟩

theorem saturated_twoStep_localCanonicalName {P R one δ p Q t : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hp : p ∈ P)
    (τ : ForcingName P)
    (hτ : p ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName one δ]))
    (hm : p ∈ atomicMembership P R τ.val Q) :
    ⟨p, forcingLocalCanonicalName P R one δ p τ.val⟩ₖ ∈
      twoStepConditions P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q) t := by
  exact saturated_twoStep_localCanonicalName_below hR ht hδ hP hp hp (hR.2.1 p hp) τ hτ hm

end ZFVP
