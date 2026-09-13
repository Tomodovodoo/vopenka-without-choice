import ZFVP.ModelTheory.RankCollapsePrefixReflection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.strictPrefixCutoff_countable [Countable V] {P R one κ δ : V}
    (hδ : IsWoodinSupercompact δ) (hord : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ) (hκδ : κ ∈ δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceBelowFormula (standardTuple ![checkName one κ])) :
    ∃ c ∈ δ, IsWoodinPrefixCutoff P R one κ c := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hκδ
  let η := (κ ∪ rank P) ∪ rank R
  have hηδ : η ∈ δ := ordinal_union_mem
    (ordinal_union_mem hκδ ((mem_hierarchy_iff_rank_mem _ _).mp hP))
    ((mem_hierarchy_iff_rank_mem _ _).mp hR)
  let := IsOrdinal.of_mem hηδ
  obtain ⟨γ, hδγ, hγ⟩ := sigmaOneStarCorrect_unbounded δ
  let := hγ.1.ordinal
  have h0γ : (∅ : V) ∈ hierarchy γ := (hierarchy_transitive γ).mem_trans empty_mem_ω
    (ordinal_mem_hierarchy_iff.mpr hγ.1.omega_lt)
  obtain ⟨ρ, _, hρ, _, _, e, he, c, hc, hcρ, hci, hηc, hcδ, hec, _⟩ :=
    (hδ.highCritical.2.2 γ hδγ hγ ∅ h0γ η hηδ).inaccessible_cutoff hδγ hγ.1
  let := hci.1
  have hκc : κ ∈ c := ordinal_mem_of_subset_mem
    (show κ ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inl hz)))) hηc
  have hPc : P ∈ hierarchy c := (mem_hierarchy_iff_rank_mem _ _).mpr (ordinal_mem_of_subset_mem
    (show rank P ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inr hz)))) hηc)
  have hRc : R ∈ hierarchy c := (mem_hierarchy_iff_rank_mem _ _).mpr (ordinal_mem_of_subset_mem
    (show rank R ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inr hz)) hηc)
  have hks : κ ⊆ c := IsOrdinal.toIsTransitive.transitive _ hκc
  have hcs : c ⊆ δ := IsOrdinal.toIsTransitive.transitive _ hcδ
  refine ⟨c, hcδ, (woodinPrefixCutoff_iff_all_generics hord htop).mpr ⟨hκc, hci, ?_⟩⟩
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hord, htop, hG⟩
  obtain ⟨p, hp⟩ := hG.1.2.1
  have hκA : IsRegularCardinal (A.check κ) := (Defined.eval_iff _).mp
    ((A.checked_unary_truth regularCardinalFormula κ).mpr ⟨p, hp, hκ p (hG.1.1 p hp)⟩)
  have hDCA : ∀ α ∈ A.check κ, InternalDependentChoiceAt α := (Defined.eval_iff _).mp
    ((A.checked_unary_truth dependentChoiceBelowFormula κ).mpr ⟨p, hp, hDC p (hG.1.1 p hp)⟩)
  have hz : (∅ : V) ∈ κ := (A.check_mem_iff _ _).mp (by
    rw [A.check_empty]
    exact hκA.2.1 ∅ (by simp))
  exact A.rankCollapse_localRestoration hδ hρ hγ he hc hcρ hci hPc hRc
    hκc hks hcδ hcs hz hec hκA hDCA

def strictWoodinPrefixCutoffFormula : SetTheorySemisentence 5 :=
  f“P R o κ δ. !woodinSupercompactFormula δ ∧ !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    P ∈ !hierarchyFormula δ ∧ R ∈ !hierarchyFormula δ ∧ κ ∈ δ ∧
    (∀ p ∈ P, !(checkedUnaryForcingFormula regularCardinalFormula) P R o p κ) ∧
    (∀ p ∈ P, !(checkedUnaryForcingFormula dependentChoiceBelowFormula) P R o p κ) →
      ∃ c ∈ δ, !woodinPrefixCutoffFormula P R o κ c”

theorem eval_strictWoodinPrefixCutoffFormula (v : Fin 5 → V) :
    strictWoodinPrefixCutoffFormula.Evalb v ↔
      (IsWoodinSupercompact (v 4) → IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        v 0 ∈ hierarchy (v 4) → v 1 ∈ hierarchy (v 4) → v 3 ∈ v 4 →
        (∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) regularCardinalFormula
          (standardTuple ![checkName (v 2) (v 3)])) →
        (∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) dependentChoiceBelowFormula
          (standardTuple ![checkName (v 2) (v 3)])) →
        ∃ c ∈ v 4, IsWoodinPrefixCutoff (v 0) (v 1) (v 2) (v 3) c) := by
  simp [strictWoodinPrefixCutoffFormula]

theorem IsWoodinSupercompact.strictPrefixCutoff {P R one κ δ : V}
    (hδ : IsWoodinSupercompact δ) (hord : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ) (hκδ : κ ∈ δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceBelowFormula (standardTuple ![checkName one κ])) :
    ∃ c ∈ δ, IsWoodinPrefixCutoff P R one κ c := by
  have hh := eval_of_countable_zf strictWoodinPrefixCutoffFormula (by
    intro W _ _ _ _ v
    exact (eval_strictWoodinPrefixCutoffFormula v).mpr (fun hδ ho ht hP hR hk hκ hDC ↦
      hδ.strictPrefixCutoff_countable ho ht hP hR hk hκ hDC)) ![P, R, one, κ, δ]
  exact (eval_strictWoodinPrefixCutoffFormula _).mp hh hδ hord htop hP hR hκδ hκ hDC

theorem woodinPrefixCutoff_lt_supercompact {P R one κ δ : V}
    (hδ : IsWoodinSupercompact δ) (hord : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ) (hκδ : κ ∈ δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceBelowFormula (standardTuple ![checkName one κ])) :
    woodinPrefixCutoff P R one κ ∈ δ := by
  let := hδ.1.1
  obtain ⟨c, hcδ, hc⟩ := hδ.strictPrefixCutoff hord htop hP hR hκδ hκ hDC
  let := hc.2.1.1
  let := (woodinPrefixCutoff_spec hc).1
  exact ordinal_mem_of_subset_mem (woodinPrefixCutoff_le hc) hcδ

end ZFVP
