import ZFVP.ModelTheory.WoodinStrictPrefixCutoff
import ZFVP.ModelTheory.ForcingHartogsName
import ZFVP.SetTheory.WoodinNamedPrefixCutoff
import ZFVP.SetTheory.InaccessibleHartogs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.strictHartogsPrefixCutoff_countable [Countable V] {P R one a δ : V}
    (hδ : IsWoodinSupercompact δ) (hord : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ) (haδ : a ∈ δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R (checkName one a)]))
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceBelowFormula
      (standardTuple ![hartogsNumberName P R (checkName one a)])) :
    ∃ c ∈ δ, IsWoodinNamedPrefixCutoff P R one a (hartogsNumberName P R (checkName one a)) c := by
  let := hδ.1.1
  let := IsOrdinal.of_mem haδ
  let η := (a ∪ rank P) ∪ rank R
  have hηδ : η ∈ δ := ordinal_union_mem
    (ordinal_union_mem haδ ((mem_hierarchy_iff_rank_mem _ _).mp hP))
    ((mem_hierarchy_iff_rank_mem _ _).mp hR)
  let := IsOrdinal.of_mem hηδ
  obtain ⟨γ, hδγ, hγ⟩ := sigmaOneStarCorrect_unbounded δ
  let := hγ.1.ordinal
  have h0γ : (∅ : V) ∈ hierarchy γ := (hierarchy_transitive γ).mem_trans empty_mem_ω
    (ordinal_mem_hierarchy_iff.mpr hγ.1.omega_lt)
  obtain ⟨ρ, _, hρ, _, _, e, he, c, hc, hcρ, hci, hηc, hcδ, hec, _⟩ :=
    (hδ.highCritical.2.2 γ hδγ hγ ∅ h0γ η hηδ).inaccessible_cutoff hδγ hγ.1
  let := hci.1
  have hac : a ∈ c := ordinal_mem_of_subset_mem
    (show a ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inl hz)))) hηc
  have hPc : P ∈ hierarchy c := (mem_hierarchy_iff_rank_mem _ _).mpr (ordinal_mem_of_subset_mem
    (show rank P ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inr hz)))) hηc)
  have hRc : R ∈ hierarchy c := (mem_hierarchy_iff_rank_mem _ _).mpr (ordinal_mem_of_subset_mem
    (show rank R ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inr hz)) hηc)
  have hcs : c ⊆ δ := IsOrdinal.toIsTransitive.transitive _ hcδ
  let τ : ForcingName P := ⟨checkName one a, checkName_isName htop.1 _⟩
  let κ : ForcingName P := ⟨hartogsNumberName P R τ.val, hartogsNumberName_isName _ _ _⟩
  let ν : ForcingName P := ⟨checkName one c, checkName_isName htop.1 _⟩
  refine ⟨c, hcδ, hac, hci, ?_⟩
  intro p hp
  apply forcingFormula_of_all_generics hord htop hp woodinLocalRestorationFormula ![κ, ν]
  intro G hG _
  let A : ForcingContext V := ⟨P, R, one, G, hord, htop, hG⟩
  obtain ⟨q, hq⟩ := hG.1.2.1
  have hκA : IsRegularCardinal (A.ofName κ) := (Defined.eval_iff _).mp
    ((A.formula_truth regularCardinalFormula ![κ]).mpr ⟨q, hq, hκ q (hG.1.1 q hq)⟩)
  have hDCA : ∀ α ∈ A.ofName κ, InternalDependentChoiceAt α := (Defined.eval_iff _).mp
    ((A.formula_truth dependentChoiceBelowFormula ![κ]).mpr ⟨q, hq, hDC q (hG.1.1 q hq)⟩)
  have hv : A.ofName κ = hartogsNumber (A.check a) := A.hartogsName_value τ
  have hk : A.ofName κ ∈ A.check c := by
    rw [hv]
    exact (A.check_inaccessible_of_small hci hPc).hartogsNumber_mem
      (ordinal_mem_hierarchy_iff.mpr ((A.check_mem_iff _ _).mpr hac))
  obtain ⟨k, hkc, hke⟩ := (A.mem_check_iff c (A.ofName κ)).mp hk
  rw [hke] at hκA hDCA
  have hz : (∅ : V) ∈ k := (A.check_mem_iff _ _).mp (by
    rw [A.check_empty]
    exact hκA.2.1 ∅ (by simp))
  have hl := A.rankCollapse_localRestoration hδ hρ hγ he hc hcρ hci hPc hRc hkc
    (IsOrdinal.toIsTransitive.transitive _ hkc) hcδ hcs hz hec hκA hDCA
  apply (Defined.eval_iff _).mpr
  change IsWoodinLocalRestoration (A.ofName κ) (A.check c)
  rwa [hke]

end ZFVP
