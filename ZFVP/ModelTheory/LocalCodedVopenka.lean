import ZFVP.ModelTheory.CriticalStageModels
import ZFVP.ModelTheory.ElementaryAmbientEmbeddings

/-! Vopenka for every internal class code in the critical limit model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def LocalCodedVopenka (U φ : V) : Prop :=
  ∀ L a : SetDomain U,
    (∀ A : SetDomain U, ∃ M : SetDomain U,
      MembershipSatisfies U 2 φ (standardTuple ![M.val, a.val]) ∧ M ∉ A) →
    (∀ M : SetDomain U, MembershipSatisfies U 2 φ (standardTuple ![M.val, a.val]) →
      isStructureCodeFormula.Evalb ![L, M]) →
    ∃ M N e : SetDomain U, M ≠ N ∧
      MembershipSatisfies U 2 φ (standardTuple ![M.val, a.val]) ∧
      MembershipSatisfies U 2 φ (standardTuple ![N.val, a.val]) ∧
      codedElementaryEmbeddingFormula.Evalb ![L, M, N, e]

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

set_option maxHeartbeats 2000000 in
theorem limit_localCodedVopenka_of_bound (m : ℕ) (hm : coreSyntaxDictionaryBound ≤ m + 1)
    (hlim : criticalLimit f κ ∈ hierarchy δ)
    {φ : V} (hφ : IsMembershipFormulaCode (2 : V) φ) :
    LocalCodedVopenka (hierarchy (criticalLimit f κ)) φ := by
  let U := hierarchy (criticalLimit f κ)
  let := limit_ordinal hδ h hκ
  let := hierarchy_transitive (criticalLimit f κ)
  let := rankDomain_nonempty (omega_mem_limit hδ h hκ)
  let := limit_models_zf hδ h hκ
  intro L a hproper hclass
  let d : SetDomain U := ⟨L, ⟨a, syntaxUniverse L ∅⟩ₖ⟩ₖ
  obtain ⟨i, hi, hdi⟩ := (rank_union_iff hδ h hκ d.val).mp d.property
  let c : SetDomain U :=
    ⟨criticalIterate f κ i, ordinal_subset_hierarchy _ _ (iterate_mem_limit hδ h hκ hi)⟩
  have hco : IsOrdinal c := (TransitiveZF.ordinal_iff U c).mpr (iterate_spec hδ h hκ hi).1
  let := hco
  let := hierarchy_transitive c
  have hd : d ∈ hierarchy c := (TransitiveZF.hierarchy_mem_iff U c d hco).mpr hdi
  obtain ⟨hLc, hap⟩ := kpair_components_mem_transitive hd
  obtain ⟨hac, hSc⟩ := kpair_components_mem_transitive hap
  let P : SetDomain U → Prop := fun M ↦ MembershipSatisfies U 2 φ (standardTuple ![M.val, a.val])
  have hp : IsProperClass P := hproper
  obtain ⟨M, hMP, hcM⟩ := hp.rank_unbounded c
  have hM : IsStructureCode L M := (Defined.eval_iff ![L, M]).mp (hclass M hMP)
  obtain ⟨q, hq, hMq⟩ := (rank_union_iff hδ h hκ M.val).mp M.property
  let s := succ q
  let t := succ (succ q)
  have hs : s ∈ (ω : V) := ω_succ_closed hq
  have ht : t ∈ (ω : V) := ω_succ_closed hs
  have hs0 : s ≠ 0 := by
    intro hz
    have hm : q ∈ s := by simp [s]
    simp only [hz, zero_def, not_mem_empty] at hm
  have ht0 : t ≠ 0 := by
    intro hz
    have hm : succ q ∈ t := by simp [t]
    simp only [hz, zero_def, not_mem_empty] at hm
  let r := ordinalAdd s i
  let z := ordinalAdd (ordinalAdd s t) i
  have hr : r ∈ (ω : V) := ordinalAdd_natural hs hi
  have hz : z ∈ (ω : V) := ordinalAdd_natural (ordinalAdd_natural hs ht) hi
  let α : SetDomain U :=
    ⟨criticalIterate f κ r, ordinal_subset_hierarchy _ _ (iterate_mem_limit hδ h hκ hr)⟩
  let β : SetDomain U :=
    ⟨criticalIterate f κ z, ordinal_subset_hierarchy _ _ (iterate_mem_limit hδ h hκ hz)⟩
  let e : SetDomain U :=
    ⟨shiftedCriticalEmbedding δ f κ s t i, shifted_mem_limit hδ h hκ hlim hs ht hi⟩
  have he := shifted_elementary hδ h hκ hlim hs ht hi
  have hec := shifted_criticalPoint hδ h hκ hlim hs ht hi hs0 ht0
  have he' := stageEmbedding_internal hδ h hκ hr hz α β e rfl rfl he
  have hc' := stageCriticalPoint_internal hδ h hκ hr hz α β e c rfl rfl he hec
  have hα : Cn (m + 1) α :=
    (eval_cnFormula _ α).mp (limit_stage_cn hδ h hκ hr m α rfl)
  have hβ : Cn (m + 1) β :=
    (eval_cnFormula _ β).mp (limit_stage_cn hδ h hκ hz m β rfl)
  let := hα.ordinal
  let := hβ.ordinal
  let := hierarchy_transitive α
  let := hierarchy_transitive β
  let := (iterate_spec hδ h hκ hq).1
  let := (iterate_spec hδ h hκ (ordinalAdd_natural hq hi)).1
  let := (iterate_spec hδ h hκ hr).1
  let := (iterate_spec hδ h hκ (ordinalAdd_natural ht hi)).1
  have hMqrank : rank M.val ∈ criticalIterate f κ q := (mem_hierarchy_iff_rank_mem _ _).mp hMq
  have hMrank : rank M.val ∈ α.val := IsOrdinal.toIsTransitive.mem_trans
    ((iterate_subset_add hδ h hκ hq hi) _ hMqrank) (iterate_add_increasing hδ h hκ hq hi)
  have hMα : M ∈ hierarchy α := (TransitiveZF.hierarchy_mem_iff U α M hα.ordinal).mpr
    ((mem_hierarchy_iff_rank_mem _ _).mpr hMrank)
  have hafix := rankEmbedding_fixed_below_criticalPoint hα hβ he' hc' a hac
  have haα : a ∈ hierarchy α := (hierarchy_transitive α).mem_trans hac
    (hα.hierarchy_closed hco hc'.mem_domain)
  let := IsFunction.of_mem he'.function
  have hval (x : SetDomain U) (hx : x ∈ hierarchy α) :
      (e ‘ x).val = e.val ‘ x.val := TransitiveZF.value_val U e x
    (by rw [domain_eq_of_mem_function he'.function]; exact hx)
  have hfix : e.val ‘ a.val = a.val := by
    rw [← hval a haα, hafix]
  have htarget : P (e ‘ M) := by
    change MembershipSatisfies U 2 φ (standardTuple ![(e ‘ M).val, a.val])
    rw [hval M hMα]
    exact (he.ambient_class (limit_elementaryInclusion hδ h hκ hr)
      (limit_elementaryInclusion hδ h hκ hz) hφ
      ((TransitiveZF.hierarchy_mem_iff U α M hα.ordinal).mp hMα)
      ((TransitiveZF.hierarchy_mem_iff U α a hα.ordinal).mp haα) hfix).mp hMP
  have hgeneric := rankEmbedding_generic_restrict hα hβ he' hc' hm
    hLc ((hierarchy_transitive c).transitive _ hSc) hM hMα
  have hmove : rank M ∈ e ‘ c := by
    change (rank M).val ∈ (e ‘ c).val
    rw [TransitiveZF.rank_val U M, hval c hc'.mem_domain]
    change rank M.val ∈ (shiftedCriticalEmbedding δ f κ s t i) ‘ (criticalIterate f κ i)
    rw [shifted_value_criticalPoint hδ h hκ hlim hs ht hi hs0]
    exact IsOrdinal.toIsTransitive.mem_trans hMrank (iterate_add_increasing hδ h hκ hs hi)
  have hne : M ≠ e ‘ M := by
    intro hsame
    have hrfix : e ‘ (rank M) = rank M := by
      rw [rankEmbedding_value_rank hα hβ he' hMα, ← hsame]
    have hm := (he'.value_mem_iff hc'.mem_domain (hα.rank_closed hMα)).mpr hcM
    rw [hrfix] at hm
    let := he'.value_ordinal hc'.ordinal hc'.mem_domain
    exact mem_irrefl (rank M) (IsOrdinal.toIsTransitive.mem_trans hmove hm)
  exact ⟨M, e ‘ M, e ↾ (structureDomain M), hne, hMP, htarget,
    (Defined.eval_iff ![L, M, e ‘ M, e ↾ (structureDomain M)]).mpr hgeneric⟩

set_option maxHeartbeats 2000000 in
theorem limit_localCodedVopenka (hlim : criticalLimit f κ ∈ hierarchy δ)
    {φ : V} (hφ : IsMembershipFormulaCode (2 : V) φ) :
    LocalCodedVopenka (hierarchy (criticalLimit f κ)) φ :=
  limit_localCodedVopenka_of_bound hδ h hκ coreSyntaxDictionaryBound (Nat.le_add_right _ _) hlim hφ

end CriticalSequence

end ZFVP
