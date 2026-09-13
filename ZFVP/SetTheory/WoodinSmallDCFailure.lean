import ZFVP.SetTheory.DependentChoiceFailureCertificate
import ZFVP.SetTheory.WoodinSupercompactInaccessible
import ZFVP.ModelTheory.SuccessorRankFunctionClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.small_dependentChoice_failure_certificate {δ κ : V}
    (hδ : IsWoodinSupercompact δ) (hκ : κ ∈ δ)
    (hfail : ¬InternalDependentChoiceAt κ) :
    ∃ B ∈ hierarchy δ, IsRankFunctionClosed (succ κ) B ∧ hierarchy (succ κ) ∈ B ∧
      κ ∈ B ∧ IsTransitive B ∧ IsFunctionRestrictionClosed B ∧
      IsBoundedDependentChoiceFailure κ B := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hκ
  obtain ⟨B, hclosed, hD, hkB, ht, hr, hf⟩ := hδ.dependentChoice_failure_certificate hfail
  let η := δ ∪ rank B
  let : IsOrdinal η := ordinal_union_ordinal δ (rank B)
  obtain ⟨θ, hηθ, hθ⟩ := sigmaOneStarCorrect_unbounded η
  let := hθ.1.ordinal
  have hδθ : δ ∈ θ := ordinal_mem_of_subset_mem
    (show δ ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inl hz)) hηθ
  have hBθ : B ∈ hierarchy θ := (mem_hierarchy_iff_rank_mem _ _).mpr
    (ordinal_mem_of_subset_mem
      (show rank B ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inr hz)) hηθ)
  have hsκδ : succ κ ∈ δ := regularCardinal_succ_closed hδ.regular hκ
  obtain ⟨_, ρ, hρδ, hρ, b, hb, e, he, c, hc, hec, heb, hsκc⟩ :=
    hδ.highCritical.2.2 θ hδθ hθ B hBθ (succ κ) hsκδ
  let := hρ.1.ordinal
  let := hc.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ θ)
  have hcρ := successorRankEmbedding_criticalPoint_lt_height he hc (hec.symm ▸ hδθ)
  have hsκρ := IsOrdinal.toIsTransitive.mem_trans hsκc hcρ
  have hsκV : succ κ ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr hsκρ
  have hkρ : κ ∈ ρ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self κ) hsκρ
  have hkV : κ ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr hkρ
  have hDV : hierarchy (succ κ) ∈ hierarchy ρ := hierarchy_mem hsκρ
  have heκ : e ‘ κ = κ := hc.fixed_below
    (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self κ) hsκc)
  have hesκ : e ‘ (succ κ) = succ κ := hc.fixed_below hsκc
  have heD : e ‘ (hierarchy (succ κ)) = hierarchy (succ κ) :=
    successorRankEmbedding_fixed_below_criticalPoint hρ.1 hθ.1 he hc hcρ _ (hierarchy_mem hsκc)
  have hinc : hierarchy ρ ⊆ hierarchy (succ ρ) := hierarchy_mono
    (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz))
  have hcsmall : IsRankFunctionClosed (succ κ) b := by
    apply (successorRankEmbedding_rankFunctionClosed hρ.1 hθ.1 he inferInstance hsκV hb).mpr
    simpa [hesκ, heb] using hclosed
  have hDsmall : hierarchy (succ κ) ∈ b := by
    apply (he.value_mem_iff (hinc _ hDV) (hinc _ hb)).mp
    simpa [heD, heb] using hD
  have hksmall : κ ∈ b := by
    apply (he.value_mem_iff (hinc _ hkV) (hinc _ hb)).mp
    simpa [heκ, heb] using hkB
  have htsmall : IsTransitive b := by
    apply (he.bounded_defined_iff isTransitiveFormula_bounded
      (fun v ↦ IsTransitive (v 0)) ![b] (by simp [hinc _ hb])).mpr
    simpa [heb] using ht
  have hrsmall : IsFunctionRestrictionClosed b := by
    apply (he.bounded_defined_iff functionRestrictionClosedFormula_bounded
      (fun v ↦ IsFunctionRestrictionClosed (v 0)) ![b] (by simp [hinc _ hb])).mpr
    simpa [heb] using hr
  have hfsmall : IsBoundedDependentChoiceFailure κ b := by
    apply (he.bounded_defined_iff boundedDependentChoiceFailureFormula_bounded
      (fun v ↦ IsBoundedDependentChoiceFailure (v 0) (v 1)) ![κ, b]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hinc _ hkV, hinc _ hb])).mpr
    simpa [heκ, heb] using hf
  exact ⟨b, hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hρδ) _ hb,
    hcsmall, hDsmall, hksmall, htsmall, hrsmall, hfsmall⟩

end ZFVP
