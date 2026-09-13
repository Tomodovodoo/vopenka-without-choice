import ZFVP.SetTheory.ChoicelessEquivalence
import ZFVP.SetTheory.CnCofinal

/-! Correctness of choiceless cardinals. Small embeddings pull back
correct-domain witnesses while fixing the parameter assignment. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsChoicelessSupercompact.cnCofinal {k : ℕ} {κ : V}
    (hκ : IsChoicelessSupercompact (k + 1) κ) : CnCofinal (k + 1) κ := by
  let := hκ.1
  intro α hα
  obtain ⟨μ, hκμ, hμ⟩ := cn_unbounded (k + 1) κ
  let := hμ.ordinal
  obtain ⟨_, ν, x, f, c, hνκ, hν, _, _, hc, hαc, _⟩ :=
    (hκ.2.2 α hα).2.2 μ hμ hκμ ω (ordinal_subset_hierarchy μ _ hμ.omega_lt)
  let := hν.ordinal
  let := hc.ordinal
  exact ⟨ν, hνκ, IsOrdinal.toIsTransitive.mem_trans hαc
    (ordinal_mem_hierarchy_iff.mp hc.mem_domain), hν⟩

theorem IsChoicelessSupercompact.cn {k : ℕ} {κ : V}
    (hκ : IsChoicelessSupercompact (k + 1) κ) : Cn (k + 1) κ := by
  let := hκ.1
  exact cn_closed _ hκ.2.1 hκ.cnCofinal

theorem IsChoicelessSupercompact.cn_succ {k : ℕ} {κ : V}
    (hκ : IsChoicelessSupercompact (k + 1) κ) : Cn (k + 2) κ := by
  let := hκ.1
  let := hierarchy_transitive κ
  have hbase := hκ.cn
  have hD := ((cn_successor_iff k κ).mp hbase).2
  apply (cn_successor_iff (k + 1) κ).mpr
  refine ⟨hκ.1, hD, ?_⟩
  intro n _ φ _ b hb hcode htyped htruth
  obtain ⟨B, hB, hbB, hsB⟩ := htruth
  have hrbκ : rank b ∈ κ := (mem_hierarchy_iff_rank_mem b κ).mp hb
  let := ordinal_union_ordinal κ (rank B)
  obtain ⟨μ, hbound, hμ⟩ := cn_unbounded (k + 1) (κ ∪ rank B)
  let := hμ.ordinal
  let := hierarchy_transitive μ
  have hκμ := ordinal_mem_of_subset_mem (subset_union_left κ (rank B)) hbound
  have hrBμ := ordinal_mem_of_subset_mem (subset_union_right κ (rank B)) hbound
  have hBV : B ∈ hierarchy μ := (mem_hierarchy_iff_rank_mem B μ).mpr hrBμ
  obtain ⟨_, ν, C, f, c, hνκ, hν, hCV, hj, hc, hrbc, hCB⟩ :=
    (hκ.2.2 (rank b) hrbκ).2.2 μ hμ hκμ B hBV
  let := hν.ordinal
  let := hierarchy_transitive ν
  let := hc.ordinal
  let := hierarchy_transitive c
  let : IsSequenceSupport (hierarchy ν) := ((cn_successor_iff k ν).mp hν).2.support
  have hbC : b ∈ hierarchy c := (mem_hierarchy_iff_rank_mem b c).mpr hrbc
  have hbV := (hierarchy_transitive ν).mem_trans hbC
    (hν.hierarchy_closed hc.ordinal hc.mem_domain)
  have hfix := rankEmbedding_fixed_below_criticalPoint hν hμ hj hc b hbC
  have hn := hcode.context
  have hnV : n ∈ hierarchy ν := IsCodingSupport.natural_mem hn
  have hC : CorrectDomain (k + 1) C := by
    apply (rankEmbedding_defined_iff hν hμ hj (correctDomainFormula_pi (k + 1))
      (fun v ↦ CorrectDomain (k + 1) (v 0)) ![C] (by simpa using hCV)).mpr
    change CorrectDomain (k + 1) (f ‘ C)
    rwa [hCB]
  have hbtyped : b ∈ C ^ n := by
    apply (hj.bounded_defined_iff boundedFunctionFormula_bounded
      (fun v ↦ v 0 ∈ v 2 ^ v 1) ![b, n, C]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hbV, hnV, hCV])).mpr
    change f ‘ b ∈ (f ‘ C) ^ (f ‘ n)
    rwa [hfix, hCB, hj.value_natural hn]
  have hbν : b ∈ (hierarchy ν) ^ n := (function_on_support_iff hbV n).mpr
    ⟨IsFunction.of_mem hbtyped, domain_eq_of_mem_function hbtyped⟩
  have hcomp : compose b f = b := (hj.value_assignment hn hbV hbν).symm.trans hfix
  have hsat : MembershipSatisfies C n φ b := by
    apply (rankEmbedding_setSatisfaction hν hμ hj hCV
      ((mem_formulaSet_iff _ _ _ _).mp hcode.valid) hbtyped).mpr
    rwa [hCB, hcomp]
  have hCκ : C ⊆ hierarchy κ := (hierarchy_transitive κ).transitive C
    (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hνκ) C hCV)
  exact correctDomainCode_upward (k + 1) hcode C (hierarchy κ) hC hD hCκ b hbtyped hsat

theorem IsChoicelessExtendible.cn {n : ℕ} {κ : V}
    (hκ : IsChoicelessExtendible (n + 1) κ) : Cn (n + 3) κ := hκ.supercompact_succ.cn_succ

theorem IsCnExtendible.cn {n : ℕ} {κ : V} (hκ : IsCnExtendible (n + 1) κ) : Cn (n + 3) κ := by
  let := hκ.1.1
  have hfull : IsChoicelessExtendible (n + 1) κ :=
    ⟨hκ.1.1, ?_, fun α hα ↦ hκ.alphaChoiceless hα⟩
  · exact hfull.cn
  · obtain ⟨μ, hκμ, hμ⟩ := cn_unbounded (n + 1) κ
    obtain ⟨ν, f, _, hν, hf, hc, _⟩ := hκ.2 μ hμ hκμ
    let : IsSequenceSupport (hierarchy μ) := ((cn_successor_iff n μ).mp hμ).2.support
    let : IsSequenceSupport (hierarchy ν) := ((cn_successor_iff n ν).mp hν).2.support
    exact ⟨ω, hc.omega_lt hf⟩

end ZFVP
