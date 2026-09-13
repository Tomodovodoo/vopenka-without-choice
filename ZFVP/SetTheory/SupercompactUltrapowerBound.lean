import ZFVP.SetTheory.SupercompactUltrapower
import ZFVP.SetTheory.SmallSubsetsStage

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A member of the image of the small-subset set has an actual smallness witness.
Only bounded injection absoluteness is needed in the transitive target. -/
theorem image_smallSubsets_member_small {θ M j κ lam s : V} [IsOrdinal θ]
    [IsTransitive M] (hsucc : ∀ β ∈ θ, succ β ∈ θ)
    (hj : IsCodedMembershipEmbedding (hierarchy θ) M j)
    (hκ : κ ∈ hierarchy θ) (hlam : lam ∈ hierarchy θ)
    (hs : s ∈ j ‘ (smallSubsetsBelow κ lam)) : USmall (j ‘ κ) s := by
  have hP := smallSubsetsBelow_mem_hierarchy hsucc hκ hlam
  have hsrc := (eval_smallSubsetsBelowFormula_stage hsucc hP hκ hlam).mpr rfl
  have htr := (hj.eval_semisentence smallSubsetsBelowFormula
    (![⟨smallSubsetsBelow κ lam, hP⟩, ⟨κ, hκ⟩, ⟨lam, hlam⟩] :
      Fin 3 → SetDomain (hierarchy θ))).mp hsrc
  let P' := hj.toFunction ⟨smallSubsetsBelow κ lam, hP⟩
  let κ' := hj.toFunction ⟨κ, hκ⟩
  let lam' := hj.toFunction ⟨lam, hlam⟩
  have hev : smallSubsetsBelowFormula.Evalb ![P', κ', lam'] := by
    have hv : hj.toFunction ∘ (![⟨smallSubsetsBelow κ lam, hP⟩, ⟨κ, hκ⟩, ⟨lam, hlam⟩] :
        Fin 3 → SetDomain (hierarchy θ)) = ![P', κ', lam'] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
        (fun l ↦ Fin.elim0 l) k) j) i
    rwa [hv] at htr
  simp only [smallSubsetsBelowFormula] at hev
  simp at hev
  let s' : SetDomain M := ⟨s, (inferInstance : IsTransitive M).mem_trans hs P'.property⟩
  obtain ⟨_, μ, hμ, g, hg⟩ := (hev s').mp hs
  have habs := (bounded_formula_absolute M boundedInjectionFormula_bounded ![g, s', μ]).mp hg
  have hinj : g.val ∈ μ.val ^ s ∧ Injective g.val := by simpa using habs
  exact ⟨μ.val, hμ, g.val, hinj.1, hinj.2⟩

/-- Fineness injects the index ordinal into the collapsed identity seed. -/
theorem ultraSeed_cardLE (hAC : InternalChoice V) {κ lam U A : V} [IsOrdinal κ]
    [IsTransitive A] (hU : IsNormalFineMeasure κ lam U)
    (hω : (ω : V) ∈ κ) (hA : IsNonempty A)
    (hlam : lam ⊆ A) (hPA : smallSubsetsBelow κ lam ⊆ A) :
    lam ≤# (ultraCollapse (smallSubsetsBelow κ lam) U A) ‘
      (SetTheory.identity (smallSubsetsBelow κ lam)) := by
  let P := smallSubsetsBelow κ lam
  let j := ultraEmbedding P U A
  let s := (ultraCollapse P U A) ‘ (SetTheory.identity P)
  have hf : j ↾ lam ∈ s ^ lam := by
    apply mem_function_of_domain_values (by infer_instance)
    · rw [domain_restrict_eq, domain_ultraEmbedding]
      apply mem_ext
      intro x
      exact ⟨fun hx ↦ (mem_inter_iff.mp hx).2, fun hx ↦ mem_inter_iff.mpr ⟨hlam x hx, hx⟩⟩
    · intro x hx
      rw [value_restrict (by simpa only [j, domain_ultraEmbedding] using hlam x hx) hx,
        value_ultraEmbedding (hlam x hx)]
      exact (ultraCollapse_mem_iff hAC hU.1 hU.2.1 hω hA
        (constantGraph_mem_ultraFunctions (hlam x hx)) (identity_mem_ultraFunctions hPA)).mpr
        (ultraMem_constantGraph_identity hU hx)
  refine ⟨j ↾ lam, hf, ?_⟩
  intro x y z hx hy
  exact (ultraEmbedding_injective hAC hU.1 hU.2.1 hω hA) x y z
    ((mem_restrict_iff.mp hx).1) ((mem_restrict_iff.mp hy).1)
theorem ultraEmbedding_index_lt (hAC : InternalChoice V) {κ lam θ U : V}
    [IsOrdinal κ] [IsOrdinal θ] (hlam : IsInitialOrdinal lam)
    (hU : IsNormalFineMeasure κ lam U) (hω : (ω : V) ∈ κ)
    (hsucc : ∀ β ∈ θ, succ β ∈ θ) (hκθ : κ ∈ θ) (hlamθ : lam ∈ θ) :
    lam ∈ (ultraEmbedding (smallSubsetsBelow κ lam) U (hierarchy θ)) ‘ κ := by
  let := hlam.1
  let A := hierarchy θ
  let P := smallSubsetsBelow κ lam
  let j := ultraEmbedding P U A
  let s := (ultraCollapse P U A) ‘ (SetTheory.identity P)
  let := hierarchy_transitive θ
  have hκA : κ ∈ A := ordinal_mem_hierarchy_iff.mpr hκθ
  have hlamA : lam ∈ A := ordinal_mem_hierarchy_iff.mpr hlamθ
  have hA : IsNonempty A := ⟨⟨κ, hκA⟩⟩
  have hP : P ∈ A := smallSubsetsBelow_mem_hierarchy hsucc hκA hlamA
  have hPA : P ⊆ A := (hierarchy_transitive θ).transitive _ hP
  have hwf := ultraMemRelation_wellFounded hAC hU.1 hU.2.1 hω (A := A)
  let := ultraTarget_transitive hwf
  have hj := ultraEmbedding_codedMembershipEmbedding hAC hU.1 hU.2.1 hω hA
  have hseed : s ∈ j ‘ P := by
    rw [value_ultraEmbedding hP]
    apply (ultraCollapse_mem_iff hAC hU.1 hU.2.1 hω hA
      (identity_mem_ultraFunctions hPA) (constantGraph_mem_ultraFunctions hP)).mpr
    have he : ultraMem P (SetTheory.identity P) (constantGraph P P) = P := by
      apply mem_ext
      intro x
      rw [mem_ultraMem_iff]
      exact ⟨fun hh ↦ hh.1, fun hx ↦ ⟨hx, by rw [identity_value hx, value_constantGraph P P hx]; exact hx⟩⟩
    change ultraMem P (SetTheory.identity P) (constantGraph P P) ∈ U
    rw [he]
    exact hU.1.2.1
  have hsmall : USmall (j ‘ κ) s := image_smallSubsets_member_small hsucc hj hκA hlamA hseed
  have hle : lam ≤# s := ultraSeed_cardLE hAC hU hω hA
    ((hierarchy_transitive θ).transitive _ hlamA) hPA
  obtain ⟨μ, hμ, hm⟩ := hsmall
  let := hj.value_ordinal (inferInstance : IsOrdinal κ) hκA
  let := IsOrdinal.of_mem hμ
  have hsub : lam ⊆ μ := (initialOrdinal_cardLE_iff hlam).mp (hle.trans hm)
  rcases IsOrdinal.subset_iff.mp hsub with he | he
  · exact (congrArg (fun x : V ↦ x ∈ j ‘ κ) he).mpr hμ
  · exact IsOrdinal.toIsTransitive.mem_trans he hμ

/-- The rank-stage ultrapower also sends its critical point above the initial
index ordinal. The target retains the existing small-family closure. -/
theorem supercompact_ultrapower_stage_above (hAC : InternalChoice V) {κ lam θ : V}
    (h : IsSupercompact κ) (hlam : IsInitialOrdinal lam) (hκlam : κ ⊆ lam)
    (h0 : (∅ : V) ∈ lam) (hθ : IsRegularCardinal θ) (hlamθ : lam ∈ θ) (hκθ : κ ∈ θ) :
    ∃ M j : V, IsTransitive M ∧ IsNonempty M ∧
      IsCodedMembershipEmbedding (hierarchy θ) M j ∧
      IsCriticalPoint (hierarchy θ) j κ ∧ lam ∈ j ‘ κ ∧
      (∀ s, s ∈ M ^ lam → range s ∈ M) ∧
      (∀ y, y ⊆ M → IsNonempty y → y ≤# lam → y ∈ M) ∧
      (∀ α ∈ κ, j ‘ α = α) := by
  let := h.isOrdinal
  let := hθ.1.1
  let := hlam.1
  let := hierarchy_transitive θ
  obtain ⟨U, hU⟩ := h.measure hlam.1 hκlam
  let A := hierarchy θ
  let P := smallSubsetsBelow κ lam
  have hκA : κ ∈ A := ordinal_mem_hierarchy_iff.mpr hκθ
  have hκsub : κ ⊆ A := (hierarchy_transitive θ).transitive _ hκA
  have hA : IsNonempty A := ⟨⟨κ, hκA⟩⟩
  have hsucc : ∀ β ∈ θ, succ β ∈ θ := fun _ hb ↦ regularCardinal_succ_closed hθ hb
  have hsubset : ∀ w z : V, z ∈ A → w ⊆ z → w ∈ A :=
    fun _ _ hz hw ↦ subset_mem_hierarchy_limit hsucc hz hw
  have hsmall : ∀ w : V, w ⊆ A → USmall κ w → w ∈ A :=
    fun _ hw hs ↦ small_subset_mem_hierarchy hθ hκθ hw hs
  have hwf := ultraMemRelation_wellFounded hAC hU.1 hU.2.1 h.2.1 (A := A)
  refine ⟨ultraTarget P U A, ultraEmbedding P U A, ultraTarget_transitive hwf,
    ultraTarget_nonempty hwf hA,
    ultraEmbedding_codedMembershipEmbedding hAC hU.1 hU.2.1 h.2.1 hA,
    ultraEmbedding_criticalPoint hAC h.1 hU h.2.1 hA h0 hκA hκsub hκlam hsubset,
    ultraEmbedding_index_lt hAC hlam hU h.2.1 hsucc hκθ hlamθ,
    fun s hs ↦ range_mem_ultraTarget hAC hU rfl hU.2.1 h.2.1 hA hsmall h0 hs,
    fun y hy hne hcard ↦
      mem_ultraTarget_of_subset_cardLE hAC hU rfl hU.2.1 h.2.1 hA hsmall h0 hy hne hcard,
    ultraEmbedding_fixes_ordinal hAC hU.1 hU.2.1 h.2.1 hA hκsub⟩
end ZFVP

