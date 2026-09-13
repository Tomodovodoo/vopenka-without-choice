import ZFVP.ModelTheory.RankCollapseTwoStepLift
import ZFVP.ModelTheory.RankCollapseCombinedClosure
import ZFVP.ModelTheory.RankCollapseCombinedWellOrdering
import ZFVP.ModelTheory.SuccessorRankGenericBranch
import ZFVP.ModelTheory.HighCriticalInaccessibleCutoff
import ZFVP.ModelTheory.SuccessorRankPairPreimages
import ZFVP.SetTheory.FiniteCofinality

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]

namespace ForcingContext
variable (A : ForcingContext V)

theorem rankCollapse_combined_dependentChoiceAt {κ δ : V}
    (hδ : IsWoodinSupercompact δ) (hP : A.P ∈ hierarchy δ) (hR : A.R ∈ hierarchy δ)
    (hκδ : κ ∈ δ) (hκsub : κ ⊆ δ) (hz : (∅ : V) ∈ κ)
    (hκ : IsRegularCardinal (A.check κ)) (hDC : ∀ α ∈ A.check κ, InternalDependentChoiceAt α)
    {H : Set A.Model}
    (hH : IsExternalForcingGeneric (woodinCollapse (A.check κ) (A.check δ))
      (woodinCollapseOrder (A.check κ) (A.check δ)) H) :
    InternalDependentChoiceAt ((A.rankCollapseCombinedContext hδ.inaccessible hP hκsub hz hH).check κ) := by
  let B := A.rankCollapseCombinedContext hδ.inaccessible hP hκsub hz hH
  let := hδ.1.1
  let := IsOrdinal.of_mem hκδ
  intro X R _ hserial
  obtain ⟨τ, rfl⟩ := B.ofName_surjective X
  obtain ⟨σ, rfl⟩ := B.ofName_surjective R
  let a := ⟨τ.val, σ.val⟩ₖ
  let θ := δ ∪ rank a
  let : IsOrdinal θ := ordinal_union_ordinal δ (rank a)
  obtain ⟨γ, hθγ, hγ⟩ := sigmaOneStarCorrect_unbounded θ
  let := hγ.1.ordinal
  have hδγ : δ ∈ γ := ordinal_mem_of_subset_mem
    (show δ ⊆ θ from fun z hz ↦ mem_union_iff.mpr (Or.inl hz)) hθγ
  have ha : a ∈ hierarchy γ := (mem_hierarchy_iff_rank_mem _ _).mpr (ordinal_mem_of_subset_mem
    (show rank a ⊆ θ from fun z hz ↦ mem_union_iff.mpr (Or.inr hz)) hθγ)
  let η := (κ ∪ rank A.P) ∪ rank A.R
  have hηδ : η ∈ δ := ordinal_union_mem
    (ordinal_union_mem hκδ ((mem_hierarchy_iff_rank_mem _ _).mp hP))
    ((mem_hierarchy_iff_rank_mem _ _).mp hR)
  let := IsOrdinal.of_mem hηδ
  obtain ⟨ρ, hρδ, hρ, x, hx, e, he, c, hc, hcρ, hci, hηc, hcδ, hec, hxa⟩ :=
    (hδ.highCritical.2.2 γ hδγ hγ a ha η hηδ).inaccessible_cutoff hδγ hγ.1
  let := hρ.1.ordinal
  let := hci.1
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  have hκc : κ ∈ c := ordinal_mem_of_subset_mem
    (show κ ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inl hz)))) hηc
  have hPc : A.P ∈ hierarchy c := (mem_hierarchy_iff_rank_mem _ _).mpr (ordinal_mem_of_subset_mem
    (show rank A.P ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inr hz)))) hηc)
  have hRc : A.R ∈ hierarchy c := (mem_hierarchy_iff_rank_mem _ _).mpr (ordinal_mem_of_subset_mem
    (show rank A.R ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inr hz)) hηc)
  have hcs : c ⊆ δ := IsOrdinal.toIsTransitive.transitive _ hcδ
  have hks : κ ⊆ c := IsOrdinal.toIsTransitive.transitive _ hκc
  let Hc := woodinCollapseInitialGeneric (A.check κ) (A.check c) H
  have hHc := A.rankCollapse_initial_generic hci hPc hκ hcs hH
  let C := A.rankCollapseCombinedContext hci hPc hks hz hHc
  have hTail : ∀ p, p ∈ Hc ↔ p ∈ H ∧ p ∈ woodinCollapse (A.check κ) (A.check c) := fun _ ↦ Iff.rfl
  have hG : ∀ p, p ∈ C.G ↔ p ∈ B.G ∧ p ∈ C.P :=
    A.rankCollapse_combined_restrict_of_filter hci hδ.inaccessible hPc hP hks hκsub hcs hz hHc hH hTail
  have hCB : C.P ⊆ B.P := twoStepConditions_posetName_mono
    (rankCollapseName_mono_countable A.order A.top hci hδ.inaccessible hPc hks hcs)
  let L : SuccessorRankLiftData C B ρ γ e := A.rankCollapse_successorRankLift hρ.1 hγ.1 he hc hcρ
    hci hδ.inaccessible hPc hRc hκc hks hcs hz hec hHc hH hTail
  have hcV : c ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr hcρ
  have hκV : κ ∈ hierarchy ρ := (hierarchy_transitive ρ).mem_trans hκc hcV
  have hPρ : A.P ∈ hierarchy ρ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hcρ) A.P hPc
  have hfix : ∀ α ∈ κ, e ‘ α = α := fun α hα ↦
    hc.fixed_below (IsOrdinal.toIsTransitive.mem_trans hα hκc)
  have heone : e ‘ C.one = B.one := by
    change e ‘ ⟨A.one, (∅ : V)⟩ₖ = ⟨A.one, (∅ : V)⟩ₖ
    apply successorRankEmbedding_fixed_below_criticalPoint hρ.1 hγ.1 he hc hcρ
    exact kpair_mem_hierarchy_limit hci.rankCriterion.2.2.1
      ((hierarchy_transitive c).mem_trans A.top.1 hPc)
      (ordinal_mem_hierarchy_iff.mpr (IsOrdinal.toIsTransitive.mem_trans hz hκc))
  obtain ⟨u, v, hu, hv, _, hue, hve⟩ := successorRankEmbedding_pair_preimages hρ.1 hγ.1 he hx hxa
  have huN : IsForcingName C.P u := by
    apply (successorRankEmbedding_forcingName_iff hρ.1 hγ.1 he L.poset_mem hu).mpr
    rw [L.poset_image, hue]
    exact τ.property
  have hvN : IsForcingName C.P v := by
    apply (successorRankEmbedding_forcingName_iff hρ.1 hγ.1 he L.poset_mem hv).mpr
    rw [L.poset_image, hve]
    exact σ.property
  let U : ForcingName C.P := ⟨u, huN⟩
  let W : ForcingName C.P := ⟨v, hvN⟩
  let Xu := B.ofName ⟨u, huN.mono hCB⟩
  let Rv := B.ofName ⟨v, hvN.mono hCB⟩
  have hXu : Xu ∈ domain (L.genericGraph hCB) := (L.genericGraph_domain hCB Xu).mpr ⟨U, hu, rfl⟩
  have hRv : Rv ∈ domain (L.genericGraph hCB) := (L.genericGraph_domain hCB Rv).mpr ⟨W, hv, rfl⟩
  have hjX : (L.genericGraph hCB) ‘ Xu = B.ofName τ := by
    rw [show Xu = B.ofName ⟨U.val, U.property.mono hCB⟩ from rfl, L.genericGraph_value hCB hG U hu]
    exact congrArg B.ofName (Subtype.ext hue)
  have hjR : (L.genericGraph hCB) ‘ Rv = B.ofName σ := by
    rw [show Rv = B.ofName ⟨W.val, W.property.mono hCB⟩ from rfl, L.genericGraph_value hCB hG W hv]
    exact congrArg B.ofName (Subtype.ext hve)
  have hw : IsWellOrderable Xu := A.rankCollapse_combined_lowerName_wellOrderable
    hδ.inaccessible hP hκsub hz hH hκ hρ.1 hPρ hρδ ⟨u, huN.mono hCB⟩ hu
  have hp : ∀ α ∈ κ, ∀ (Y : C.Model) (f : B.Model),
      f ∈ C.genericInclusion B hG Y ^ B.check α →
      ∃ g ∈ Y ^ C.check α, C.genericInclusion B hG g = f := by
    intro α hα Y f hf
    exact A.rankCollapse_combined_function_of_closed hci hδ.inaccessible hPc hP hks hκsub hcs hz
      hHc hH hTail hκ hDC hα hf
  have hb := L.genericGraph_dependentChoicePath hCB hG heone hκV hfix hp hXu hRv hw
    (by simpa only [hjX, hjR] using hserial)
  simpa only [hjX, hjR, IsDependentChoicePath] using hb

end ForcingContext
end ZFVP
