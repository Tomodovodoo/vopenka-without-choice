import ZFVP.ModelTheory.WoodinCollapseLiftBranch
import ZFVP.ModelTheory.SuccessorRankPairPreimages
import ZFVP.SetTheory.SigmaOneStarUnbounded

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinCollapseModel

set_option maxHeartbeats 1600000 in
theorem dependentChoiceAt_restored {κ δ : V} (hκ : IsRegularCardinal κ)
    (hδ : HasHighCriticalWoodinWitnesses δ) (hκδ : κ ∈ δ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) {G : Set V}
    (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G) :
    InternalDependentChoiceAt ((woodinCollapseContext hκ δ G hG).check κ) := by
  let B := woodinCollapseContext hκ δ G hG
  let := hκ.1.1
  let := hδ.1.1
  intro X R _ hserial
  obtain ⟨τ, rfl⟩ := B.ofName_surjective X
  obtain ⟨σ, rfl⟩ := B.ofName_surjective R
  let a := ⟨τ.val, σ.val⟩ₖ
  let η := δ ∪ rank a
  let : IsOrdinal η := ordinal_union_ordinal δ (rank a)
  obtain ⟨γ, hηγ, hγ⟩ := sigmaOneStarCorrect_unbounded η
  let := hγ.1.ordinal
  have hδγ : δ ∈ γ := ordinal_mem_of_subset_mem
    (show δ ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inl hz)) hηγ
  have ha : a ∈ hierarchy γ := (mem_hierarchy_iff_rank_mem _ _).mpr (ordinal_mem_of_subset_mem
    (show rank a ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inr hz)) hηγ)
  have hw := hδ.2.2 γ hδγ hγ a ha κ hκδ
  obtain ⟨ρ, hρδ, hρ, x, hx, e, he, c, hc, hcρ, hcReg, hκc, hcδ, hec, hxa⟩ :=
    hw.regular_cutoff hκ hδγ hγ.1
  let := hρ.ordinal
  let := hc.ordinal
  let := hierarchy_transitive (succ ρ)
  have hcsub : c ⊆ δ := IsOrdinal.toIsTransitive.transitive _ hcδ
  let A := initialContext hκ hcReg hcsub hG
  have hπ : IsForcingRetraction A.P A.R B.P B.R (woodinCollapseProjection κ c δ) :=
    woodinCollapse_retraction hκ hcReg hcsub
  have hAG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P := fun _ ↦ Iff.rfl
  let L : SuccessorRankLiftData A B ρ γ e := initial_liftData hκ hcReg hcsub hG
    hρ hγ.1 he hc hcρ hκc hec
  have hcV : c ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr hcρ
  have hκV : κ ∈ hierarchy ρ := (hierarchy_transitive ρ).mem_trans hκc hcV
  have hfix : ∀ α ∈ κ, e ‘ α = α := fun α hα ↦
    hc.fixed_below (IsOrdinal.toIsTransitive.mem_trans hα hκc)
  have heone : e ‘ A.one = ∅ := hfix ∅ (hκ.2.1 ∅ (by simp))
  obtain ⟨u, v, hu, hv, _, hue, hve⟩ := successorRankEmbedding_pair_preimages hρ hγ.1 he hx hxa
  have huN : IsForcingName A.P u := by
    apply (successorRankEmbedding_forcingName_iff hρ hγ.1 he L.poset_mem hu).mpr
    rw [L.poset_image, hue]
    exact τ.property
  have hvN : IsForcingName A.P v := by
    apply (successorRankEmbedding_forcingName_iff hρ hγ.1 he L.poset_mem hv).mpr
    rw [L.poset_image, hve]
    exact σ.property
  let U : ForcingName A.P := ⟨u, huN⟩
  let W : ForcingName A.P := ⟨v, hvN⟩
  let Xu := B.ofName ⟨u, huN.mono hπ.inclusion⟩
  let Rv := B.ofName ⟨v, hvN.mono hπ.inclusion⟩
  have hXu : Xu ∈ domain (L.graph hπ) := (L.graph_domain hπ Xu).mpr ⟨U, hu, rfl⟩
  have hRv : Rv ∈ domain (L.graph hπ) := (L.graph_domain hπ Rv).mpr ⟨W, hv, rfl⟩
  have hjX : (L.graph hπ) ‘ Xu = B.ofName τ := by
    rw [show Xu = B.ofName ⟨U.val, U.property.mono hπ.inclusion⟩ from rfl, L.graph_value hπ hAG U hu]
    exact congrArg B.ofName (Subtype.ext hue)
  have hjR : (L.graph hπ) ‘ Rv = B.ofName σ := by
    rw [show Rv = B.ofName ⟨W.val, W.property.mono hπ.inclusion⟩ from rfl, L.graph_value hπ hAG W hv]
    exact congrArg B.ofName (Subtype.ext hve)
  have hbranch := lifted_branch hκ hG L hπ hAG rfl heone hρδ hκV hfix hDC hXu hRv
    (by simpa only [hjX, hjR] using hserial)
  simpa only [hjX, hjR, IsDependentChoicePath] using hbranch

end WoodinCollapseModel
end ZFVP
