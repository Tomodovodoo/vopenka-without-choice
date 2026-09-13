import ZFVP.ModelTheory.WoodinCollapseInitialModel
import ZFVP.ModelTheory.SuccessorRankLiftChecks
import ZFVP.ModelTheory.SuccessorRankWoodinCollapse
import ZFVP.ModelTheory.SuccessorRankOrdinal
import ZFVP.SetTheory.WoodinCollapseRank
import ZFVP.SetTheory.HighCriticalWoodinWitness

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinCollapseModel

theorem initial_liftData {κ c δ ρ γ e : V} (hκ : IsRegularCardinal κ)
    (hc : IsRegularCardinal c) [IsOrdinal δ] (hcδ : c ⊆ δ)
    {G : Set V} (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G)
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hcrit : IsCriticalPoint (hierarchy (succ ρ)) e c) (hcρ : c ∈ ρ)
    (hκc : κ ∈ c) (hec : e ‘ c = δ) :
    SuccessorRankLiftData (initialContext hκ hc hcδ hG) (woodinCollapseContext hκ δ G hG) ρ γ e := by
  let := hρ.ordinal
  let := hγ.ordinal
  let := hc.1.1
  let := hκ.1.1
  let := hierarchy_transitive (succ ρ)
  have hcV : c ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr hcρ
  have hκV : κ ∈ hierarchy ρ := (hierarchy_transitive ρ).mem_trans hκc hcV
  have hek : e ‘ κ = κ := hcrit.fixed_below hκc
  refine ⟨hρ, hγ, he, woodinCollapse_mem_hierarchy hρ hc.1.1 hκV hcV,
    woodinCollapseOrder_mem_hierarchy hρ hc.1.1 hκV hcV, ?_, ?_, ?_⟩
  · change e ‘ (woodinCollapse κ c) = woodinCollapse κ δ
    simpa only [hek, hec] using successorRankEmbedding_value_woodinCollapse hρ hγ he hc.1.1 hκV hcV
  · change e ‘ (woodinCollapseOrder κ c) = woodinCollapseOrder κ δ
    simpa only [hek, hec] using successorRankEmbedding_value_woodinCollapseOrder hρ hγ he hc.1.1 hκV hcV
  · intro p hp
    change p ∈ G ∧ p ∈ woodinCollapse κ c at hp
    have hpV := woodinCollapse_condition_mem_hierarchy hc
      (IsOrdinal.toIsTransitive.transitive _ hκc) hp.2
    have hep := successorRankEmbedding_fixed_below_criticalPoint hρ hγ he hcrit hcρ p hpV
    change e ‘ p ∈ G
    exact hep.symm ▸ hp.1

end WoodinCollapseModel

theorem HighCriticalWoodinWitness.regular_cutoff {κ δ γ a : V}
    (hκ : IsRegularCardinal κ) [IsOrdinal δ] (hδγ : δ ∈ γ) (hγ : Cn 1 γ)
    (hw : HighCriticalWoodinWitness δ γ a κ) :
    ∃ ρ, ρ ∈ δ ∧ Cn 1 ρ ∧ ∃ x ∈ hierarchy ρ, ∃ e,
      IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e ∧
      ∃ c, IsCriticalPoint (hierarchy (succ ρ)) e c ∧ c ∈ ρ ∧ IsRegularCardinal c ∧
        κ ∈ c ∧ c ∈ δ ∧ e ‘ c = δ ∧ e ‘ x = a := by
  obtain ⟨_, ρ, hρδ, hρ, x, hx, e, he, c, hc, hec, hxa, hκc⟩ := hw
  let := hρ.1.ordinal
  let := hγ.ordinal
  let := hc.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  have hcρ := successorRankEmbedding_criticalPoint_lt_height he hc (hec.symm ▸ hδγ)
  have hcReg := successorRankEmbedding_criticalPoint_regular hρ.1 hγ he hc hcρ
    (subset_trans hκ.2.1 (IsOrdinal.toIsTransitive.transitive _ hκc))
  exact ⟨ρ, hρδ, hρ.1, x, hx, e, he, c, hc, hcρ, hcReg, hκc, hec ▸ hc.lt_value he, hec, hxa⟩

end ZFVP
