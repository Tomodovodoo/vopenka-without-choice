import ZFVP.ModelTheory.WoodinFixedPointRank
import ZFVP.ModelTheory.WoodinEndpointStageMap

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ γ : V} (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
  (hγ : γ ∈ δ) (hfix : (kpair.π₂ (woodinIterationRec δ)) ‘ γ = γ)
include hδ hAC hγ

theorem woodinIteration_fixedPoint_extends :
    ForcingCodeExtends (kpair.π₁ (woodinIterationRec γ)) (kpair.π₁ (woodinIterationRec δ)) ∧
      kpair.π₂ (woodinIterationRec γ) ⊆ kpair.π₂ (woodinIterationRec δ) := by
  let := hδ.inaccessible.1
  exact woodinIterationRec_extends_previous (woodinIterationHistory_of_stages
    (fun _ hi ↦ ((woodinIterationExit hδ hAC).2.1 _ hi).1)) hγ

include hfix

theorem woodinIteration_fixedPoint_inaccessible : IsChoicelessInaccessible γ :=
  hfix ▸ (woodinIteration_endpoint_valid hδ hAC).1.inaccessible γ (mem_succ_iff.mpr (Or.inr hγ))

theorem woodinIteration_fixedPoint_cardinal : (kpair.π₂ (woodinIterationRec γ)) ‘ γ = γ := by
  have h := ((woodinIterationExit hδ hAC).2.1 γ hγ).1
  have he := (woodinIteration_fixedPoint_extends hδ hAC hγ).2
  rw [h.cardinals.value_of_subset (woodinIteration_endpoint_valid hδ hAC).1.cardinals he
    (mem_succ_self γ)]
  exact hfix

/-- Below a fixed point, every earlier stage cardinal is strictly below it. -/
theorem woodinIteration_fixedPoint_prefix :
    IsWoodinIteration γ γ (woodinIterationPrefix γ) (woodinIterationCardinalPrefix γ) := by
  let := hδ.inaccessible.1
  have hi := woodinIteration_fixedPoint_inaccessible hδ hAC hγ hfix
  let := hi.1
  have h := ((woodinIterationExit hδ hAC).2.1 γ hγ).1
  have hs : ∀ i ∈ γ, IsWoodinIteration δ (succ i)
      (kpair.π₁ (woodinIterationRec i)) (kpair.π₂ (woodinIterationRec i)) :=
    fun _ hi' ↦ ((woodinIterationExit hδ hAC).2.1 _ (IsOrdinal.toIsTransitive.mem_trans hi' hγ)).1
  have hp := woodinIterationPrefix_of_stages hs
  have hzero : γ ≠ ∅ := by
    intro he
    exact not_mem_empty (he ▸ hi.2.1)
  have he : woodinIterationCardinalPrefix γ ⊆ kpair.π₂ (woodinIterationRec γ) := by
    rw [woodinIterationRec_rule]
    exact woodinStageRule_cardinals_extend hp.cardinals hzero
  refine ⟨hp.code, hp.cardinals, hp.stage, hp.small, hp.inaccessible, ?_, hp.increasing⟩
  intro i hi'
  rw [hp.cardinals.value_of_subset h.cardinals he hi']
  have hb := h.increasing i (mem_succ_iff.mpr (Or.inr hi')) γ (mem_succ_self γ) hi'
  rwa [woodinIteration_fixedPoint_cardinal hδ hAC hγ hfix] at hb

/-- The actual recursion takes the direct branch at every fixed point. -/
theorem woodinIteration_fixedPoint_direct :
    woodinIterationRec γ = ⟨forcingDirectCode γ (woodinIterationPrefix γ),
      forcingFamilyNext γ (woodinIterationCardinalPrefix γ) γ⟩ₖ := by
  have hi := woodinIteration_fixedPoint_inaccessible hδ hAC hγ hfix
  let := hi.1
  have hlim : ∀ i ∈ γ, succ i ∈ γ := fun _ hm ↦ regularCardinal_succ_closed hi.regular hm
  have he := (woodinIteration_fixedPoint_prefix hδ hAC hγ hfix).limitCardinal_eq_endpoint hlim
  have h0 : γ ≠ ∅ := by
    intro hz
    exact not_mem_empty (hz ▸ hi.2.1)
  have hn : γ ≠ succ (⋃ˢ γ) := by
    intro hz
    have hm : ⋃ˢ γ ∈ γ := (congrArg (fun x : V ↦ (⋃ˢ γ) ∈ x) hz).mpr (mem_succ_self (⋃ˢ γ))
    have hh := hlim _ hm
    rw [← hz] at hh
    exact mem_irrefl _ hh
  simpa only [he] using woodinIterationRec_direct h0 hn (he.symm ▸ hi)

theorem woodinIteration_fixedPoint_poset :
    (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ γ =
      forcingDirectLimit γ (forcingCodeP (woodinIterationPrefix γ))
        (forcingCodeπ (woodinIterationPrefix γ)) (forcingCodeE (woodinIterationPrefix γ))
        (forcingCodeUniverse (woodinIterationPrefix γ)) := by
  have hc := ((woodinIterationExit hδ hAC).2.1 γ hγ).1.code
  rw [← hc.tableP.value_of_subset (woodinIteration_endpoint_valid hδ hAC).1.code.tableP
    (woodinIteration_fixedPoint_extends hδ hAC hγ).1.subP (mem_succ_self γ)]
  rw [woodinIteration_fixedPoint_direct hδ hAC hγ hfix, kpair.π₁_kpair]
  exact forcingThreadCode_poset _ _ _

theorem woodinIteration_fixedPoint_order :
    (forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ γ =
      forcingThreadOrder γ (forcingCodeR (woodinIterationPrefix γ))
        (forcingDirectLimit γ (forcingCodeP (woodinIterationPrefix γ))
          (forcingCodeπ (woodinIterationPrefix γ)) (forcingCodeE (woodinIterationPrefix γ))
          (forcingCodeUniverse (woodinIterationPrefix γ))) := by
  have hc := ((woodinIterationExit hδ hAC).2.1 γ hγ).1.code
  rw [← hc.tableR.value_of_subset (woodinIteration_endpoint_valid hδ hAC).1.code.tableR
    (woodinIteration_fixedPoint_extends hδ hAC hγ).1.subR (mem_succ_self γ)]
  rw [woodinIteration_fixedPoint_direct hδ hAC hγ hfix, kpair.π₁_kpair]
  exact forcingThreadCode_order _ _ _

end ZFVP
