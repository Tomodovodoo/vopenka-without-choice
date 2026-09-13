import ZFVP.ModelTheory.WoodinSourceSeedQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The stage invariant with the manuscript's trivial seed exception.
The recursion branch equations are separate correspondence obligations. -/
structure IsWoodinSourceInvariant (δ θ s K : V) : Prop where
  code : IsForcingIterationCode θ s
  cardinals : IsIterationTable θ K
  seed : woodinIterationStage s K ∅ = woodinSeedStage
  seed_bounded : K ‘ ∅ ∈ δ
  stage : ∀ i ∈ θ, i ≠ ∅ → IsWoodinStage (woodinIterationStage s K i)
  small : ∀ i ∈ θ, i ≠ ∅ → IsWoodinStageSmall (woodinIterationStage s K i)
  inaccessible : ∀ i ∈ θ, i ≠ ∅ → IsChoicelessInaccessible (K ‘ i)
  bounded : ∀ i ∈ θ, K ‘ i ∈ δ
  increasing : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → K ‘ i ∈ K ‘ j

theorem woodinSourceCode_invariant {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (h0 : (∅ : V) ∈ θ)
    (hseed : (woodinSeedCardinal : V) ∈ δ) (hfirst : (woodinSeedCardinal : V) ∈ K ‘ ∅) :
    IsWoodinSourceInvariant δ (woodinSourceIndex θ) (woodinSourceCode θ s)
      (woodinSourceCardinals θ K) := by
  have positive (j : V) (hj : j ∈ θ) : (woodinSeedCardinal : V) ∈ K ‘ j := by
    let := IsOrdinal.of_mem hj
    rcases IsOrdinal.subset_iff.mp (empty_subset j) with he | hj0
    · simpa only [← he] using hfirst
    · let := (h.inaccessible j hj).1
      exact IsOrdinal.toIsTransitive.mem_trans hfirst (h.increasing ∅ h0 j hj hj0)
  refine ⟨woodinSourceCode_valid h.code, woodinSourceCardinals_table _ _,
    woodinSourceCode_seed _ _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [woodinSourceCardinals_seed] using hseed
  · intro i hi hn
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · exact False.elim (hn rfl)
    · rw [woodinSourceCode_stage ha]; exact h.stage a ha
  · intro i hi hn
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · exact False.elim (hn rfl)
    · rw [woodinSourceCode_stage ha]; exact h.small a ha
  · intro i hi hn
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · exact False.elim (hn rfl)
    · rw [woodinSourceCardinals_stage ha]; exact h.inaccessible a ha
  · intro i hi
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · simpa only [woodinSourceCardinals_seed] using hseed
    · rw [woodinSourceCardinals_stage ha]; exact h.bounded a ha
  · intro i hi j hj hij
    rcases woodinSourceIndex_cases hj with rfl | ⟨b, hb, rfl⟩
    · simp at hij
    · rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
      · rw [woodinSourceCardinals_seed, woodinSourceCardinals_stage hb]
        exact positive b hb
      · let := IsOrdinal.of_mem ha
        let := IsOrdinal.of_mem hb
        rw [woodinSourceCardinals_stage ha, woodinSourceCardinals_stage hb]
        exact h.increasing a ha b hb (woodinSourceIndex_mem_iff.mp hij)

theorem woodinSeedCardinal_lt_initial {δ : V} (hδ : IsWoodinSupercompact δ) :
    (woodinSeedCardinal : V) ∈ woodinStageCardinal (woodinInitialStage : V) := by
  have hn := woodinSuccessorStep_preserves_below_supercompact woodinSeedStage_stage woodinSeedStage_small hδ
    (by simpa only [woodinSeedStage, woodinStageCardinal_code] using woodinSeedCardinal_lt hδ)
  simpa only [woodinInitialStage, woodinSeedStage, woodinStageCardinal_code] using hn.2.2.2.1

theorem woodinSourceCode_actual_prefix_invariant {δ θ : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
    (hθ : θ ⊆ δ) (h0 : (∅ : V) ∈ θ) :
    IsWoodinSourceInvariant δ (woodinSourceIndex θ) (woodinSourceCode θ (woodinIterationPrefix θ))
      (woodinSourceCardinals θ (woodinIterationCardinalPrefix θ)) := by
  have hx := woodinIterationExit hδ hAC
  have hs := fun i hi ↦ (hx.2.1 i (hθ i hi)).1
  have hi := woodinIterationPrefix_of_stages hs
  have he := woodinIterationPrefix_initial_stage (woodinIterationHistory_of_stages hs) h0
  apply woodinSourceCode_invariant hi h0 (woodinSeedCardinal_lt hδ)
  have hc : (woodinIterationCardinalPrefix θ) ‘ ∅ = woodinStageCardinal (woodinInitialStage : V) := by
    simpa only [woodinIterationStage, woodinStageCardinal_code] using congrArg woodinStageCardinal he
  rw [hc]
  exact woodinSeedCardinal_lt_initial hδ
theorem woodinSourceCode_actual_full_invariant {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    IsWoodinSourceInvariant (succ δ) (woodinSourceIndex (succ δ))
      (woodinSourceCode (succ δ) (kpair.π₁ (woodinIterationRec δ)))
      (woodinSourceCardinals (succ δ) (kpair.π₂ (woodinIterationRec δ))) := by
  let := hδ.inaccessible.1
  have hx := woodinIterationExit hδ hAC
  have hv := woodinIteration_endpoint_valid hδ hAC
  have h0 : (∅ : V) ∈ δ := IsOrdinal.toIsTransitive.mem_trans (by simp) hδ.inaccessible.2.1
  have he0 := woodinIterationPrefix_initial_stage
    (woodinIterationHistory_of_stages (fun i hi ↦ (hx.2.1 i hi).1)) h0
  have he : woodinIterationStage (kpair.π₁ (woodinIterationRec δ)) (kpair.π₂ (woodinIterationRec δ)) ∅ =
      woodinInitialStage := by
    rw [woodinIteration_endpoint_direct hδ hAC, kpair.π₁_kpair, kpair.π₂_kpair]
    simpa only [woodinIterationStage, forcingDirectCode, forcingThreadCode, forcingIterationCodeNext,
      forcingCodeP_code, forcingCodeR_code, forcingCodet_code, forcingFamilyNext_old h0] using he0
  apply woodinSourceCode_invariant hv.1 (mem_succ_iff.mpr (Or.inr h0))
    (mem_succ_iff.mpr (Or.inr (woodinSeedCardinal_lt hδ)))
  have hc : (kpair.π₂ (woodinIterationRec δ)) ‘ ∅ = woodinStageCardinal (woodinInitialStage : V) := by
    simpa only [woodinIterationStage, woodinStageCardinal_code] using congrArg woodinStageCardinal he
  rw [hc]
  exact woodinSeedCardinal_lt_initial hδ
/-- Source-index transfer of the frozen stage and quotient invariants.
This predicate does not assert the separate recursion correspondence contract. -/
def WoodinSourceInvariantExit (δ : V) : Prop :=
  IsLeastDependentChoiceFailure (woodinSeedCardinal : V) ∧
  (∀ θ : V, IsOrdinal θ → θ ⊆ δ → (∅ : V) ∈ θ →
    IsWoodinSourceInvariant δ (woodinSourceIndex θ) (woodinSourceCode θ (woodinIterationPrefix θ))
      (woodinSourceCardinals θ (woodinIterationCardinalPrefix θ)) ∧
    HasWoodinQuotientClosure (woodinSourceIndex θ) (woodinSourceCode θ (woodinIterationPrefix θ))
      (woodinSourceCardinals θ (woodinIterationCardinalPrefix θ))) ∧
  IsWoodinSourceInvariant (succ δ) (woodinSourceIndex (succ δ))
    (woodinSourceCode (succ δ) (kpair.π₁ (woodinIterationRec δ)))
    (woodinSourceCardinals (succ δ) (kpair.π₂ (woodinIterationRec δ))) ∧
  HasWoodinQuotientClosure (woodinSourceIndex (succ δ))
    (woodinSourceCode (succ δ) (kpair.π₁ (woodinIterationRec δ)))
    (woodinSourceCardinals (succ δ) (kpair.π₂ (woodinIterationRec δ)))

theorem woodinSourceInvariantExit {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) : WoodinSourceInvariantExit δ := by
  refine ⟨woodinSeedCardinal_spec hAC, ?_, woodinSourceCode_actual_full_invariant hδ hAC,
    woodinSourceCode_actual_full_quotient_closure hδ hAC⟩
  intro θ hθo hθ h0
  let := hθo
  exact ⟨woodinSourceCode_actual_prefix_invariant hδ hAC hθ h0,
    woodinSourceCode_actual_prefix_quotient_closure hδ hAC hθ h0⟩
end ZFVP
