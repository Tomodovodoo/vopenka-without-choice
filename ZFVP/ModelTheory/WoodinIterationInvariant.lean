import ZFVP.ModelTheory.WoodinIterationSuccessor
import ZFVP.ModelTheory.WoodinSuccessorBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Frozen restored-stage invariant. Closure and bound-construction lemmas are
separate predicates; they do not add fields to this structure. The trivial
source seed is represented before restored stage zero. -/
structure IsWoodinIteration (δ θ s K : V) : Prop where
  code : IsForcingIterationCode θ s
  cardinals : IsIterationTable θ K
  stage : (∀ i ∈ θ, IsWoodinStage (woodinIterationStage s K i))
  small : (∀ i ∈ θ, IsWoodinStageSmall (woodinIterationStage s K i))
  inaccessible : (∀ i ∈ θ, IsChoicelessInaccessible (K ‘ i))
  bounded : (∀ i ∈ θ, K ‘ i ∈ δ)
  increasing : (∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → K ‘ i ∈ K ‘ j)

theorem IsWoodinIteration.successor {δ k s K : V} [IsOrdinal k]
    (hδ : IsWoodinSupercompact δ) (h : IsWoodinIteration δ (succ k) s K) :
    IsWoodinIteration δ (succ (succ k)) (woodinIterationSuccessor k s K)
      (woodinIterationCardinalNext k s K) := by
  let x := woodinIterationStage s K k
  have hx : IsWoodinStage x := h.stage k (by simp)
  have hs : IsWoodinStageSmall x := h.small k (by simp)
  have hb : woodinStageCardinal x ∈ δ := by
    simpa [x, woodinIterationStage] using h.bounded k (by simp)
  have hn := woodinSuccessorStep_preserves_below_supercompact hx hs hδ hb
  let := hδ.inaccessible.1
  have hP := hs δ hδ.inaccessible hb
  have hR := hx.order_mem_hierarchy hδ.inaccessible.rankCriterion.2.2.1 hP
  obtain ⟨c, _, hc⟩ := hδ.strictPrefixCutoff hx.1 hx.2.1 hP hR hb
    hx.2.2.2.1 hx.2.2.2.2
  have hc' : IsWoodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
      ((forcingCodet s) ‘ k) (K ‘ k) c := by
    simpa [x, woodinIterationStage] using hc
  have hreg : ∀ p ∈ (forcingCodeP s) ‘ k, p ∈ forcingFormula
      ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) regularCardinalFormula
      (standardTuple ![checkName ((forcingCodet s) ‘ k) (K ‘ k)]) := by
    simpa [x, woodinIterationStage] using hx.2.2.2.1
  have hnew : (woodinIterationCardinalNext k s K) ‘ (succ k) =
      woodinStageCardinal (woodinSuccessorStep x) := forcingFamilyNext_new _ _ _
  have hold : ∀ i ∈ succ k, (woodinIterationCardinalNext k s K) ‘ i = K ‘ i := by
    intro i hi
    exact forcingFamilyNext_old hi
  have hl := (woodinPrefixCutoff_spec hc).2.1
  have hPl := hs _ hl.2.1 hl.1
  refine ⟨woodinIterationSuccessor_valid h.code hreg hc' (by
      simpa [x, woodinIterationStage] using hPl),
    woodinIterationCardinalNext_table _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · rw [woodinIterationSuccessor_stage]; exact hn.1
    · rw [woodinIterationSuccessor_old hi]; exact h.stage i hi
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · rw [woodinIterationSuccessor_stage]; exact hn.2.1
    · rw [woodinIterationSuccessor_old hi]; exact h.small i hi
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · rw [hnew]; exact hn.2.2.1
    · rw [hold i hi]; exact h.inaccessible i hi
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · rw [hnew]; exact hn.2.2.2.2
    · rw [hold i hi]; exact h.bounded i hi
  · intro i hi j hj hij
    rcases mem_succ_iff.mp hj with rfl | hj
    · rw [hnew, hold i hij]
      have hknew : K ‘ k ∈ woodinStageCardinal (woodinSuccessorStep x) := by
        simpa [x, woodinIterationStage] using hn.2.2.2.1
      rcases mem_succ_iff.mp hij with rfl | hik
      · exact hknew
      · let := hn.2.2.1.1
        exact IsOrdinal.toIsTransitive.transitive _ hknew _
          (h.increasing i (mem_succ_iff.mpr (Or.inr hik)) k (by simp) hik)
    · have hi' : i ∈ succ k :=
        IsOrdinal.toIsTransitive.transitive _ hj _ hij
      rw [hold i hi', hold j hj]
      exact h.increasing i hi' j hj hij

end ZFVP
