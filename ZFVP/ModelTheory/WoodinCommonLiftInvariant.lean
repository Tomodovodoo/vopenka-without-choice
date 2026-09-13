import ZFVP.ModelTheory.WoodinBoundCoherence
import ZFVP.ModelTheory.WoodinCoordinateProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A single base decision controls the common lift at every stage. -/
def IsWoodinCommonLiftBoundAt (θ i p f c d j : V) : Prop :=
  let s := woodinIterationPrefix θ
  i ⊆ j → ∀ r ∈ (forcingCodeP s) ‘ j,
    ⟨r, woodinQuotientBoundRec θ i p f j⟩ₖ ∈ (forcingCodeR s) ‘ j →
    ∀ b ∈ (forcingCodeP s) ‘ i,
      ⟨b, ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ r⟩ₖ ∈ (forcingCodeR s) ‘ i →
      ⟨b, d⟩ₖ ∈ (forcingCodeR s) ‘ i →
      ⟨((forcingCodeL s) ‘ ⟨i, j⟩ₖ) ‘ ⟨r, b⟩ₖ, c ‘ j⟩ₖ ∈ (forcingCodeR s) ‘ j

instance isWoodinCommonLiftBoundAt_definable (θ i p f c d : V) :
    ℒₛₑₜ-predicate[V] (IsWoodinCommonLiftBoundAt θ i p f c d) := by
  unfold IsWoodinCommonLiftBoundAt
  dsimp only
  definability

theorem woodinCommonLiftBoundAt_before {θ i p f c d j : V} [IsOrdinal i]
    (hj : j ∈ i) : IsWoodinCommonLiftBoundAt θ i p f c d j := by
  intro hij
  exact (mem_irrefl j (hij j hj)).elim

theorem woodinCommonLiftBoundAt_base {δ θ i p f c d : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hi : i ∈ θ)
    (hc : c ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hd : d ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hdc : ⟨d, c ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i) :
    IsWoodinCommonLiftBoundAt θ i p f c d i := by
  intro hii r hr _ b hb hbr hbd
  have h := (woodinIterationPrefix_of_stages hs).code.system
  have hl := h.lifts.lift i hi i hi hii r hr b hb hbr
  have he := (h.split.projId hi hl.1).symm.trans hl.2.2
  rw [he]
  exact (h.order.preorder i hi).2.2 b hb d hd _
    (((mem_forcingInverseLimit_iff _ _ _ _ _).mp hc).2.1 i hi) hbd hdc

end ZFVP
