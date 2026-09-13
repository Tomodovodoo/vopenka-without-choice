import ZFVP.SetTheory.LimitStageEmbedding
import ZFVP.SetTheory.SmallSubsetsStage
import ZFVP.SetTheory.DerivedFineMeasure

/-! # What one Magidor witness gives

A single small embedding `e : V_lb → V_gam` with critical point `ab`, target index closed under
successor and `lb` below `e ‘ ab`, already yields the whole package used by Magidor's theorem:
the source index is closed under successor, the critical point is an initial ordinal above `ω`,
and every ordinal of the source index carries a normal fine measure on `P_ab` of it, with the
measure itself living inside the source stage.

Nothing new is proved here. The successor closure comes from
`ZFVP.SetTheory.LimitStageEmbedding`, the transport of `P_ab(ξ)` from
`ZFVP.SetTheory.SmallSubsetsStage`, and the measure from `ZFVP.SetTheory.DerivedFineMeasure`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- What one Magidor witness gives: the source stage index is closed under successor, the
critical point is an initial ordinal above omega, and every ordinal of the source stage carries
a normal fine measure on `P_ab` of it, lying inside the source stage. -/
theorem magidorWitness_measures {κ lb gam ab e : V} [IsOrdinal lb] [IsOrdinal gam]
    (hgam : ∀ ξ ∈ gam, succ ξ ∈ gam)
    (he : IsCodedMembershipEmbedding (hierarchy lb) (hierarchy gam) e)
    (hc : IsCriticalPoint (hierarchy lb) e ab) (hek : e ‘ ab = κ) (hlbk : lb ∈ κ) :
    (∀ ξ ∈ lb, succ ξ ∈ lb) ∧ IsInitialOrdinal ab ∧ (ω : V) ∈ ab ∧
      ∀ ξ ∈ lb, ∃ U ∈ hierarchy lb, IsNormalFineMeasure ab ξ U := by
  let := hierarchy_transitive lb
  let := hierarchy_transitive gam
  let := hc.ordinal
  have hlb : ∀ ξ ∈ lb, succ ξ ∈ lb := successorClosed_of_embedding hgam he
  have habA : ab ∈ hierarchy lb := hc.mem_domain
  have hab : ab ∈ lb := ordinal_mem_hierarchy_iff.mp habA
  have hlbe : lb ∈ e ‘ ab := hek ▸ hlbk
  refine ⟨hlb, limitRankEmbedding_criticalPoint_initial hlb he hc,
    omega_mem_criticalPoint hlb he hc, ?_⟩
  intro ξ hξ
  have hξo : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hξA : ξ ∈ hierarchy lb := ordinal_mem_hierarchy_iff.mpr hξ
  have hP : e ‘ (smallSubsetsBelow ab ξ) = smallSubsetsBelow (e ‘ ab) (e ‘ ξ) :=
    value_smallSubsetsBelow hlb hgam he hab hξ
  refine ⟨derivedFineMeasure e ab ξ, ?_, derived_isNormalFineMeasure hlb he hc hξ hlbe hP⟩
  exact subsets_mem_hierarchy hlb (smallSubsetsBelow_mem_hierarchy hlb habA hξA)
    (fun X hX ↦ mem_power_iff.mpr ((mem_derivedFineMeasure_iff e ab ξ X).mp hX).1)

end ZFVP
