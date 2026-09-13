import ZFVP.ModelTheory.ClassForcingPretameness
import ZFVP.ModelTheory.ProjectionQuotient
import ZFVP.SetTheory.ForcingSeparativeOrder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

/-- Compatibility with a condition at a fixed stage can be tested by the
projection of an arbitrary class condition to that stage. -/
theorem classCompatible_stage_iff {k c q : V} [IsOrdinal k]
    (hc : T.Condition c) (hq : q ∈ T.P k) :
    T.ClassCompatible c ⟨k, q⟩ₖ ↔
      ForcingCompatible (T.P k) (T.R k) (T.projectCondition k c) q := by
  constructor
  · rintro ⟨d, hd, hdc, hdq⟩
    exact ⟨T.projectCondition k d, T.projectCondition_mem hd,
      T.projectCondition_order hdc, (T.below_stage_iff hd hq).mp hdq⟩
  · rintro ⟨r, hr, hrc, hrq⟩
    obtain ⟨d, hd, hdc, hdr⟩ := T.lift_stage_condition hc hr hrc
    exact ⟨d, hd, hdc, T.le_trans hdr ((T.le_sameStage_iff hr hq).mpr hrq)⟩

theorem classCompatible_bounded_iff {k c d : V} [IsOrdinal k]
    (hc : T.Condition c) (hd : d ∈ T.boundedConditions k) :
    T.ClassCompatible c d ↔
      ForcingCompatible (T.P k) (T.R k) (T.projectCondition k c) (T.reduceCondition k d) := by
  rw [← T.classCompatible_stage_iff hc (T.reduceCondition_mem hd)]
  have he := T.reduceCondition_equivalent hd
  exact ⟨fun ⟨r, hr, hrc, hrd⟩ ↦ ⟨r, hr, hrc, T.le_trans hrd he.2⟩,
    fun ⟨r, hr, hrc, hrd⟩ ↦ ⟨r, hr, hrc, T.le_trans hrd he.1⟩⟩

/-- A separative comparison in the quotient provides ground compatibility
with any class condition whose stage projection lies in that quotient. -/
theorem classCompatible_of_quotient_separative {i k c p q : V}
    [IsOrdinal i] [IsOrdinal k] (hik : i ⊆ k)
    (A : ForcingContext V) (hAP : A.P = T.P i)
    (hc : T.Condition c) (hp : p ∈ T.P k)
    (hcp : T.LE c ⟨k, p⟩ₖ)
    (hcG : (T.projection i k) ‘ (T.projectCondition k c) ∈ A.G)
    (hsep : ⟨A.check p, A.check q⟩ₖ ∈
      forcingSeparativeOrder (A.projectionQuotient (T.P k) (T.projection i k))
        (A.projectionQuotientOrder (T.P k) (T.R k) (T.projection i k))) :
    T.ClassCompatible c ⟨k, q⟩ₖ := by
  have hπ : T.projection i k ∈ A.P ^ T.P k := by
    rw [hAP]
    exact T.projection_function i k inferInstance inferInstance hik
  have hproj := T.projectCondition_mem (i := k) hc
  have hcQ := (A.check_mem_projectionQuotient_iff hπ).mpr ⟨hproj, hcG⟩
  obtain ⟨hpQ, hqQ, hs⟩ := (kpair_mem_forcingSeparativeOrder _ _ _ _).mp hsep
  have hq := ((A.check_mem_projectionQuotient_iff hπ).mp hqQ).1
  have hcpQ : ⟨A.check (T.projectCondition k c), A.check p⟩ₖ ∈
      A.projectionQuotientOrder (T.P k) (T.R k) (T.projection i k) :=
    (A.projectionQuotientOrder_pair_iff _ _ _ _ _).mpr
      ⟨A.check_kpair _ _ ▸ (A.check_mem_iff _ _).mpr ((T.below_stage_iff hc hp).mp hcp), hcQ, hpQ⟩
  obtain ⟨u, hu, huc, huq⟩ := hs _ hcQ hcpQ
  obtain ⟨r, hr, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ u).mp hu
  have hrc := ((A.projectionQuotientOrder_pair_iff _ _ _ _ _).mp huc).1
  have hrq := ((A.projectionQuotientOrder_pair_iff _ _ _ _ _).mp huq).1
  rw [← A.check_kpair, A.check_mem_iff] at hrc hrq
  exact (T.classCompatible_stage_iff hc hq).mpr ⟨r, hr, hrc, hrq⟩

end DefinableForcingTower
end ZFVP
