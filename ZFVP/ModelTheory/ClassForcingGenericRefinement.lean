import ZFVP.ModelTheory.ClassForcingCompatibilityReduction
import ZFVP.ModelTheory.ClassForcingDenseRestriction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

noncomputable def genericStageContext (i : V) [IsOrdinal i] {G : Set V}
    (hG : IsExternalForcingGeneric (T.P i) (T.R i) G) : ForcingContext V :=
  ⟨T.P i, T.R i, T.top i, G, T.order i inferInstance, T.top_spec i inferInstance, hG⟩

/-- A set-stage quotient statement valid in all generics through a base
condition yields ground predense refinements. A class condition below both
the quotient bound and the base condition is the required common strength. -/
theorem boundedDenseFamily_refinement_of_generics [Countable V]
    (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    {I i k p u c : V} [IsOrdinal i] [IsOrdinal k] (hik : i ⊆ k)
    (hp : p ∈ T.P k) (hu : u ∈ T.P i)
    (hcp : T.LE c ⟨k, p⟩ₖ) (hcu : T.LE c ⟨i, u⟩ₖ)
    (hsem : ∀ (G : Set V) (hG : IsExternalForcingGeneric (T.P i) (T.R i) G),
      u ∈ G → ∀ a ∈ I,
      let A := T.genericStageContext i hG
      ∃ d ∈ T.boundedConditions k, D a d ∧
        ⟨A.check p, A.check (T.reduceCondition k d)⟩ₖ ∈
          forcingSeparativeOrder (A.projectionQuotient (T.P k) (T.projection i k))
            (A.projectionQuotientOrder (T.P k) (T.R k) (T.projection i k))) :
    T.ClassDenseRefinements D I c (T.boundedDenseFamily D hDdef I k) := by
  apply T.boundedDenseFamily_refinement D hDdef
  intro a ha r hr hrc
  have hrp := T.le_trans hrc hcp
  have hru := T.le_trans hrc hcu
  have hrK := T.projectCondition_mem (i := k) hr
  have hπr := T.projection_mem hik hrK
  have hbelow : ⟨(T.projection i k) ‘ (T.projectCondition k r), u⟩ₖ ∈ T.R i := by
    apply (T.below_section i k inferInstance inferInstance hik _ hrK u hu).mp
    exact (T.below_stage_iff hr (T.section_mem hik hu)).mp
      (T.le_trans hru (T.section_equivalent hik hu).1)
  obtain ⟨G, hG, hrG⟩ := exists_externalForcingGeneric (T.order i inferInstance) hπr
  have huG := hG.1.2.2.1 _ hrG u hu hbelow
  obtain ⟨d, hd, hDa, hpd⟩ := hsem G hG huG a ha
  let A := T.genericStageContext i hG
  have hcomp := T.classCompatible_of_quotient_separative hik A rfl hr hp hrp hrG hpd
  refine ⟨d, hd, hDa, ?_⟩
  obtain ⟨s, hs, hsr, hsd⟩ := hcomp
  exact ⟨s, hs, hsr, T.le_trans hsd (T.reduceCondition_equivalent hd).1⟩

end DefinableForcingTower
end ZFVP
