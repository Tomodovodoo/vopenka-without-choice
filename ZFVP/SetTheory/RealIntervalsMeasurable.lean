import ZFVP.SetTheory.RealRationalNullSingleton

/-! Every rational basic interval is Carathéodory measurable. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realInterval_lebesgueMeasurable (a b : InternalRational V) :
    IsRealLebesgueMeasurable (realInterval a.val b.val) := by
  have h := realLebesgueMeasurable_inter
    (realLebesgueMeasurable_complement (realLowerHalf_lebesgueMeasurable a))
    (realLebesgueMeasurable_sdiff (realLowerHalf_lebesgueMeasurable b)
      (realNull_lebesgueMeasurable (realNull_rationalSingleton b)))
  have he : ((dedekindReals V) \ realLowerHalf a.val) ∩
      (realLowerHalf b.val \ ({rationalCut b.val} : V)) = realInterval a.val b.val := by
    apply mem_ext
    intro x
    simp only [mem_inter_iff, mem_sdiff_iff, mem_realLowerHalf_iff,
      mem_singleton_iff, mem_dedekindReals_iff, mem_realInterval_iff]
    constructor
    · rintro ⟨⟨hx, ha⟩, ⟨⟨_, hb⟩, hxb⟩⟩
      have hxa : ¬ x ⊆ rationalCut a.val := fun h ↦ ha ⟨hx, h⟩
      refine ⟨hx, ⟨(dedekindCuts_comparable hx (rationalCut_isCut a.property)).resolve_left hxa, ?_⟩,
        ⟨hb, hxb⟩⟩
      intro heq
      exact hxa (heq ▸ subset_refl _)
    · rintro ⟨hx, hax, hxb⟩
      refine ⟨⟨hx, ?_⟩, ⟨⟨hx, hxb.1⟩, hxb.2⟩⟩
      intro ha
      exact hax.2 (subset_antisymm hax.1 ha.2)
  rwa [he] at h

end ZFVP
