import ZFVP.SetTheory.ForcingIterationSystem

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingIterationSystem.empty (P R π E L t : V) :
    IsForcingIterationSystem ∅ P R π E L t := by
  constructor <;> constructor <;> intro i hi <;> simp at hi

theorem forcingInitialColumn {P R π E L t Q T ρ F M u : V}
    (hR : IsForcingPreorder Q T) (ht : IsForcingTop Q T u) :
    IsForcingIterationColumn ∅ P R π E L t Q T ρ F M u := by
  refine ⟨?_, ⟨hR, ?_, ?_⟩, ?_, ⟨ht, ?_, ?_⟩, ?_, ?_⟩
  · constructor <;> intro i hi <;> simp at hi
  · intro i hi; simp at hi
  · intro i hi; simp at hi
  · constructor <;> intro i hi <;> simp at hi
  · intro i hi; simp at hi
  · intro i hi; simp at hi
  · constructor <;> intro i hi <;> simp at hi
  · constructor; intro i hi; simp at hi

theorem forcingInitialSystem {Q T u : V}
    (hR : IsForcingPreorder Q T) (ht : IsForcingTop Q T u) :
    IsForcingIterationSystem (succ ∅) (forcingFamilyNext ∅ ∅ Q) (forcingFamilyNext ∅ ∅ T)
      (forcingMatrixNext ∅ ∅ ∅ (identity Q)) (forcingMatrixNext ∅ ∅ ∅ (identity Q))
      (forcingMatrixNext ∅ ∅ ∅ (forcingIdentityLift Q)) (forcingFamilyNext ∅ ∅ u) :=
  (IsForcingIterationSystem.empty ∅ ∅ ∅ ∅ ∅ ∅).extend (forcingInitialColumn hR ht)

theorem singletonForcing_preorder (u : V) : IsForcingPreorder ({u} : V) (({u} : V) ×ˢ {u}) := by
  refine ⟨fun _ hz ↦ hz, ?_, ?_⟩
  · intro p hp
    exact kpair_mem_iff.mpr ⟨hp, hp⟩
  · intro p hp q _ r hr _ _
    exact kpair_mem_iff.mpr ⟨hp, hr⟩

theorem singletonForcing_top (u : V) : IsForcingTop ({u} : V) (({u} : V) ×ˢ {u}) u := by
  refine ⟨by simp, ?_⟩
  intro p hp
  exact kpair_mem_iff.mpr ⟨hp, by simp⟩

end ZFVP
