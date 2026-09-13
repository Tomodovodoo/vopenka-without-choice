import ZFVP.SetTheory.SchroederBernstein

/-! Images compose as actual sets, and identity graphs fix subsets. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem graphImage_compose (e h X : V) : graphImage h (graphImage e X) = graphImage (compose e h) X := by
  apply mem_ext
  intro z
  simp only [mem_graphImage_iff, kpair_mem_compose_iff]
  constructor
  · rintro ⟨y, ⟨x, hx, hxy⟩, hyz⟩
    exact ⟨x, hx, y, hxy, hyz⟩
  · rintro ⟨x, hx, y, hxy, hyz⟩
    exact ⟨y, ⟨x, hx, hxy⟩, hyz⟩

theorem graphImage_identity {D X : V} (hX : X ⊆ D) : graphImage (SetTheory.identity D) X = X := by
  apply mem_ext
  intro x
  simp only [mem_graphImage_iff, kpair_mem_identity_iff]
  exact ⟨fun ⟨y, hy, _, hyx⟩ ↦ hyx ▸ hy, fun hx ↦ ⟨x, hx, hX x hx, rfl⟩⟩

end ZFVP
