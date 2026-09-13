import ZFVP.SetTheory.ClassForcingTower
import ZFVP.ModelTheory.ForcingSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

theorem splitProjection {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j) :
    IsForcingSplitProjection (T.P i) (T.R i) (T.P j) (T.R j)
      (T.projection i j) (T.sectionMap i j) :=
  ⟨⟨T.projection_function i j inferInstance inferInstance hij,
      T.projection_mono i j inferInstance inferInstance hij,
      T.lift i j inferInstance inferInstance hij⟩,
    T.section_function i j inferInstance inferInstance hij,
    T.projection_section i j inferInstance inferInstance hij,
    T.below_section i j inferInstance inferInstance hij⟩

end DefinableForcingTower
end ZFVP
