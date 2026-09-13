import ZFVP.Syntax.ProgramZFVPProvability
import ZFVP.Syntax.PrimitiveProgramTheoryComposition

/-! The explicit ZF+VP proof predicate satisfies the second derivability condition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram ProvabilityAbstraction

theorem programZFVPProvability_D2 (φ ψ : SetTheorySentence) :
    𝗜𝚺₁ ⊢ programZFVPProvability (φ 🡒 ψ) 🡒
      programZFVPProvability φ 🡒 programZFVPProvability ψ := by
  apply complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simp only [models_iff, Semiformula.Realize, LogicalConnective.HomClass.map_imply]
  change (M↓[ℒₒᵣ] ⊧ programZFVPProvableFormula.val/[⌜φ 🡒 ψ⌝]) →
    (M↓[ℒₒᵣ] ⊧ programZFVPProvableFormula.val/[⌜φ⌝]) →
    (M↓[ℒₒᵣ] ⊧ programZFVPProvableFormula.val/[⌜ψ⌝])
  simp only [models_programZFVPProvableFormula_quote]
  exact ProgramTheoryProvable.modusPonens φ ψ

instance programZFVPProvability_HBL2 : programZFVPProvability.HBL2 where
  D2 := programZFVPProvability_D2 _ _

end ZFVP
