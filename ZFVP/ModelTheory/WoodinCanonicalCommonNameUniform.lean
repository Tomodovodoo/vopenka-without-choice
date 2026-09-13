import ZFVP.ModelTheory.WoodinCanonicalSparseCommonExtension
import ZFVP.ModelTheory.WoodinCanonicalTailNameUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem canonicalTailCommonName_comp {n : ℕ} {P R top f p q : (Fin n → V) → V}
    (hP : Language.DefinableFunction ℒₛₑₜ P) (hR : Language.DefinableFunction ℒₛₑₜ R)
    (ht : Language.DefinableFunction ℒₛₑₜ top) (hf : Language.DefinableFunction ℒₛₑₜ f)
    (hp : Language.DefinableFunction ℒₛₑₜ p) (hq : Language.DefinableFunction ℒₛₑₜ q) :
    Language.DefinableFunction ℒₛₑₜ (fun v ↦
      canonicalTailCommonName (P v) (R v) (top v) (f v) (p v) (q v)) := by
  unfold canonicalTailCommonName normalizedBinaryNameUnion
  apply Language.DefinableFunction₄.comp hP hR ht
  apply Language.DefinableFunction₂.comp
  · apply Language.DefinableFunction₅.comp <;> assumption
  · exact hq

end ZFVP
