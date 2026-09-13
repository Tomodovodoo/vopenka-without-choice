import ZFVP.SetTheory.ElementaryDefined
import Foundation.FirstOrder.SetTheory.LoewenheimSkolem

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

theorem eval_of_countable_zf {n : ℕ} (φ : SetTheorySemisentence n)
    (h : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
      [Countable W], ∀ b : Fin n → W, φ.Evalb b)
    {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (v : Fin n → V) : φ.Evalb v := by
  let U := Hull (Set.range v)
  have hZF : U↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
    (inferInstance : U ≡ₑ[ℒₛₑₜ] V).modelsTheory.mpr inferInstance
  let b : Fin n → U := fun i ↦ ⟨v i, Hull.subset (Set.range v) ⟨i, rfl⟩⟩
  exact (Hull.hull_models_iff (s := Set.range v) (b := b) (φ := φ)).mp (h U b)

end ZFVP

