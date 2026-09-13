import ZFVP.ModelTheory.ModelEmbeddingHierarchy
import ZFVP.ModelTheory.CriticalPowerRestrictions

/-! Restricting a graph above its critical point preserves that critical point. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCriticalPoint.restrict {A B f κ a : V} [IsTransitive A] [IsTransitive a]
    (hκ : IsCriticalPoint A f κ) (hf : f ∈ B ^ A) (ha : a ⊆ A) (hκa : κ ∈ a) :
    IsCriticalPoint a (f ↾ a) κ := by
  let := IsFunction.of_mem hf
  have hv : ∀ x ∈ a, (f ↾ a) ‘ x = f ‘ x := by
    intro x hx
    exact value_restrict (by rw [domain_eq_of_mem_function hf]; exact ha x hx) hx
  apply IsCriticalPoint.of_fixed_below hκ.ordinal hκa
  · rw [hv κ hκa]
    exact hκ.moved
  · intro α hα
    rw [hv α ((inferInstance : IsTransitive a).mem_trans hα hκa)]
    exact hκ.fixed_below hα

end ZFVP
