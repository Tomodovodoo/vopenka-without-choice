import ZFVP.SetTheory.ForcingMapExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem function_eq_identity_of_values {f A : V} (hf : f ∈ A ^ A)
    (h : ∀ x ∈ A, f ‘ x = x) : f = identity A := by
  let := IsFunction.of_mem hf
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hf z hz)
    exact kpair_mem_identity_iff.mpr ⟨hx, (h x hx).symm.trans (value_eq_of_kpair_mem hz)⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := mem_identity_iff.mp hz
    have hp : ⟨x, f ‘ x⟩ₖ ∈ f := kpair_value_mem ((domain_eq_of_mem_function hf).symm ▸ hx)
    simpa only [h x hx] using hp

theorem IsSplitForcingSystem.projection_diagonal {θ P π E i : V}
    (h : IsSplitForcingSystem θ P π E) (m : IsFunctionalSplitForcingSystem θ P π E)
    (hi : i ∈ θ) : π ‘ ⟨i, i⟩ₖ = identity (P ‘ i) :=
  function_eq_identity_of_values (m.projection i hi i hi (subset_refl _)) (fun _ hp ↦ h.projId hi hp)

theorem IsSplitForcingSystem.section_diagonal {θ P π E i : V}
    (h : IsSplitForcingSystem θ P π E) (m : IsFunctionalSplitForcingSystem θ P π E)
    (hi : i ∈ θ) : E ‘ ⟨i, i⟩ₖ = identity (P ‘ i) :=
  function_eq_identity_of_values (m.sectionMap i hi i hi (subset_refl _)) (h.secId i hi)

end ZFVP


