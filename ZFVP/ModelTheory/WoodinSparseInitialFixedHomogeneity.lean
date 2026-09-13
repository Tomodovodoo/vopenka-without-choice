import ZFVP.ModelTheory.WoodinSparseInitialHomogeneity

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseInitial_poset {Ω : V} (hΩ : IsWoodinSupercompact Ω) :
    IsForcingPoset (woodinSparseInitialCarrier : V) woodinSparseInitialOrder := by
  have hf := woodinSparseInitialCollapseMap_isomorphism hΩ
  refine ⟨woodinSparseInitial_preorder hΩ, ?_⟩
  intro p hp q hq hpq hqp
  have he := (woodinCollapse_poset _ _).2 _ (function_value_mem hf.1 hp)
    _ (function_value_mem hf.1 hq) ((hf.2.2.2 _ hp _ hq).mp hpq)
    ((hf.2.2.2 _ hq _ hp).mp hqp)
  have hcancel := congrArg (fun x ↦ (converseGraph (woodinSparseInitialCollapseMap : V)) ‘ x) he
  simpa only [hf.inverse_value hp, hf.inverse_value hq] using hcancel

theorem woodinSparseInitial_weak_homogeneous_fixed_top {Ω p q : V}
    (hΩ : IsWoodinSupercompact Ω) (hp : p ∈ (woodinSparseInitialCarrier : V))
    (hq : q ∈ (woodinSparseInitialCarrier : V)) :
    ∃ π : V, IsForcingAutomorphism woodinSparseInitialCarrier woodinSparseInitialOrder π ∧
      π ‘ ∅ = ∅ ∧ ForcingCompatible woodinSparseInitialCarrier woodinSparseInitialOrder (π ‘ p) q := by
  obtain ⟨π, hπ, hc⟩ := woodinSparseInitial_weak_homogeneous hΩ hp hq
  exact ⟨π, hπ, forcingAutomorphism_top (woodinSparseInitial_poset hΩ)
    (woodinSparseInitial_empty_top hΩ) hπ, hc⟩

end ZFVP
