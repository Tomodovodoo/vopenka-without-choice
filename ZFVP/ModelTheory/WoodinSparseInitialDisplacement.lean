import ZFVP.ModelTheory.WoodinSparseInitialFixedHomogeneity

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseInitialDisplacement (p q : V) : V :=
  let f := (woodinSparseInitialCollapseMap : V)
  let c := woodinPrefixCutoff {∅} (({∅} : V) ×ˢ {∅}) ∅ woodinSeedCardinal
  compose f (compose (woodinCollapseDisplacement woodinSeedCardinal c (f ‘ p) (f ‘ q)) (converseGraph f))

instance woodinSparseInitialDisplacement_definable :
    ℒₛₑₜ-function₂[V] woodinSparseInitialDisplacement := by
  unfold woodinSparseInitialDisplacement
  dsimp only
  apply Language.DefinableFunction₂.comp
  · definability
  · apply Language.DefinableFunction₂.comp
    · apply Language.DefinableFunction₄.comp <;> definability
    · definability
theorem woodinSparseInitialDisplacement_spec {Ω p q : V} (hΩ : IsWoodinSupercompact Ω)
    (hp : p ∈ (woodinSparseInitialCarrier : V)) (hq : q ∈ (woodinSparseInitialCarrier : V)) :
    IsForcingAutomorphism woodinSparseInitialCarrier woodinSparseInitialOrder
      (woodinSparseInitialDisplacement p q) ∧
    (woodinSparseInitialDisplacement p q) ‘ ∅ = ∅ ∧
    ForcingCompatible woodinSparseInitialCarrier woodinSparseInitialOrder
      ((woodinSparseInitialDisplacement p q) ‘ p) q := by
  have hf := woodinSparseInitialCollapseMap_isomorphism hΩ
  have hpQ := function_value_mem hf.1 hp
  have hqQ := function_value_mem hf.1 hq
  have hg := woodinCollapseDisplacement_automorphism woodinSeedCardinal_regular hpQ hqQ
  have hgi : IsForcingIsomorphism _ _ _ _ _ := hg
  have hi := hf.inverse
  have ha : IsForcingAutomorphism woodinSparseInitialCarrier woodinSparseInitialOrder
      (woodinSparseInitialDisplacement p q) := hf.comp (hgi.comp hi)
  refine ⟨ha, forcingAutomorphism_top (woodinSparseInitial_poset hΩ)
    (woodinSparseInitial_empty_top hΩ) ha, ?_⟩
  obtain ⟨r, hr, hrp, hrq⟩ := woodinCollapseDisplacement_common_extension woodinSeedCardinal_regular hpQ hqQ
  refine ⟨(converseGraph (woodinSparseInitialCollapseMap : V)) ‘ r,
    function_value_mem hi.1 hr, ?_, ?_⟩
  · rw [woodinSparseInitialDisplacement,
      value_compose_of_mem_function hf.1 (compose_function hg.1 hi.1) hp,
      value_compose_of_mem_function hg.1 hi.1 hpQ]
    exact (hi.2.2.2 _ hr _ (function_value_mem hg.1 hpQ)).mp hrp
  · have he := (hi.2.2.2 _ hr _ hqQ).mp hrq
    rwa [hf.inverse_value hq] at he

end ZFVP



