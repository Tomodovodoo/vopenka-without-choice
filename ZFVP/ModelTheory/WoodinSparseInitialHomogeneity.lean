import ZFVP.ModelTheory.SingletonNormalizedCollapseIsomorphism
import ZFVP.ModelTheory.WoodinSparseInitial
import ZFVP.ModelTheory.ForcingIsomorphismComposition
import ZFVP.ModelTheory.ForcingIsomorphismTransport
import ZFVP.SetTheory.WoodinCollapseDisplacement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseInitialCollapseMap : V :=
  compose (converseGraph woodinSparseInitialMap)
    (singletonNormalizedCollapseMap ∅ woodinSeedCardinal
      (woodinPrefixCutoff {∅} (({∅} : V) ×ˢ {∅}) ∅ woodinSeedCardinal))

instance woodinSparseInitialCollapseMap_definable :
    Language.DefinableFunction₀ ℒₛₑₜ (woodinSparseInitialCollapseMap : V) := by
  unfold woodinSparseInitialCollapseMap
  definability
theorem woodinSparseInitialCollapseMap_isomorphism {Ω : V} (hΩ : IsWoodinSupercompact Ω) :
    IsForcingIsomorphism woodinSparseInitialCarrier woodinSparseInitialOrder
      (woodinCollapse woodinSeedCardinal (woodinPrefixCutoff {∅} (({∅} : V) ×ˢ {∅}) ∅ woodinSeedCardinal))
      (woodinCollapseOrder woodinSeedCardinal (woodinPrefixCutoff {∅} (({∅} : V) ×ˢ {∅}) ∅ woodinSeedCardinal))
      woodinSparseInitialCollapseMap := by
  obtain ⟨hc, hp, hk, _⟩ := woodinNormalizationInitial_inputs hΩ
  exact woodinSparseInitial_isomorphism.inverse.comp (singletonNormalizedCollapseMap_isomorphism hc hp hk)

theorem IsForcingIsomorphism.weak_homogeneity {P R Q S f : V}
    (hf : IsForcingIsomorphism P R Q S f)
    (hQ : ∀ a ∈ Q, ∀ b ∈ Q, ∃ π, IsForcingAutomorphism Q S π ∧ ForcingCompatible Q S (π ‘ a) b)
    {p q : V} (hp : p ∈ P) (hq : q ∈ P) :
    ∃ π, IsForcingAutomorphism P R π ∧ ForcingCompatible P R (π ‘ p) q := by
  have hpQ := function_value_mem hf.1 hp
  have hqQ := function_value_mem hf.1 hq
  obtain ⟨g, hg, r, hr, hrp, hrq⟩ := hQ _ hpQ _ hqQ
  have hgi : IsForcingIsomorphism Q S Q S g := hg
  have hi := hf.inverse
  refine ⟨compose f (compose g (converseGraph f)), hf.comp (hgi.comp hi),
    (converseGraph f) ‘ r, function_value_mem hi.1 hr, ?_, ?_⟩
  · rw [value_compose_of_mem_function hf.1 (compose_function hg.1 hi.1) hp,
      value_compose_of_mem_function hg.1 hi.1 hpQ]
    exact (hi.2.2.2 _ hr _ (function_value_mem hg.1 hpQ)).mp hrp
  · have he := (hi.2.2.2 _ hr _ hqQ).mp hrq
    rwa [hf.inverse_value hq] at he

theorem woodinSparseInitial_weak_homogeneous {Ω p q : V} (hΩ : IsWoodinSupercompact Ω)
    (hp : p ∈ (woodinSparseInitialCarrier : V)) (hq : q ∈ (woodinSparseInitialCarrier : V)) :
    ∃ π : V, IsForcingAutomorphism woodinSparseInitialCarrier woodinSparseInitialOrder π ∧
      ForcingCompatible woodinSparseInitialCarrier woodinSparseInitialOrder (π ‘ p) q := by
  apply (woodinSparseInitialCollapseMap_isomorphism hΩ).weak_homogeneity _ hp hq
  intro a ha b hb
  exact woodinCollapse_weak_homogeneous woodinSeedCardinal_regular ha hb

end ZFVP


