import ZFVP.SetTheory.ForcingPairNames
import ZFVP.SetTheory.RankSurjectionOperations
import ZFVP.SetTheory.RegularCofinalSurjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def orderedPairNameSupport (one B R : V) : V :=
  repl (fun z ↦ orderedPairName one (kpair.π₁ z) (kpair.π₂ z)) (by definability) (B ×ˢ R)

theorem mem_orderedPairNameSupport (one B R n : V) :
    n ∈ orderedPairNameSupport one B R ↔
      ∃ b ∈ B, ∃ r ∈ R, n = orderedPairName one b r := by
  rw [orderedPairNameSupport, repl_spec]
  constructor
  · rintro ⟨z, hz, he⟩
    obtain ⟨b, hb, r, hr, rfl⟩ := mem_prod_iff.mp hz
    exact ⟨b, hb, r, hr, by simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using he⟩
  · rintro ⟨b, hb, r, hr, rfl⟩
    exact ⟨⟨b, r⟩ₖ, kpair_mem_iff.mpr ⟨hb, hr⟩,
      by simp only [kpair.π₁_kpair, kpair.π₂_kpair]⟩

noncomputable def orderedPairNameSupportProductMap (one B R P : V) : V :=
  definableGraph ((P ×ˢ B) ×ˢ R)
    (fun z ↦ ⟨orderedPairName one (kpair.π₂ (kpair.π₁ z)) (kpair.π₂ z),
      kpair.π₁ (kpair.π₁ z)⟩ₖ) (by definability)

theorem orderedPairNameSupportProductMap_value {one B R P p b r : V}
    (hp : p ∈ P) (hb : b ∈ B) (hr : r ∈ R) :
    (orderedPairNameSupportProductMap one B R P) ‘ ⟨⟨p, b⟩ₖ, r⟩ₖ =
      ⟨orderedPairName one b r, p⟩ₖ := by
  rw [orderedPairNameSupportProductMap, value_definableGraph _ _ _
    (kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨hp, hb⟩, hr⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

theorem orderedPairNameSupportProductMap_maps (one B R P : V) :
    orderedPairNameSupportProductMap one B R P ∈
      (orderedPairNameSupport one B R ×ˢ P) ^ ((P ×ˢ B) ×ˢ R) := by
  apply definableGraph_mem_function_of_mapsTo
  intro z hz
  obtain ⟨pb, hpb, r, hr, rfl⟩ := mem_prod_iff.mp hz
  obtain ⟨p, hp, b, hb, rfl⟩ := mem_prod_iff.mp hpb
  simp only [kpair.π₁_kpair, kpair.π₂_kpair, kpair_mem_iff]
  exact ⟨(mem_orderedPairNameSupport _ _ _ _).mpr ⟨b, hb, r, hr, rfl⟩, hp⟩

theorem orderedPairNameSupportProductMap_range (one B R P : V) :
    range (orderedPairNameSupportProductMap one B R P) = orderedPairNameSupport one B R ×ˢ P := by
  have hf := orderedPairNameSupportProductMap_maps one B R P
  apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
  intro z hz
  obtain ⟨n, hn, p, hp, rfl⟩ := mem_prod_iff.mp hz
  obtain ⟨b, hb, r, hr, rfl⟩ := (mem_orderedPairNameSupport _ _ _ _).mp hn
  have hdom : ⟨⟨p, b⟩ₖ, r⟩ₖ ∈ (P ×ˢ B) ×ˢ R :=
    kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨hp, hb⟩, hr⟩
  have hval := orderedPairNameSupportProductMap_value (one := one) hp hb hr
  rw [← hval]
  exact function_value_mem (mem_function_range_of_mem_function hf) hdom

theorem orderedPairNameSupport_product_surjection (one B R P : V) :
    ∃ g ∈ (orderedPairNameSupport one B R ×ˢ P) ^ ((P ×ˢ B) ×ˢ R),
      range g = orderedPairNameSupport one B R ×ˢ P :=
  ⟨_, orderedPairNameSupportProductMap_maps one B R P, orderedPairNameSupportProductMap_range one B R P⟩

theorem orderedPairNameSupport_rank_surjection {δ η ν one B R P e : V} [IsOrdinal δ]
    (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ) (hη : η ∈ δ) (hν : ν ∈ δ)
    (hB : B ⊆ hierarchy ν) (hP : P ⊆ hierarchy ν)
    (he : e ∈ R ^ (hierarchy η)) (hre : range e = R)
    (hne : IsNonempty (orderedPairNameSupport one B R ×ˢ P)) :
    ∃ ε ∈ δ, ∃ g ∈ (orderedPairNameSupport one B R ×ˢ P) ^ (hierarchy ε),
      range g = orderedPairNameSupport one B R ×ˢ P := by
  let := IsOrdinal.of_mem hη
  let := IsOrdinal.of_mem hν
  have hcommon : ∃ β ∈ δ, hierarchy ν ⊆ hierarchy β ∧ hierarchy η ⊆ hierarchy β := by
    rcases IsOrdinal.subset_or_supset ν η with h | h
    · exact ⟨η, hη, hierarchy_mono h, subset_refl _⟩
    · exact ⟨ν, hν, subset_refl _, hierarchy_mono h⟩
  obtain ⟨β, hβ, hνβ, hηβ⟩ := hcommon
  let := IsOrdinal.of_mem hβ
  obtain ⟨q, hq, hrq⟩ := product_surjection (P := P ×ˢ B) he hre
  have hf := orderedPairNameSupportProductMap_maps one B R P
  have hrf := orderedPairNameSupportProductMap_range one B R P
  have hg := compose_function hq hf
  have hrg := range_compose_surjective hq hf hrq hrf
  have hdom : (P ×ˢ B) ×ˢ hierarchy η ⊆ hierarchy (succ (succ (succ (succ β)))) := by
    intro z hz
    obtain ⟨pb, hpb, r, hr, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨p, hp, b, hb, rfl⟩ := mem_prod_iff.mp hpb
    apply kpair_mem_hierarchy_succ_succ
    · exact kpair_mem_hierarchy_succ_succ (hνβ p (hP p hp)) (hνβ b (hB b hb))
    · apply hierarchy_mono (show β ⊆ succ (succ β) from
        subset_trans (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self β))
          (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self (succ β))))
      exact hηβ r hr
  obtain ⟨g, hg, hrg⟩ := surjection_extension hdom hg hrg hne
  exact ⟨_, hδ _ (hδ _ (hδ _ (hδ _ hβ))), g, hg, hrg⟩

end ZFVP
