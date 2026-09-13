import ZFVP.SetTheory.WeaklyLSCofinalityBounds
import ZFVP.SetTheory.NoncofinalMapBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A small family of small collapses has a union surjected by a strictly
lower rank when the indexing rank is below a weakly LS cardinal that does
not exceed the cofinality of the bound. -/
theorem smallIndexedUnion_rank_surjection {lam ν ρ F e₀ x : V} [IsOrdinal lam]
    (hsucc : ∀ β ∈ lam, succ β ∈ lam)
    (hν : IsWeaklyLSCardinal ν) (hνcf : ν ⊆ internalCofinality lam) (hρ : ρ ∈ ν)
    (he₀ : e₀ ∈ F ^ hierarchy ρ) (hre₀ : range e₀ = F) (hne : IsNonempty F)
    (hsmall : ∀ Z ∈ F, HasSmallTransitiveCollapse lam Z) (hx : ∀ Z ∈ F, x ∈ Z) :
    ∃ δ ∈ lam, ∃ e ∈ (⋃ˢ F) ^ hierarchy δ, range e = ⋃ˢ F := by
  classical
  have : IsOrdinal ν := hν.1.1
  have : IsOrdinal ρ := IsOrdinal.of_mem hρ
  have : IsFunction e₀ := IsFunction.of_mem he₀
  let c : V → V := fun Z ↦ mostowskiMap (membershipRelation Z) Z
  have hc : ℒₛₑₜ-function₁ c := by unfold c; definability
  let R : V → V := fun a ↦ rank (range (c (e₀ ‘ a)))
  have hR : ℒₛₑₜ-function₁ R := by unfold R; definability
  let r := definableGraph (hierarchy ρ) R hR
  have hr : r ∈ lam ^ hierarchy ρ := definableGraph_mem_function_of_mapsTo _ _ _ _ (by
    intro a ha
    exact (mem_hierarchy_iff_rank_mem _ _).mp
      (hsmall (e₀ ‘ a) (function_value_mem he₀ ha)).canonical.1)
  obtain ⟨η, hη, hbound⟩ := map_not_cofinal_bounded hr
    (hν.no_small_cofinalMap_of_cofinality (hierarchy_mem hρ) hνcf)
  have : IsOrdinal η := IsOrdinal.of_mem hη
  have hcη : ∀ Z ∈ F, range (c Z) ∈ hierarchy η := by
    intro Z hZ
    obtain ⟨a, haZ⟩ := mem_range_iff.mp (hre₀.symm ▸ hZ)
    have ha : a ∈ hierarchy ρ := domain_eq_of_mem_function he₀ ▸ mem_domain_of_kpair_mem haZ
    have hb := hbound a ha
    rw [show r ‘ a = R a from value_definableGraph _ _ _ ha] at hb
    dsimp only [R] at hb
    rw [value_eq_of_kpair_mem haZ] at hb
    exact (mem_hierarchy_iff_rank_mem _ _).mpr hb
  have hρlam : ρ ∈ lam := internalCofinality_subset lam _ (hνcf _ hρ)
  have hcommon : ∃ ε ∈ lam, ρ ⊆ ε ∧ η ⊆ ε := by
    rcases IsOrdinal.subset_or_supset ρ η with h | h
    · exact ⟨η, hη, h, subset_refl _⟩
    · exact ⟨ρ, hρlam, subset_refl _, h⟩
  obtain ⟨ε, hε, hρε, hηε⟩ := hcommon
  have : IsOrdinal ε := IsOrdinal.of_mem hε
  let δ := succ (succ ε)
  have hδ : δ ∈ lam := hsucc _ (hsucc ε hε)
  let d : V → V := fun Z ↦ converseGraph (c Z)
  have hd : ℒₛₑₜ-function₁ d := by unfold d; definability
  let v : V → V := fun p ↦ (d (e₀ ‘ (kpair.π₁ p))) ‘ (kpair.π₂ p)
  have hv : ℒₛₑₜ-function₁ v := by unfold v; definability
  let E : V → V := fun p ↦ if v p ∈ ⋃ˢ F then v p else x
  have hE : ℒₛₑₜ-function₁ E := by
    have ht : ℒₛₑₜ-relation (fun y p : V ↦
        (v p ∈ ⋃ˢ F ∧ y = v p) ∨ (v p ∉ ⋃ˢ F ∧ y = x)) := by definability
    apply Language.Definable.of_iff ht
    intro q
    change q 0 = E (q 1) ↔ _
    by_cases hq : v (q 1) ∈ ⋃ˢ F <;> simp [E, hq]
  have hxU : x ∈ ⋃ˢ F := by
    obtain ⟨Z, hZ⟩ := hne
    exact mem_sUnion_iff.mpr ⟨Z, hZ, hx Z hZ⟩
  have hmaps : ∀ p ∈ hierarchy δ, E p ∈ ⋃ˢ F := by
    intro p _
    dsimp only [E]
    split_ifs with hp
    · exact hp
    · exact hxU
  refine ⟨δ, hδ, definableGraph (hierarchy δ) E hE,
    definableGraph_mem_function_of_mapsTo _ _ E hE hmaps, ?_⟩
  apply mem_ext
  intro z
  rw [mem_range_iff]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨hpδ, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hp
    exact hmaps p hpδ
  · intro hz
    obtain ⟨Z, hZ, hzZ⟩ := mem_sUnion_iff.mp hz
    obtain ⟨a, haZ⟩ := mem_range_iff.mp (hre₀.symm ▸ hZ)
    have haρ : a ∈ hierarchy ρ := domain_eq_of_mem_function he₀ ▸ mem_domain_of_kpair_mem haZ
    have hca := (hsmall Z hZ).canonical.2
    have haε : a ∈ hierarchy ε := hierarchy_mono hρε a haρ
    have hbε : (c Z) ‘ z ∈ hierarchy ε := hierarchy_mono hηε _
      ((hierarchy_transitive η).mem_trans (function_value_mem hca.2.1 hzZ) (hcη Z hZ))
    have hpairδ : ⟨a, (c Z) ‘ z⟩ₖ ∈ hierarchy δ := kpair_mem_hierarchy_succ_succ haε hbε
    have hvz : v ⟨a, (c Z) ‘ z⟩ₖ = z := by
      dsimp only [v]
      rw [kpair.π₁_kpair, kpair.π₂_kpair, value_eq_of_kpair_mem haZ]
      exact converseGraph_value_value hca.2.1 hca.injective hzZ
    refine ⟨⟨a, (c Z) ‘ z⟩ₖ,
      (pair_mem_definableGraph_iff _ _ _ _ _).mpr ⟨hpairδ, ?_⟩⟩
    simp only [E, hvz, hz, ↓reduceIte]

end ZFVP
