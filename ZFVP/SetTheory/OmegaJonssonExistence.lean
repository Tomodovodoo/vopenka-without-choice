import ZFVP.SetTheory.OmegaJonssonSelection
import ZFVP.SetTheory.PowerCountableSubsets
import ZFVP.ModelTheory.OmegaJonssonEmbedding

/-! Existence of an omega-Jonsson function, the Erdos-Hajnal construction.

Let `lam` be an infinite initial ordinal of cofinality `ω` all of whose smaller power sets inject
into it, and assume internal choice. Then `lam` carries an omega-Jonsson function: a function `F`
whose arguments are countably enumerated subsets of `lam` and whose values lie in `lam`, such that
every subset `A ⊆ lam` that `lam` injects into contains, for each `γ ∈ lam`, a countably
enumerated set that `F` sends to `γ`.

The construction lists the demands `⟨A, γ⟩` in a transfinite sequence of length `θ`, the cardinal
of the demand set, and answers demand number `ξ` with a countably enumerated subset of `A` that
has not been used at any earlier stage. The pool never runs out: the countably enumerated subsets
of `A` are at least as many as those of `lam`, hence at least `θ` many, while only `ξ`-many have
been used and `ξ ∈ θ` with `θ` initial. The counting input is
`power_cardLE_countableSubsets`, which is where the hypotheses on `lam` are spent. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- At an infinite initial ordinal of cofinality `ω` whose smaller power sets all inject into it,
internal choice produces an omega-Jonsson function. -/
theorem exists_omegaJonsson (hAC : InternalChoice V) {lam : V}
    (hlam : IsInitialOrdinal lam) (hω : (ω : V) ∈ lam)
    (hcof : ∃ s, s ∈ lam ^ (ω : V) ∧ IsCofinalMap lam (ω : V) s)
    (hsl : ∀ α ∈ lam, ℘ α ≤# lam) :
    ∃ F, F ⊆ ℘ lam ×ˢ lam ∧ IsOmegaJonsson F lam := by
  have hord : IsOrdinal lam := hlam.1
  have hωsub : (ω : V) ⊆ lam := IsOrdinal.toIsTransitive.transitive _ hω
  -- Step 1: a selection device on the countably enumerated subsets of `lam`.
  have hPwo : IsWellOrderable (countableSubsets lam) :=
    wellOrderable_of_internalChoice hAC _
  have hρord : IsOrdinal (wellOrderedCardinal (countableSubsets lam)) :=
    (wellOrderedCardinal_initial hPwo).1
  have hρP : wellOrderedCardinal (countableSubsets lam) ≋ countableSubsets lam :=
    wellOrderedCardinal_cardEQ hPwo
  obtain ⟨u, hu, huinj⟩ := hρP.2
  -- Step 2 and 3: the demand set and its size.
  have hpow : ℘ lam ≤# countableSubsets lam :=
    power_cardLE_countableSubsets hAC hlam hω hcof hsl
  have hlamP : lam ≤# countableSubsets lam := cardLE_countableSubsets hω
  have hωρ : (ω : V) ⊆ wellOrderedCardinal (countableSubsets lam) := by
    have hωinit : IsInitialOrdinal (ω : V) :=
      ⟨IsOrdinal.ω, fun n hn ↦ omega_not_cardLE_natural hn⟩
    exact (initialOrdinal_cardLE_iff hωinit).mp
      (((cardLE_of_subset hωsub).trans hlamP).trans hρP.2)
  have hDP : jonssonDemands lam ≤# countableSubsets lam := by
    have h2 := ordinal_prod_cardLE_union_omega (wellOrderedCardinal (countableSubsets lam))
    rw [union_eq_iff_right.mpr hωρ] at h2
    exact ((((cardLE_of_subset jonssonDemands_subset).trans
      (prod_cardLE_prod hpow hlamP)).trans (prod_cardLE_prod hρP.2 hρP.2)).trans h2).trans hρP.1
  -- A default demand, so the enumeration below is total.
  have hd₀ : (⟨lam, (∅ : V)⟩ₖ : V) ∈ jonssonDemands lam :=
    kpair_mem_jonssonDemands_iff.mpr ⟨subset_refl lam, hωsub _ empty_mem_ω, CardLE.refl lam⟩
  -- Step 4: enumerate the demands by their cardinal.
  have hDwo : IsWellOrderable (jonssonDemands lam) := wellOrderable_of_internalChoice hAC _
  have hθinit : IsInitialOrdinal (wellOrderedCardinal (jonssonDemands lam)) :=
    wellOrderedCardinal_initial hDwo
  have hθord : IsOrdinal (wellOrderedCardinal (jonssonDemands lam)) := hθinit.1
  have hθD : wellOrderedCardinal (jonssonDemands lam) ≋ jonssonDemands lam :=
    wellOrderedCardinal_cardEQ hDwo
  obtain ⟨w, hw, hwinj⟩ := hθD.2
  have hθP : wellOrderedCardinal (jonssonDemands lam) ≤# countableSubsets lam := hθD.1.trans hDP
  -- Abbreviations for the recursion data.
  set D := jonssonDemands lam with hDdef
  set θ := wellOrderedCardinal D with hθdef
  set e := converseGraph w with hedef
  set d₀ := (⟨lam, (∅ : V)⟩ₖ : V) with hd₀def
  set G := jonssonSelection lam D e d₀ u θ with hGdef
  clear_value G d₀ e θ D
  -- Every stage carries a demand, so the data read off it behave.
  have hdem : ∀ ξ : V, kpair.π₁ (demandAt D e d₀ ξ) ⊆ lam ∧
      kpair.π₂ (demandAt D e d₀ ξ) ∈ lam ∧ lam ≤# kpair.π₁ (demandAt D e d₀ ξ) := by
    intro ξ
    have hq : demandAt D e d₀ ξ ∈ jonssonDemands lam := by
      rw [← hDdef]; exact demandAt_mem hd₀ ξ
    obtain ⟨hq1, hq2⟩ := mem_jonssonDemands_iff.mp hq
    obtain ⟨A, hA, γ, hγ, hqe⟩ := mem_prod_iff.mp hq1
    rw [hqe] at hq2 ⊢
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hq2 ⊢
    exact ⟨mem_power_iff.mp hA, hγ, hq2⟩
  -- Step 6: at every stage some countably enumerated subset of the demand is still unused.
  have hfresh : ∀ ξ ∈ θ, G ‘ ξ ∈ jonssonCandidates lam D e d₀ ξ (G ↾ ξ) := by
    intro ξ hξ
    have : IsOrdinal ξ := IsOrdinal.of_mem hξ
    have hsubθ : ξ ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hξ
    rw [hGdef, jonssonSelection_value hξ]
    apply wellOrderSelection_mem hu huinj
    · intro a ha
      exact (mem_countableSubsetsOf_iff.mp (mem_jonssonCandidates_iff.mp ha).1).1
    · rw [← hGdef]
      by_contra hempty
      have hcover : countableSubsetsOf lam (kpair.π₁ (demandAt D e d₀ ξ)) ⊆ range (G ↾ ξ) := by
        intro a ha
        by_contra hna
        exact hempty ⟨a, mem_jonssonCandidates_iff.mpr ⟨ha, hna⟩⟩
      have hres : G ↾ ξ ∈ range (G ↾ ξ) ^ ξ := by
        rw [hGdef]
        exact restrict_mem_function (jonssonSelection_isFunction lam D e d₀ u θ)
          (by rw [domain_jonssonSelection]; exact hsubθ)
      have hrange : range (G ↾ ξ) ≤# ξ :=
        cardLE_of_surjective_function (ordinal_wellOrderable ξ) hres rfl
      have hbig : countableSubsets lam ≤#
          countableSubsetsOf lam (kpair.π₁ (demandAt D e d₀ ξ)) :=
        countableSubsets_cardLE_countableSubsetsOf (hdem ξ).1 (hdem ξ).2.2
      exact hθinit.2 ξ hξ
        ((hθP.trans hbig).trans ((cardLE_of_subset hcover).trans hrange))
  -- Step 7: the selection is injective.
  have hGinj : ∀ ξ ∈ θ, ∀ η ∈ θ, G ‘ ξ = G ‘ η → ξ = η := by
    have hone : ∀ ξ ∈ θ, ∀ η ∈ ξ, G ‘ ξ ≠ G ‘ η := by
      intro ξ hξ η hη heq
      refine (mem_jonssonCandidates_iff.mp (hfresh ξ hξ)).2 ?_
      rw [hGdef]
      exact (mem_range_restrict_jonssonSelection_iff hξ).mpr
        ⟨η, hη, by rw [← hGdef]; exact heq.symm⟩
    intro ξ hξ η hη heq
    have : IsOrdinal ξ := IsOrdinal.of_mem hξ
    have : IsOrdinal η := IsOrdinal.of_mem hη
    rcases IsOrdinal.mem_trichotomy ξ η with h | h | h
    · exact absurd heq.symm (hone η hη ξ h)
    · exact h
    · exact absurd heq (hone ξ hξ η h)
  -- Step 8: read the omega-Jonsson function off the selection.
  refine ⟨jonssonFunction lam G D e d₀ θ, jonssonFunction_subset, ?_⟩
  have hmemF : ∀ q : V, q ∈ jonssonFunction lam G D e d₀ θ ↔ q ∈ ℘ lam ×ˢ lam ∧
      ∃ ξ ∈ θ, q = ⟨G ‘ ξ, kpair.π₂ (demandAt D e d₀ ξ)⟩ₖ := fun _ ↦ mem_jonssonFunction_iff
  have hGmem : ∀ ξ ∈ θ, G ‘ ξ ∈ countableSubsets lam ∧
      G ‘ ξ ⊆ kpair.π₁ (demandAt D e d₀ ξ) :=
    fun ξ hξ ↦ mem_countableSubsetsOf_iff.mp (mem_jonssonCandidates_iff.mp (hfresh ξ hξ)).1
  have hpairF : ∀ ξ ∈ θ, (⟨G ‘ ξ, kpair.π₂ (demandAt D e d₀ ξ)⟩ₖ : V) ∈ jonssonFunction lam G D e d₀ θ := by
    intro ξ hξ
    exact (hmemF _).mpr ⟨kpair_mem_iff.mpr
      ⟨mem_power_iff.mpr (countableSubsets_subset (hGmem ξ hξ).1), (hdem ξ).2.1⟩, ξ, hξ, rfl⟩
  have hsplit : ∀ x y : V, (⟨x, y⟩ₖ : V) ∈ jonssonFunction lam G D e d₀ θ →
      ∃ ξ ∈ θ, x = G ‘ ξ ∧ y = kpair.π₂ (demandAt D e d₀ ξ) := by
    intro x y hxy
    obtain ⟨_, ξ, hξ, hq⟩ := (hmemF _).mp hxy
    exact ⟨ξ, hξ, (kpair_iff.mp hq).1, (kpair_iff.mp hq).2⟩
  have hFfun : IsFunction (jonssonFunction lam G D e d₀ θ) := by
    refine IsFunction.of_mem (X := domain (jonssonFunction lam G D e d₀ θ)) (Y := lam) (mem_function.intro ?_ ?_)
    · intro p hp
      obtain ⟨_, ξ, hξ, hq⟩ := (hmemF p).mp hp
      rw [hq] at hp ⊢
      exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hp, (hdem ξ).2.1⟩
    · intro x hx
      obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
      refine ⟨y, hy, ?_⟩
      intro y' hy'
      obtain ⟨ξ, hξ, hxξ, hyξ⟩ := hsplit x y hy
      obtain ⟨η, hη, hxη, hyη⟩ := hsplit x y' hy'
      have : ξ = η := hGinj ξ hξ η hη (hxξ ▸ hxη ▸ rfl)
      rw [hyη, hyξ, this]
  refine ⟨hFfun, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
    obtain ⟨ξ, hξ, hxξ, hyξ⟩ := hsplit x y hy
    refine ⟨hxξ ▸ countableSubsets_subset (hGmem ξ hξ).1, ?_⟩
    rw [value_eq_of_kpair_mem hy, hyξ]
    exact (hdem ξ).2.1
  · intro A hA hlamA γ hγ
    have hqD : (⟨A, γ⟩ₖ : V) ∈ D := by
      rw [hDdef]; exact kpair_mem_jonssonDemands_iff.mpr ⟨hA, hγ, hlamA⟩
    have hξθ : w ‘ (⟨A, γ⟩ₖ : V) ∈ θ := function_value_mem hw hqD
    have hev : e ‘ (w ‘ (⟨A, γ⟩ₖ : V)) = ⟨A, γ⟩ₖ := by
      rw [hedef]; exact converseGraph_value_value hw hwinj hqD
    have hdξ : demandAt D e d₀ (w ‘ (⟨A, γ⟩ₖ : V)) = ⟨A, γ⟩ₖ := by
      rw [demandAt_eq_of_mem (d₀ := d₀) (by rw [hev]; exact hqD), hev]
    refine ⟨G ‘ (w ‘ (⟨A, γ⟩ₖ : V)), mem_domain_of_kpair_mem (hpairF _ hξθ), ?_, ?_, ?_⟩
    · have h := (hGmem _ hξθ).2
      rwa [hdξ, kpair.π₁_kpair] at h
    · exact exists_enumeration_of_mem_countableSubsets (hGmem _ hξθ).1
    · rw [value_eq_of_kpair_mem (hpairF _ hξθ), hdξ, kpair.π₂_kpair]

end ZFVP
