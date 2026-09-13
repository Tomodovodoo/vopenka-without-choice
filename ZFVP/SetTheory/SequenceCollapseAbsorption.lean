import ZFVP.SetTheory.TreeEmbedding
import ZFVP.SetTheory.ProductForcing
import ZFVP.SetTheory.FiniteSequencesCardinality

/-! Absorption: for a poset `P` of size at most an infinite initial `λ`, the product
`P × λ^{<ω}` receives a dense embedding of `λ^{<ω}` (so it is forcing-equivalent to `λ^{<ω}`,
the dense tree inside `Coll(ω, λ)`). The product is `λ`-splitting and the levels of the
sequence tree, paired with the top of `P`, form a collapsing system. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A sequence extends to any longer length (filling with `∅`). -/
theorem sequence_extend {lam t m n : V} (h0 : (∅ : V) ∈ lam) (ht : t ∈ lam ^ m) (hmn : m ⊆ n) :
    ∃ s ∈ lam ^ n, t ⊆ s := by
  have : IsFunction t := IsFunction.of_mem ht
  have hd := domain_eq_of_mem_function ht
  let F : V → V := fun i ↦ t ‘ i
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  refine ⟨definableGraph n F hF, definableGraph_mem_function_of_mapsTo n lam F hF ?_, ?_⟩
  · intro i hi
    by_cases him : i ∈ m
    · exact function_value_mem ht him
    · have : F i = ∅ := value_eq_empty_of_not_mem_domain (by rw [hd]; exact him)
      rw [this]
      exact h0
  · intro p hp
    obtain ⟨i, hi, y, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function ht p hp)
    exact (pair_mem_definableGraph_iff _ _ _ _ _).mpr ⟨hmn i hi, (value_eq_of_kpair_mem hp).symm⟩

/-- Distinct sequences of the same length are incompatible. -/
theorem sequence_incompatible_of_ne {lam s t n : V} (hn : n ∈ (ω : V)) (hs : s ∈ lam ^ n)
    (ht : t ∈ lam ^ n) (hne : s ≠ t) :
    ¬ForcingCompatible (finiteSequences lam) (sequenceOrder lam) s t := by
  intro hc
  have hsF : s ∈ finiteSequences lam := (mem_finiteSequences_iff _ _).mpr ⟨n, hn, hs⟩
  have htF : t ∈ finiteSequences lam := (mem_finiteSequences_iff _ _).mpr ⟨n, hn, ht⟩
  have : IsFunction s := IsFunction.of_mem hs
  have : IsFunction t := IsFunction.of_mem ht
  rcases (sequence_compatible_iff hsF htF).mp hc with h | h
  · apply hne
    rw [sequence_eq_restrict_of_subset ht hs h]
    exact IsFunction.restrict_eq_self t n (by rw [domain_eq_of_mem_function ht])
  · apply hne
    rw [sequence_eq_restrict_of_subset hs ht h]
    exact (IsFunction.restrict_eq_self s n (by rw [domain_eq_of_mem_function hs])).symm

/-- Each level of the sequence tree is a maximal antichain. -/
theorem sequence_level_maximal {lam n : V} (h0 : (∅ : V) ∈ lam) (hn : n ∈ (ω : V)) :
    IsMaximalAntichainIn (finiteSequences lam) (sequenceOrder lam) (finiteSequences lam) (lam ^ n) := by
  have hsub : lam ^ n ⊆ finiteSequences lam := fun s hs ↦ (mem_finiteSequences_iff _ _).mpr ⟨n, hn, hs⟩
  refine ⟨⟨hsub, fun s hs t ht hne ↦ sequence_incompatible_of_ne hn hs ht hne⟩, hsub, ?_⟩
  intro t ht
  obtain ⟨m, hm, htm⟩ := (mem_finiteSequences_iff _ _).mp ht
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have : IsOrdinal m := IsOrdinal.of_mem hm
  rcases IsOrdinal.subset_or_supset (α := n) (β := m) with h | h
  · refine ⟨t ↾ n, function_restrict_mem htm h, ?_⟩
    exact (sequence_compatible_iff (hsub _ (function_restrict_mem htm h)) ht).mpr
      (Or.inl (restrict_subset t n))
  · obtain ⟨s, hs, hts⟩ := sequence_extend h0 htm h
    exact ⟨s, hs, (sequence_compatible_iff (hsub s hs) ht).mpr (Or.inr hts)⟩

theorem sequence_top (lam : V) : IsForcingTop (finiteSequences lam) (sequenceOrder lam) ∅ :=
  ⟨empty_mem_finiteSequences lam, fun s hs ↦ (pair_mem_sequenceOrder_iff _ _ _).mpr
    ⟨hs, empty_mem_finiteSequences lam, fun z hz ↦ (not_mem_empty hz).elim⟩⟩

/-- A nonempty set injecting into `lam` is the range of a function on `lam`. -/
theorem exists_surjection_of_cardLE {X lam x₀ : V} (hX : X ≤# lam) (hx₀ : x₀ ∈ X) :
    ∃ E ∈ X ^ lam, range E = X := by
  obtain ⟨i, hi, hinj⟩ := hX
  have : IsFunction i := IsFunction.of_mem hi
  let E : V := sep (lam ×ˢ X)
    (fun z ↦ ⟨kpair.π₂ z, kpair.π₁ z⟩ₖ ∈ i ∨ (kpair.π₁ z ∉ range i ∧ kpair.π₂ z = x₀)) (by definability)
  have hmem : ∀ α x, ⟨α, x⟩ₖ ∈ E ↔ α ∈ lam ∧ x ∈ X ∧ (⟨x, α⟩ₖ ∈ i ∨ (α ∉ range i ∧ x = x₀)) := by
    intro α x
    simp only [E, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]
  refine ⟨E, ?_, ?_⟩
  · apply mem_function.intro
    · intro p hp
      exact (mem_sep_iff.mp hp).1
    · intro α hα
      by_cases hr : α ∈ range i
      · obtain ⟨x, hx⟩ := mem_range_iff.mp hr
        have hxX : x ∈ X := domain_eq_of_mem_function hi ▸ mem_domain_of_kpair_mem hx
        refine ⟨x, (hmem α x).mpr ⟨hα, hxX, Or.inl hx⟩, ?_⟩
        intro y hy
        rcases ((hmem α y).mp hy).2.2 with h | ⟨h, _⟩
        · exact hinj y x α h hx
        · exact (h hr).elim
      · refine ⟨x₀, (hmem α x₀).mpr ⟨hα, hx₀, Or.inr ⟨hr, rfl⟩⟩, ?_⟩
        intro y hy
        rcases ((hmem α y).mp hy).2.2 with h | ⟨_, h⟩
        · exact (hr (mem_range_of_kpair_mem h)).elim
        · exact h
  · apply mem_ext
    intro x
    rw [mem_range_iff]
    constructor
    · rintro ⟨α, hα⟩
      exact ((hmem α x).mp hα).2.1
    · intro hx
      have hxd : x ∈ domain i := by rw [domain_eq_of_mem_function hi]; exact hx
      exact ⟨i ‘ x, (hmem _ x).mpr ⟨function_value_mem hi hx, hx, Or.inl (kpair_value_mem hxd)⟩⟩

/-- The product of `P` with the sequence tree `λ^{<ω}`. -/
noncomputable def sequenceProduct (P lam : V) : V := P ×ˢ finiteSequences lam

noncomputable def sequenceProductOrder (P R lam : V) : V :=
  productOrder P R (finiteSequences lam) (sequenceOrder lam)

section

variable {P R one lam : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)

include hR in
theorem sequenceProduct_splitting : IsSplitting (sequenceProduct P lam) (sequenceProductOrder P R lam) lam := by
  intro z hz
  obtain ⟨p, hp, t, ht, rfl⟩ := mem_prod_iff.mp hz
  obtain ⟨m, hm, htm⟩ := (mem_finiteSequences_iff _ _).mp ht
  let F : V → V := fun α ↦ ⟨p, insert ⟨m, α⟩ₖ t⟩ₖ
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  have hchild : ∀ α ∈ lam, insert ⟨m, α⟩ₖ t ∈ lam ^ succ m := fun α hα ↦ function_append_mem htm hα
  have hchildF : ∀ α ∈ lam, insert ⟨m, α⟩ₖ t ∈ finiteSequences lam :=
    fun α hα ↦ (mem_finiteSequences_iff _ _).mpr ⟨succ m, ω_succ_closed hm, hchild α hα⟩
  have hval : ∀ α ∈ lam, ∀ β ∈ lam, insert ⟨m, α⟩ₖ t = insert ⟨m, β⟩ₖ t → α = β := by
    intro α hα β hβ heq
    have := congrArg (fun s ↦ s ‘ m) heq
    simpa only [value_insert_kpair htm hα, value_insert_kpair htm hβ] using this
  refine ⟨repl F hF lam, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨α, hα, rfl⟩ := (repl_spec hF).mp hx
    exact kpair_mem_iff.mpr ⟨hp, hchildF α hα⟩
  · intro x hx y hy hne hc
    obtain ⟨α, hα, rfl⟩ := (repl_spec hF).mp hx
    obtain ⟨β, hβ, rfl⟩ := (repl_spec hF).mp hy
    have hαβ : α ≠ β := fun h ↦ hne (h ▸ rfl)
    have := (product_compatible_iff hp (hchildF α hα) hp (hchildF β hβ)).mp hc
    exact sequence_incompatible_of_ne (ω_succ_closed hm) (hchild α hα) (hchild β hβ)
      (fun heq ↦ hαβ (hval α hα β hβ heq)) this.2
  · intro x hx
    obtain ⟨α, hα, rfl⟩ := (repl_spec hF).mp hx
    exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr ⟨hp, hchildF α hα, hp, ht, hR.2.1 p hp,
      (pair_mem_sequenceOrder_iff _ _ _).mpr ⟨hchildF α hα, ht, fun q hq ↦ mem_insert.mpr (Or.inr hq)⟩⟩
  · refine ⟨definableGraph lam F hF, definableGraph_mem_function_of_mapsTo _ _ F hF
      (fun α hα ↦ (repl_spec hF).mpr ⟨α, hα, rfl⟩), ?_⟩
    intro α β z hα hβ
    obtain ⟨hαl, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hα
    obtain ⟨hβl, hz⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hβ
    exact hval α hαl β hβl (kpair_iff.mp hz).2

/-- The `n`-th level of the tree, paired with the top of `P`. -/
noncomputable def levelAntichains (one lam : V) : V :=
  definableGraph (ω : V) (fun n ↦ ({one} : V) ×ˢ lam ^ succ n) (by definability)

/-- The label of `⟨n, ⟨p, s⟩⟩` is `s n`. -/
noncomputable def levelLabels (P lam : V) : V :=
  definableGraph ((ω : V) ×ˢ (P ×ˢ finiteSequences lam))
    (fun z ↦ (kpair.π₂ (kpair.π₂ z)) ‘ (kpair.π₁ z)) (by definability)

include hR htop in
theorem sequenceProduct_collapsingSystem (h0 : (∅ : V) ∈ lam) :
    IsCollapsingSystem (sequenceProduct P lam) (sequenceProductOrder P R lam) lam
      (levelAntichains one lam) (levelLabels P lam) := by
  have hA : ∀ n ∈ (ω : V), (levelAntichains one lam) ‘ n = ({one} : V) ×ˢ lam ^ succ n :=
    fun n hn ↦ value_definableGraph _ _ _ hn
  have hL : ∀ n ∈ (ω : V), ∀ q ∈ P ×ˢ finiteSequences lam,
      (levelLabels P lam) ‘ ⟨n, q⟩ₖ = (kpair.π₂ q) ‘ n := by
    intro n hn q hq
    unfold levelLabels
    rw [value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hn, hq⟩)]
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  have hFS : ∀ n ∈ (ω : V), lam ^ succ n ⊆ finiteSequences lam :=
    fun n hn s hs ↦ (mem_finiteSequences_iff _ _).mpr ⟨succ n, ω_succ_closed hn, hs⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [hA n hn]
    have hlev := sequence_level_maximal h0 (ω_succ_closed hn)
    have hsub : ({one} : V) ×ˢ lam ^ succ n ⊆ sequenceProduct P lam := by
      intro x hx
      obtain ⟨o, ho, s, hs, rfl⟩ := mem_prod_iff.mp hx
      rw [mem_singleton_iff] at ho
      subst ho
      exact kpair_mem_iff.mpr ⟨htop.1, hFS n hn s hs⟩
    refine ⟨⟨hsub, ?_⟩, hsub, ?_⟩
    · intro x hx y hy hne hc
      obtain ⟨o, ho, s, hs, rfl⟩ := mem_prod_iff.mp hx
      obtain ⟨o', ho', s', hs', rfl⟩ := mem_prod_iff.mp hy
      rw [mem_singleton_iff] at ho ho'
      subst ho
      subst ho'
      have hne' : s ≠ s' := fun h ↦ hne (h ▸ rfl)
      exact hlev.1.2 s hs s' hs' hne'
        ((product_compatible_iff htop.1 (hFS n hn s hs) htop.1 (hFS n hn s' hs')).mp hc).2
    · intro d hd
      obtain ⟨p, hp, t, ht, rfl⟩ := mem_prod_iff.mp hd
      obtain ⟨s, hs, hst⟩ := hlev.2.2 t ht
      refine ⟨⟨one, s⟩ₖ, kpair_mem_iff.mpr ⟨mem_singleton_iff.mpr rfl, hs⟩, ?_⟩
      exact (product_compatible_iff htop.1 (hFS n hn s hs) hp ht).mpr
        ⟨⟨p, hp, htop.2 p hp, hR.2.1 p hp⟩, hst⟩
  · intro n hn a ha
    rw [hA n hn] at ha
    obtain ⟨o, ho, s, hs, rfl⟩ := mem_prod_iff.mp ha
    rw [mem_singleton_iff] at ho
    subst ho
    rw [hL n hn _ (kpair_mem_iff.mpr ⟨htop.1, hFS n hn s hs⟩)]
    simp only [kpair.π₂_kpair]
    exact function_value_mem hs (mem_succ_self n)
  · intro α hα q hq
    obtain ⟨p, hp, t, ht, rfl⟩ := mem_prod_iff.mp hq
    obtain ⟨m, hm, htm⟩ := (mem_finiteSequences_iff _ _).mp ht
    have hs : insert ⟨m, α⟩ₖ t ∈ lam ^ succ m := function_append_mem htm hα
    have hsF : insert ⟨m, α⟩ₖ t ∈ finiteSequences lam := hFS m hm _ hs
    refine ⟨m, hm, ⟨one, insert ⟨m, α⟩ₖ t⟩ₖ, ?_, ?_, ?_⟩
    · rw [hA m hm]
      exact kpair_mem_iff.mpr ⟨mem_singleton_iff.mpr rfl, hs⟩
    · rw [hL m hm _ (kpair_mem_iff.mpr ⟨htop.1, hsF⟩)]
      simp only [kpair.π₂_kpair]
      exact value_insert_kpair htm hα
    · exact (product_compatible_iff htop.1 hsF hp ht).mpr ⟨⟨p, hp, htop.2 p hp, hR.2.1 p hp⟩,
        (sequence_compatible_iff hsF ht).mpr (Or.inr (fun q hq ↦ mem_insert.mpr (Or.inr hq)))⟩

include hR htop in
/-- Absorption: `λ^{<ω}` embeds densely into `P × λ^{<ω}` whenever `|P| ≤ λ`, `λ` infinite initial. -/
theorem exists_sequenceProduct_denseEmbedding (hAC : InternalChoice V) (hlam : IsInitialOrdinal lam)
    (hω : (ω : V) ⊆ lam) (hP : P ≤# lam) :
    ∃ e, IsDenseEmbedding (finiteSequences lam) (sequenceOrder lam) (sequenceProduct P lam)
      (sequenceProductOrder P R lam) e := by
  have : IsOrdinal lam := hlam.1
  have h0 : (∅ : V) ∈ lam := hω ∅ empty_mem_ω
  have hRP : IsForcingPreorder (sequenceProduct P lam) (sequenceProductOrder P R lam) :=
    productOrder_preorder hR (sequenceOrder_poset lam).1
  have htopP : IsForcingTop (sequenceProduct P lam) (sequenceProductOrder P R lam) ⟨one, ∅⟩ₖ :=
    product_top htop (sequence_top lam)
  have hsize : sequenceProduct P lam ≤# lam :=
    prod_cardLE_of_cardLE_initial hlam hω hP (finiteSequences_cardLE_initial hAC hlam hω)
  have hsplit := sequenceProduct_splitting (lam := lam) hR
  have hsys := sequenceProduct_collapsingSystem hR htop h0
  obtain ⟨E, hE, hEsurj⟩ := exists_surjection_of_cardLE hsize htopP.1
  obtain ⟨Φ, _, _, hΦ⟩ := exists_childChoice hAC hRP hsize hsplit hsys hE
  exact ⟨_, treeMap_denseEmbedding hRP htopP.1 htopP.2 hsys hE hΦ hEsurj⟩

end

end ZFVP
