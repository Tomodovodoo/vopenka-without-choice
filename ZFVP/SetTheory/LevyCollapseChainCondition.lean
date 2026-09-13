import ZFVP.SetTheory.LevyCollapseSupport
import ZFVP.SetTheory.UltrafilterOrdinals
import ZFVP.SetTheory.NaturalPigeonhole
import ZFVP.SetTheory.LeastOrdinalChoice

/-! The `κ`-chain condition for the Levy collapse `Coll(ω, <κ)` at a measurable ordinal `κ`,
proved with a nonprincipal `κ`-complete ultrafilter `U` instead of the Δ-system lemma: among
`κ` many conditions, the parts of the supports below each `λ < κ` are constant on a `U`-large
set, these constant parts stabilise at some `λ₀`, the cuts below `λ₀` are constant on a
`U`-large set, and two conditions from that set with disjoint parts above `λ₀` are compatible. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The indices whose support below `lam` is exactly `s`. -/
noncomputable def fiberSupport (f κ lam s : V) : V :=
  {α ∈ κ ; ordinalSupport (f ‘ α) ∩ lam = s}

instance fiberSupport_definable (f κ : V) : ℒₛₑₜ-function₂[V] (fiberSupport f κ) := by
  have hd : ℒₛₑₜ-relation₃[V] (fun Y lam s ↦ ∀ α, α ∈ Y ↔ α ∈ κ ∧
    ordinalSupport (f ‘ α) ∩ lam = s) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = fiberSupport f κ (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  exact ⟨fun h p ↦ (h p).trans (show p ∈ fiberSupport f κ (v 1) (v 2) ↔
      p ∈ κ ∧ ordinalSupport (f ‘ p) ∩ v 1 = v 2 from mem_sep_iff),
    fun h p ↦ (h p).trans (show p ∈ fiberSupport f κ (v 1) (v 2) ↔
      p ∈ κ ∧ ordinalSupport (f ‘ p) ∩ v 1 = v 2 from mem_sep_iff).symm⟩

/-- The `U`-majority support below `lam`. -/
noncomputable def majoritySupport (f κ U lam : V) : V :=
  ⋃ˢ {s ∈ ℘ lam ; fiberSupport f κ lam s ∈ U}

instance majoritySupport_definable (f κ U : V) : ℒₛₑₜ-function₁[V] (majoritySupport f κ U) := by
  have hd : ℒₛₑₜ-relation[V] (fun M lam ↦ ∀ x, x ∈ M ↔
    ∃ s, s ∈ ℘ lam ∧ fiberSupport f κ lam s ∈ U ∧ x ∈ s) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = majoritySupport f κ U (v 1) ↔ _
  rw [mem_ext_iff]
  constructor
  · intro h x
    rw [h x]
    unfold majoritySupport
    rw [mem_sUnion_iff]
    constructor
    · rintro ⟨s, hs, hx⟩
      obtain ⟨hs1, hs2⟩ := mem_sep_iff.mp hs
      exact ⟨s, hs1, hs2, hx⟩
    · rintro ⟨s, hs1, hs2, hx⟩
      exact ⟨s, mem_sep_iff.mpr ⟨hs1, hs2⟩, hx⟩
  · intro h x
    rw [h x]
    unfold majoritySupport
    rw [mem_sUnion_iff]
    constructor
    · rintro ⟨s, hs1, hs2, hx⟩
      exact ⟨s, mem_sep_iff.mpr ⟨hs1, hs2⟩, hx⟩
    · rintro ⟨s, hs, hx⟩
      obtain ⟨hs1, hs2⟩ := mem_sep_iff.mp hs
      exact ⟨s, hs1, hs2, hx⟩

section

variable {κ U f : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hf : f ∈ (levyCollapse κ) ^ κ)

include hAC hU hc hf

omit hf in
theorem majoritySupport_spec {lam : V} (hlam : lam ∈ κ) :
    fiberSupport f κ lam (majoritySupport f κ U lam) ∈ U ∧ majoritySupport f κ U lam ⊆ lam := by
  have hF : ℒₛₑₜ-function₁ (fun α : V ↦ ordinalSupport (f ‘ α) ∩ lam) := by definability
  let g := definableGraph κ _ hF
  have hg : g ∈ ℘ lam ^ κ := by
    apply mem_function_of_mem_function_of_subset (definableGraph_mem_function κ _ hF)
    intro y hy
    obtain ⟨α, _, rfl⟩ := (repl_spec hF).mp hy
    exact mem_power_iff.mpr (fun z hz ↦ (mem_inter_iff.mp hz).2)
  obtain ⟨μ, hμ, hμlam⟩ := measurable_power_bounded hAC hU hc hlam
  obtain ⟨s, hs, hfib⟩ := ultrafilter_fiber_mem hU hc hμ hμlam hg
  have hfib' : fiberSupport f κ lam s ∈ U := by
    have : {a ∈ κ ; g ‘ a = s} = fiberSupport f κ lam s := by
      ext a
      constructor
      · intro h
        obtain ⟨ha, hga⟩ := mem_sep_iff.mp h
        rw [value_definableGraph κ _ hF ha] at hga
        exact mem_sep_iff.mpr ⟨ha, hga⟩
      · intro h
        obtain ⟨ha, hga⟩ := mem_sep_iff.mp h
        exact mem_sep_iff.mpr ⟨ha, by rw [value_definableGraph κ _ hF ha]; exact hga⟩
    rw [← this]
    exact hfib
  have hunique : ∀ s', s' ∈ ℘ lam → fiberSupport f κ lam s' ∈ U → s' = s := by
    intro s' _ hs'
    obtain ⟨a, ha⟩ := hU.1.nonempty_of_mem (hU.1.inter hs' hfib')
    rw [mem_inter_iff] at ha
    exact ((mem_sep_iff.mp ha.1).2).symm.trans (mem_sep_iff.mp ha.2).2
  have hset : {s' ∈ ℘ lam ; fiberSupport f κ lam s' ∈ U} = ({s} : V) := by
    ext s'
    rw [mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := mem_sep_iff.mp h
      exact hunique s' h1 h2
    · rintro rfl
      exact mem_sep_iff.mpr ⟨hs, hfib'⟩
  have hmaj : majoritySupport f κ U lam = s := by
    unfold majoritySupport
    rw [hset]
    ext x
    rw [mem_sUnion_iff]
    constructor
    · rintro ⟨t, ht, hx⟩
      rw [mem_singleton_iff] at ht
      exact ht ▸ hx
    · intro hx
      exact ⟨s, mem_singleton_iff.mpr rfl, hx⟩
  rw [hmaj]
  exact ⟨hfib', mem_power_iff.mp hs⟩

theorem majoritySupport_cut {lam lam' : V} (hlam : lam ∈ κ) (hlam' : lam' ∈ κ) (h : lam ⊆ lam') :
    majoritySupport f κ U lam = majoritySupport f κ U lam' ∩ lam := by
  obtain ⟨h1, _⟩ := majoritySupport_spec hAC hU hc hlam
  obtain ⟨h2, _⟩ := majoritySupport_spec hAC hU hc hlam'
  obtain ⟨a, ha⟩ := hU.1.nonempty_of_mem (hU.1.inter h1 h2)
  rw [mem_inter_iff] at ha
  have e1 := (mem_sep_iff.mp ha.1).2
  have e2 := (mem_sep_iff.mp ha.2).2
  rw [← e1, ← e2]
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨hx, hxl⟩
    exact ⟨⟨hx, h _ hxl⟩, hxl⟩
  · rintro ⟨⟨hx, _⟩, hxl⟩
    exact ⟨hx, hxl⟩

theorem majoritySupport_bounded (hω : (ω : V) ∈ κ) :
    ∃ k ∈ (ω : V), ∀ lam ∈ κ, ¬succ k ≤# majoritySupport f κ U lam := by
  by_contra hno
  push Not at hno
  have hR : ℒₛₑₜ-relation[V] (fun k lam ↦ lam ∈ κ ∧ succ k ≤# majoritySupport f κ U lam) := by
    definability
  let lamOf := leastOrdinalOrZero _ hR
  have hlam : ∀ k ∈ (ω : V), lamOf k ∈ κ ∧ succ k ≤# majoritySupport f κ U (lamOf k) := by
    intro k hk
    obtain ⟨lam, hlam, hle⟩ := hno k hk
    have : IsOrdinal lam := IsOrdinal.of_mem hlam
    exact (leastOrdinalOrZero_spec _ hR k ⟨lam, inferInstance, hlam, hle⟩).2.1
  have hF : ℒₛₑₜ-function₁ (fun k ↦ fiberSupport f κ (lamOf k) (majoritySupport f κ U (lamOf k))) := by
    definability
  let Y := definableGraph ω _ hF
  have hY : Y ∈ U ^ (ω : V) := by
    apply mem_function_of_mem_function_of_subset (definableGraph_mem_function ω _ hF)
    intro y hy
    obtain ⟨k, hk, rfl⟩ := (repl_spec hF).mp hy
    exact (majoritySupport_spec hAC hU hc (hlam k hk).1).1
  have hZ := hc ω hω Y hY
  obtain ⟨α, hα⟩ := hU.1.nonempty_of_mem hZ
  rw [mem_indexedIntersection_iff] at hα
  have hfin := ordinalSupport_finite (function_value_mem hf hα.1)
  obtain ⟨n, hn, hnot⟩ := internallyFinite_not_all_cardLE hfin
  apply hnot
  have hαn := hα.2 n hn
  rw [value_definableGraph ω _ hF hn] at hαn
  have heq := (mem_sep_iff.mp hαn).2
  refine (hlam n hn).2.trans ?_
  rw [← heq]
  exact cardLE_of_subset (fun z hz ↦ (mem_inter_iff.mp hz).1)

theorem majoritySupport_stable (hω : (ω : V) ∈ κ) :
    ∃ lam₀ ∈ κ, ∀ lam ∈ κ, lam₀ ⊆ lam → majoritySupport f κ U lam = majoritySupport f κ U lam₀ := by
  obtain ⟨k, hk, hbound⟩ := majoritySupport_bounded hAC hU hc hf hω
  have hR : ℒₛₑₜ-relation[V] (fun (_ : V) k ↦ k ∈ (ω : V) ∧
    ∀ lam ∈ κ, ¬succ k ≤# majoritySupport f κ U lam) := by definability
  have hleast := leastOrdinalOrZero_spec _ hR ∅ ⟨k, IsOrdinal.of_mem hk, hk, hbound⟩
  set k₀ := leastOrdinalOrZero _ hR ∅ with hk₀
  obtain ⟨hk₀ord, ⟨hk₀ω, hk₀bound⟩, hk₀min⟩ := hleast
  -- a level where `k₀` fits into the majority support
  have hexists : ∃ lam₀ ∈ κ, k₀ ≤# majoritySupport f κ U lam₀ := by
    rcases internalNatural_cases hk₀ω with h0 | ⟨k₁, hk₁, hsucc⟩
    · obtain ⟨z, hz⟩ := hU.1.nonempty_of_mem hU.1.2.1
      have : IsNonempty κ := ⟨⟨z, hz⟩⟩
      refine ⟨∅, IsOrdinal.empty_mem_iff_nonempty.mpr this, ?_⟩
      rw [h0]
      exact cardLE_empty _
    · by_contra hno
      push Not at hno
      have hk₁lt : k₁ ∈ k₀ := by rw [hsucc]; exact mem_succ_self _
      have : IsOrdinal k₁ := IsOrdinal.of_mem hk₁
      have hk₁prop : k₁ ∈ (ω : V) ∧ ∀ lam ∈ κ, ¬succ k₁ ≤# majoritySupport f κ U lam :=
        ⟨hk₁, fun lam hlam h ↦ hno lam hlam (hsucc ▸ h)⟩
      exact mem_irrefl k₁ (hk₀min k₁ inferInstance hk₁prop _ hk₁lt)
  obtain ⟨lam₀, hlam₀, hle⟩ := hexists
  refine ⟨lam₀, hlam₀, fun lam hlam hsub ↦ ?_⟩
  have hcut := majoritySupport_cut hAC hU hc hf hlam₀ hlam hsub
  have hsub' : majoritySupport f κ U lam₀ ⊆ majoritySupport f κ U lam := by
    rw [hcut]
    exact fun z hz ↦ (mem_inter_iff.mp hz).1
  by_contra hne
  have hproper : ∃ x ∈ majoritySupport f κ U lam, x ∉ majoritySupport f κ U lam₀ := by
    by_contra h
    push Not at h
    exact hne (SetTheory.subset_antisymm h hsub')
  obtain ⟨x, hx, hxn⟩ := hproper
  apply hk₀bound lam hlam
  have h1 : insert k₀ k₀ ≤# insert x (majoritySupport f κ U lam₀) :=
    cardLE_insert_fresh hle (mem_irrefl k₀) hxn
  refine h1.trans (cardLE_of_subset ?_)
  intro z hz
  rcases mem_insert.mp hz with rfl | hz
  · exact hx
  · exact hsub' _ hz

set_option maxHeartbeats 1000000 in
/-- Two of `κ` many Levy collapse conditions are compatible. -/
theorem levyCollapse_chainCondition (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
    (hinj : Injective f) :
    ∃ α ∈ κ, ∃ β ∈ κ, α ≠ β ∧
      ForcingCompatible (levyCollapse κ) (levyOrder κ) (f ‘ α) (f ‘ β) := by
  let := IsFunction.of_mem hf
  have hdf : domain f = κ := domain_eq_of_mem_function hf
  have hreg : IsRegularCardinal κ := measurable_regular hκ (IsOrdinal.toIsTransitive.transitive _ hω) hU hc
  obtain ⟨lam₀, hlam₀, hstable⟩ := majoritySupport_stable hAC hU hc hf hω
  have : IsOrdinal lam₀ := IsOrdinal.of_mem hlam₀
  obtain ⟨s, hs⟩ : ∃ s, s = majoritySupport f κ U lam₀ := ⟨_, rfl⟩
  obtain ⟨hY₁, hslam⟩ := majoritySupport_spec hAC hU hc hlam₀
  rw [← hs] at hY₁ hslam
  -- the cuts below `lam₀` are constant on a `U`-large set
  have hF := levyCut_value_definable lam₀ f
  let g := definableGraph κ _ hF
  have hBsmall : ∃ μ ∈ κ, ℘ (((ω : V) ×ˢ lam₀) ×ˢ lam₀) ≤# μ := by
    obtain ⟨γ₁, hγ₁, h1⟩ := regularCardinal_ordinal_prod_small hreg hlam₀ hω
    have : IsOrdinal γ₁ := IsOrdinal.of_mem hγ₁
    obtain ⟨γ₂, hγ₂, h2⟩ := regularCardinal_ordinal_prod_small hreg hlam₀ hγ₁
    obtain ⟨μ, hμ, h3⟩ := measurable_power_bounded hAC hU hc hγ₂
    refine ⟨μ, hμ, (power_cardLE_of_cardLE ?_).trans h3⟩
    exact (prod_cardLE_prod h1 (CardLE.refl _)).trans h2
  obtain ⟨μ, hμ, hBμ⟩ := hBsmall
  have hg : g ∈ ℘ (((ω : V) ×ˢ lam₀) ×ˢ lam₀) ^ κ := by
    apply mem_function_of_mem_function_of_subset (definableGraph_mem_function κ _ hF)
    intro y hy
    obtain ⟨α, hα, rfl⟩ := (repl_spec hF).mp hy
    have hcut := levyCut_mem (β := lam₀) (function_value_mem hf hα)
    exact mem_power_iff.mpr
      ((mem_finitePartialFunctions _ _ _).mp (levyCollapse_finitePartialFunction hcut)).1
  obtain ⟨q, _, hY₂⟩ := ultrafilter_fiber_mem hU hc hμ hBμ hg
  have hcutq : ∀ α ∈ {a ∈ κ ; g ‘ a = q}, levyCut lam₀ (f ‘ α) = q := by
    intro α hα
    obtain ⟨hα, hq⟩ := mem_sep_iff.mp hα
    rw [value_definableGraph κ _ hF hα] at hq
    exact hq
  have hY := hU.1.inter hY₁ hY₂
  obtain ⟨α, hα⟩ := hU.1.nonempty_of_mem hY
  have hακ : α ∈ κ := (mem_sep_iff.mp (mem_inter_iff.mp hα).1).1
  have hpα := function_value_mem hf hακ
  have hqα : levyCut lam₀ (f ‘ α) = q := hcutq α (mem_inter_iff.mp hα).2
  have hsupα : ordinalSupport (f ‘ α) ∩ lam₀ = s := (mem_sep_iff.mp (mem_inter_iff.mp hα).1).2
  have hqfun : IsFunction q := by
    rw [← hqα]
    exact ((mem_finitePartialFunctions _ _ _).mp
      (levyCollapse_finitePartialFunction (levyCut_mem (β := lam₀) hpα))).2.1
  by_cases hbelow : ordinalSupport (f ‘ α) ⊆ lam₀
  · have hcompl : relativeComplement κ ({α} : V) ∈ U := by
      rcases hU.1.dichotomy (show ({α} : V) ⊆ κ from fun z hz ↦ by
        rw [mem_singleton_iff] at hz; exact hz ▸ hακ) with h | h
      · exact (hU.2 α hακ h).elim
      · exact h
    obtain ⟨β, hβ⟩ := hU.1.nonempty_of_mem (hU.1.inter hY hcompl)
    rw [mem_inter_iff, mem_relativeComplement_iff, mem_singleton_iff] at hβ
    have hβκ : β ∈ κ := hβ.2.1
    have hqβ : levyCut lam₀ (f ‘ β) = q := hcutq β (mem_inter_iff.mp hβ.1).2
    refine ⟨α, hακ, β, hβκ, fun h ↦ hβ.2.2 h.symm, ?_⟩
    exact levyCollapse_compatible_of_cut hpα (function_value_mem hf hβκ)
      (levyCut_eq_of_support hpα hbelow) (hqβ.trans hqα.symm)
  · obtain ⟨γ, hγ, hγn⟩ : ∃ γ ∈ ordinalSupport (f ‘ α), γ ∉ lam₀ := by
      by_contra h
      push Not at h
      exact hbelow (fun z hz ↦ h z hz)
    obtain ⟨δ, hδ, hOδ⟩ := hU.finite_bounded hc (ordinalSupport_finite hpα) (ordinalSupport_subset hpα)
    have : IsOrdinal δ := IsOrdinal.of_mem hδ
    obtain ⟨δ', hδ', hδδ', hlamδ'⟩ : ∃ δ' ∈ κ, δ ⊆ δ' ∧ lam₀ ⊆ δ' := by
      rcases IsOrdinal.subset_or_supset (α := δ) (β := lam₀) with h | h
      · exact ⟨lam₀, hlam₀, h, subset_refl _⟩
      · exact ⟨δ, hδ, subset_refl _, h⟩
    have hsδ' : majoritySupport f κ U δ' = s := (hstable δ' hδ' hlamδ').trans hs.symm
    have hY₃ : fiberSupport f κ δ' s ∈ U := by
      have := (majoritySupport_spec (f := f) hAC hU hc hδ').1
      rwa [hsδ'] at this
    obtain ⟨β, hβ⟩ := hU.1.nonempty_of_mem (hU.1.inter hY hY₃)
    rw [mem_inter_iff] at hβ
    have hβκ : β ∈ κ := (mem_sep_iff.mp hβ.2).1
    have hsupβ : ordinalSupport (f ‘ β) ∩ δ' = s := (mem_sep_iff.mp hβ.2).2
    have hpβ := function_value_mem hf hβκ
    have hqβ : levyCut lam₀ (f ‘ β) = q := hcutq β (mem_inter_iff.mp hβ.1).2
    have hOδ' : ordinalSupport (f ‘ α) ⊆ δ' := subset_trans hOδ hδδ'
    have hne : α ≠ β := by
      intro h
      rw [← h] at hsupβ
      have hγδ' : γ ∈ ordinalSupport (f ‘ α) ∩ δ' := mem_inter_iff.mpr ⟨hγ, hOδ' _ hγ⟩
      rw [hsupβ] at hγδ'
      exact hγn (hslam _ hγδ')
    refine ⟨α, hακ, β, hβκ, hne, ?_⟩
    exact levyCollapse_compatible_of_split hpα hpβ (hqα.trans hqβ.symm) hOδ'
      (by rw [hsupβ]; exact hslam)

end

end ZFVP
