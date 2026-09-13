import ZFVP.SetTheory.UltrafilterFibers
import ZFVP.SetTheory.CofinalityDictionary
import ZFVP.SetTheory.OrdinalProductBound
import ZFVP.SetTheory.FiniteSets

/-! Ordinal combinatorics of a nonprincipal complete ultrafilter on an ordinal `κ`: small
ordinals are not members, `κ` is closed under successor, finite subsets are bounded, `κ` is
regular, fibers in the ultrafilter are unique, and products respect size comparison. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsNonprincipalSetUltrafilter.small_not_mem {κ U lam : V} [IsOrdinal κ]
    (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U) (hlam : lam ∈ κ) :
    lam ∉ U := by
  intro hmem
  have hF : ℒₛₑₜ-function₁ (fun i : V ↦ relativeComplement κ ({i} : V)) := by definability
  let g := definableGraph lam _ hF
  have hg : g ∈ U ^ lam := by
    apply mem_function_of_mem_function_of_subset (definableGraph_mem_function lam _ hF)
    intro y hy
    obtain ⟨i, hi, rfl⟩ := (repl_spec hF).mp hy
    have hiκ : i ∈ κ := IsOrdinal.toIsTransitive.mem_trans hi hlam
    rcases hU.1.dichotomy (show ({i} : V) ⊆ κ from fun z hz ↦ by
      rw [mem_singleton_iff] at hz; exact hz ▸ hiκ) with h | h
    · exact (hU.2 i hiκ h).elim
    · exact h
  have hZ := hc lam hlam g hg
  obtain ⟨z, hz⟩ := hU.1.nonempty_of_mem (hU.1.inter hmem hZ)
  rw [mem_inter_iff, mem_indexedIntersection_iff] at hz
  have hzz := hz.2.2 z hz.1
  rw [value_definableGraph lam _ hF hz.1, mem_relativeComplement_iff] at hzz
  exact hzz.2 (mem_singleton_iff.mpr rfl)

theorem IsNonprincipalSetUltrafilter.succ_mem {κ U a : V} [IsOrdinal κ]
    (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U) (ha : a ∈ κ) :
    succ a ∈ κ := by
  have : IsOrdinal a := IsOrdinal.of_mem ha
  rcases IsOrdinal.mem_trichotomy (α := succ a) (β := κ) with h | h | h
  · exact h
  · exfalso
    have haU := hU.small_not_mem hc ha
    rcases hU.1.dichotomy (IsOrdinal.toIsTransitive.transitive a ha) with h1 | h1
    · exact haU h1
    · have hcomp : relativeComplement κ a = ({a} : V) := by
        ext z
        rw [mem_relativeComplement_iff, mem_singleton_iff, ← h]
        constructor
        · rintro ⟨hz, hza⟩
          rcases mem_succ_iff.mp hz with rfl | hz'
          · rfl
          · exact (hza hz').elim
        · intro hz
          rw [hz]
          exact ⟨mem_succ_self a, mem_irrefl a⟩
      rw [hcomp] at h1
      exact hU.2 a ha h1
  · exfalso
    rcases mem_succ_iff.mp h with h' | h'
    · exact mem_irrefl _ (h' ▸ ha)
    · exact mem_asymm ha h'

theorem IsNonprincipalSetUltrafilter.finite_bounded {κ U O : V} [IsOrdinal κ]
    (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
    (hO : IsInternallyFinite O) (hsub : O ⊆ κ) : ∃ δ ∈ κ, O ⊆ δ := by
  have key : ∀ O, IsInternallyFinite O → O ⊆ κ → ∃ δ ∈ κ, O ⊆ δ := by
    apply internallyFinite_induction (fun O ↦ O ⊆ κ → ∃ δ ∈ κ, O ⊆ δ) (by definability)
    · intro _
      obtain ⟨z, hz⟩ := hU.1.nonempty_of_mem hU.1.2.1
      have : IsNonempty κ := ⟨⟨z, hz⟩⟩
      exact ⟨∅, IsOrdinal.empty_mem_iff_nonempty.mpr this, empty_subset _⟩
    · intro A a ih hsub
      obtain ⟨δ, hδ, hAδ⟩ := ih (fun z hz ↦ hsub z (mem_insert.mpr (Or.inr hz)))
      have haκ : a ∈ κ := hsub a (mem_insert.mpr (Or.inl rfl))
      have hsa : succ a ∈ κ := hU.succ_mem hc haκ
      have : IsOrdinal a := IsOrdinal.of_mem haκ
      have : IsOrdinal δ := IsOrdinal.of_mem hδ
      rcases IsOrdinal.subset_or_supset (α := succ a) (β := δ) with h | h
      · refine ⟨δ, hδ, ?_⟩
        intro z hz
        rcases mem_insert.mp hz with rfl | hz
        · exact h _ (mem_succ_self _)
        · exact hAδ _ hz
      · refine ⟨succ a, hsa, ?_⟩
        intro z hz
        rcases mem_insert.mp hz with rfl | hz
        · exact mem_succ_self _
        · exact h _ (hAδ _ hz)
  exact key O hO hsub

/-- A measurable ordinal is regular. -/
theorem measurable_regular {κ U : V} (hκ : IsInitialOrdinal κ) (hω : (ω : V) ⊆ κ)
    (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U) :
    IsRegularCardinal κ := by
  have := hκ.1
  refine ⟨hκ, hω, ?_⟩
  rcases IsOrdinal.subset_iff.mp (internalCofinality_subset κ) with he | hlt
  · exact he
  · exfalso
    obtain ⟨f, hf⟩ := cofinalMap_exists κ
    have hβ : IsOrdinal (internalCofinality κ) := IsOrdinal.of_mem hlt
    have hF : ℒₛₑₜ-function₁ (fun i : V ↦ relativeComplement κ (succ (f ‘ i))) := by definability
    let g := definableGraph (internalCofinality κ) _ hF
    have hg : g ∈ U ^ internalCofinality κ := by
      apply mem_function_of_mem_function_of_subset (definableGraph_mem_function _ _ hF)
      intro y hy
      obtain ⟨i, hi, rfl⟩ := (repl_spec hF).mp hy
      have hfi : f ‘ i ∈ κ := function_value_mem hf.1 hi
      have hsi : succ (f ‘ i) ∈ κ := hU.succ_mem hc hfi
      rcases hU.1.dichotomy (IsOrdinal.toIsTransitive.transitive _ hsi) with h | h
      · exact (hU.small_not_mem hc hsi h).elim
      · exact h
    have hZ := hc _ hlt g hg
    obtain ⟨ξ, hξ⟩ := hU.1.nonempty_of_mem hZ
    rw [mem_indexedIntersection_iff] at hξ
    obtain ⟨i, hi, hξi⟩ := hf.2 ξ hξ.1
    have hmem := hξ.2 i hi
    rw [value_definableGraph _ _ hF hi, mem_relativeComplement_iff] at hmem
    have : IsOrdinal ξ := IsOrdinal.of_mem hξ.1
    have : IsOrdinal (f ‘ i) := IsOrdinal.of_mem (function_value_mem hf.1 hi)
    apply hmem.2
    rcases IsOrdinal.subset_iff.mp hξi with h | h
    · exact h ▸ mem_succ_self _
    · exact mem_succ_iff.mpr (Or.inr h)

theorem IsNonprincipalSetUltrafilter.fiber_unique {κ U g s s' : V}
    (hU : IsNonprincipalSetUltrafilter κ U) (hs : {a ∈ κ ; g ‘ a = s} ∈ U)
    (hs' : {a ∈ κ ; g ‘ a = s'} ∈ U) : s = s' := by
  obtain ⟨a, ha⟩ := hU.1.nonempty_of_mem (hU.1.inter hs hs')
  rw [mem_inter_iff] at ha
  exact ((mem_sep_iff.mp ha.1).2).symm.trans (mem_sep_iff.mp ha.2).2

/-- Products respect size comparison. -/
theorem prod_cardLE_prod {A A' B B' : V} (h1 : A ≤# A') (h2 : B ≤# B') :
    A ×ˢ B ≤# A' ×ˢ B' := by
  obtain ⟨e1, he1, hi1⟩ := h1
  obtain ⟨e2, he2, hi2⟩ := h2
  let := IsFunction.of_mem he1
  let := IsFunction.of_mem he2
  have hd1 := domain_eq_of_mem_function he1
  have hd2 := domain_eq_of_mem_function he2
  have hF : ℒₛₑₜ-function₁ (fun z : V ↦ ⟨e1 ‘ (kpair.π₁ z), e2 ‘ (kpair.π₂ z)⟩ₖ) := by definability
  refine ⟨definableGraph (A ×ˢ B) _ hF, ?_, ?_⟩
  · apply mem_function_of_mem_function_of_subset (definableGraph_mem_function _ _ hF)
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (repl_spec hF).mp hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact kpair_mem_iff.mpr ⟨function_value_mem he1 ha, function_value_mem he2 hb⟩
  · intro z₁ z₂ y h₁ h₂
    obtain ⟨hz₁, e₁⟩ := (pair_mem_definableGraph_iff _ _ hF z₁ y).mp h₁
    obtain ⟨hz₂, e₂⟩ := (pair_mem_definableGraph_iff _ _ hF z₂ y).mp h₂
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := mem_prod_iff.mp hz₁
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := mem_prod_iff.mp hz₂
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at e₁ e₂
    obtain ⟨ha, hb⟩ := kpair_iff.mp (e₁.symm.trans e₂)
    have p1 : ⟨a₁, e1 ‘ a₁⟩ₖ ∈ e1 := kpair_value_mem (by rw [hd1]; exact ha₁)
    have p2 : ⟨a₂, e1 ‘ a₂⟩ₖ ∈ e1 := kpair_value_mem (by rw [hd1]; exact ha₂)
    have q1 : ⟨b₁, e2 ‘ b₁⟩ₖ ∈ e2 := kpair_value_mem (by rw [hd2]; exact hb₁)
    have q2 : ⟨b₂, e2 ‘ b₂⟩ₖ ∈ e2 := kpair_value_mem (by rw [hd2]; exact hb₂)
    rw [ha] at p1
    rw [hb] at q1
    rw [hi1 a₁ a₂ _ p1 p2, hi2 b₁ b₂ _ q1 q2]

end ZFVP
