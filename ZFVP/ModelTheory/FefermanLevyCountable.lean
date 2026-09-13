import ZFVP.ModelTheory.FefermanLevyModel
import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.EndExtensionFinite
import ZFVP.SetTheory.EndExtensionWellOrdering

/-! Each stage set of reals is countable in the Feferman-Levy extension: it injects into
the check of the nice names of the stage, which is collapsed to omega by the next column
of the generic. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace FefermanLevyModel

variable {G : Set V} (hG : IsExternalForcingGeneric (flConditions V) (flOrder V) G)

/-- The stage-`n` part of the generic filter, as a set of the extension. -/
noncomputable def stageGeneric {n : V} (hn : n ∈ (ω : V)) : (flContext G hG).Model :=
  (flContext G hG).ofName ⟨flGenericName n, flGenericName_hereditarilySymmetric hn⟩

theorem mem_stageGeneric_iff {n : V} (hn : n ∈ (ω : V)) (x : (flContext G hG).Model) :
    x ∈ stageGeneric hG hn ↔ ∃ q ∈ G, q ∈ flStage n ∧ x = (flContext G hG).check q := by
  let S := flContext G hG
  rw [stageGeneric, S.mem_ofName_iff]
  constructor
  · rintro ⟨ν, p, hpG, hνp, rfl⟩
    obtain ⟨q, hq, he⟩ := (mem_flGenericName n _).mp hνp
    obtain ⟨hν, hpq⟩ := kpair_iff.mp he
    subst hpq
    exact ⟨p, hpG, hq, congrArg S.ofName (Subtype.ext hν)⟩
  · rintro ⟨q, hqG, hq, rfl⟩
    exact ⟨⟨checkName ∅ q, hereditarilySymmetric_checkName fl_poset flGroup_group flFilter_normal fl_top q⟩,
      q, hqG, (mem_flGenericName n _).mpr ⟨q, hq, rfl⟩, rfl⟩

/-- The union of the stage generic: the generic function on the first `n` columns. -/
noncomputable def stageFunction {n : V} (hn : n ∈ (ω : V)) : (flContext G hG).Model :=
  ⋃ˢ stageGeneric hG hn

theorem mem_stageFunction_iff {n : V} (hn : n ∈ (ω : V)) (x : (flContext G hG).Model) :
    x ∈ stageFunction hG hn ↔ ∃ q ∈ G, q ∈ flStage n ∧ x ∈ (flContext G hG).check q := by
  simp only [stageFunction, mem_sUnion_iff, mem_stageGeneric_iff]
  constructor
  · rintro ⟨y, ⟨q, hqG, hq, rfl⟩, hx⟩
    exact ⟨q, hqG, hq, hx⟩
  · rintro ⟨q, hqG, hq, hx⟩
    exact ⟨_, ⟨q, hqG, hq, rfl⟩, hx⟩

instance stageFunction_isFunction {n : V} (hn : n ∈ (ω : V)) : IsFunction (stageFunction hG hn) := by
  let S := flContext G hG
  have hfun (q : V) (hq : q ∈ G) : IsFunction (S.check q) := by
    have : IsFunction q := flStage_function (hG.1.1 q hq)
    exact S.checkEmbedding.map_function q
  apply isFunction_sUnion
  · intro f hf
    obtain ⟨q, hqG, _, rfl⟩ := (mem_stageGeneric_iff hG hn f).mp hf
    exact hfun q hqG
  · intro f hf g hg x y z hxy hxz
    obtain ⟨p, hpG, _, rfl⟩ := (mem_stageGeneric_iff hG hn f).mp hf
    obtain ⟨q, hqG, _, rfl⟩ := (mem_stageGeneric_iff hG hn g).mp hg
    obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p hpG q hqG
    have hpr : p ⊆ r := ((pair_mem_flOrder _ _).mp hrp).2.2
    have hqr : q ⊆ r := ((pair_mem_flOrder _ _).mp hrq).2.2
    have : IsFunction (S.check r) := hfun r hr
    exact IsFunction.unique (f := S.check r) ((S.checkEmbedding.subset_iff p r).mpr hpr _ hxy)
      ((S.checkEmbedding.subset_iff q r).mpr hqr _ hxz)

theorem stageFunction_pair {n m k v : V} (hn : n ∈ (ω : V)) (hm : m ∈ n)
    (hpair : ∃ p ∈ G, ⟨⟨m, k⟩ₖ, v⟩ₖ ∈ p) :
    ⟨⟨(flContext G hG).check m, (flContext G hG).check k⟩ₖ, (flContext G hG).check v⟩ₖ ∈
      stageFunction hG hn := by
  let S := flContext G hG
  obtain ⟨p, hpG, hp⟩ := hpair
  have hpP : p ∈ flConditions V := hG.1.1 p hpG
  have hkω : k ∈ (ω : V) := by
    have := flStage_domain hpP _ (mem_domain_of_kpair_mem hp)
    exact (kpair_mem_iff.mp this).2
  have hres : ⟨⟨m, k⟩ₖ, v⟩ₖ ∈ p ↾ (n ×ˢ (ω : V)) :=
    mem_restrict_iff.mpr ⟨hp, ⟨m, k⟩ₖ, kpair_mem_iff.mpr ⟨hm, hkω⟩, v, rfl⟩
  refine (mem_stageFunction_iff hG hn _).mpr ⟨p ↾ (n ×ˢ (ω : V)),
    hG.1.2.2.1 p hpG _ (flStage_subset hn _ (flRestrict_mem hpP n)) (flRestrict_le hpP hn),
    flRestrict_mem hpP n, ?_⟩
  have hk2 : ∀ x y : V, S.check ⟨x, y⟩ₖ = ⟨S.check x, S.check y⟩ₖ :=
    fun x y ↦ S.checkEmbedding.map_kpair x y
  rw [← hk2, ← hk2]
  exact (S.check_mem_iff _ _).mpr hres

/-- The column-`m` map: a surjection from omega onto the collapsed cardinal. -/
noncomputable def columnMap {m : V} (hm : m ∈ (ω : V)) : (flContext G hG).Model :=
  {z ∈ (ω : (flContext G hG).Model) ×ˢ (flContext G hG).check (flCardinal m) ;
    ⟨⟨(flContext G hG).check m, kpair.π₁ z⟩ₖ, kpair.π₂ z⟩ₖ ∈ stageFunction hG (ω_succ_closed hm)}

theorem pair_mem_columnMap {m : V} (hm : m ∈ (ω : V)) (x y : (flContext G hG).Model) :
    ⟨x, y⟩ₖ ∈ columnMap hG hm ↔ x ∈ (ω : (flContext G hG).Model) ∧
      y ∈ (flContext G hG).check (flCardinal m) ∧
      ⟨⟨(flContext G hG).check m, x⟩ₖ, y⟩ₖ ∈ stageFunction hG (ω_succ_closed hm) := by
  simp only [columnMap, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

theorem columnMap_mem_function {m : V} (hm : m ∈ (ω : V)) :
    columnMap hG hm ∈ (flContext G hG).check (flCardinal m) ^ (ω : (flContext G hG).Model) := by
  let S := flContext G hG
  have hω : S.check (ω : V) = (ω : S.Model) := S.checkEmbedding.map_omega
  have hmsucc : m ∈ succ m := mem_succ_self m
  apply mem_function.intro
  · intro z hz
    obtain ⟨hzP, _⟩ := mem_sep_iff.mp hz
    exact hzP
  · intro x hx
    rw [← hω] at hx
    obtain ⟨k, hk, rfl⟩ := (S.mem_check_iff ω x).mp hx
    obtain ⟨p, hpG, hp⟩ := hG.2 _ (fl_coordinate_dense hm hk)
    obtain ⟨hpP, hdom⟩ := mem_sep_iff.mp hp
    obtain ⟨v, hv⟩ := mem_domain_iff.mp hdom
    have hvC : v ∈ flCardinal m := by
      have := flStage_values hpP _ hv
      simpa using this
    have hpair := stageFunction_pair hG (ω_succ_closed hm) hmsucc ⟨p, hpG, hv⟩
    refine ⟨S.check v, (pair_mem_columnMap hG hm _ _).mpr
      ⟨by rw [← hω]; exact (S.check_mem_iff k ω).mpr hk, (S.check_mem_iff v _).mpr hvC, hpair⟩, ?_⟩
    intro y hy
    obtain ⟨_, _, hy'⟩ := (pair_mem_columnMap hG hm _ _).mp hy
    exact IsFunction.unique hy' hpair

theorem columnMap_range {m : V} (hm : m ∈ (ω : V)) :
    range (columnMap hG hm) = (flContext G hG).check (flCardinal m) := by
  let S := flContext G hG
  have hω : S.check (ω : V) = (ω : S.Model) := S.checkEmbedding.map_omega
  apply SetTheory.subset_antisymm (range_subset_of_mem_function (columnMap_mem_function hG hm))
  intro y hy
  obtain ⟨v, hv, rfl⟩ := (S.mem_check_iff _ y).mp hy
  obtain ⟨p, hpG, hp⟩ := hG.2 _ (fl_column_value_dense hm hv)
  obtain ⟨_, k, hk, hkv⟩ := mem_sep_iff.mp hp
  have hpair := stageFunction_pair hG (ω_succ_closed hm) (mem_succ_self m) ⟨p, hpG, hkv⟩
  exact mem_range_of_kpair_mem (x := S.check k) ((pair_mem_columnMap hG hm _ _).mpr
    ⟨by rw [← hω]; exact (S.check_mem_iff k ω).mpr hk, hy, hpair⟩)

theorem check_flCardinal_cardLE_omega {m : V} (hm : m ∈ (ω : V)) :
    (flContext G hG).check (flCardinal m) ≤# (ω : (flContext G hG).Model) :=
  cardLE_of_surjective_function internallyCountable_omega.wellOrderable
    (columnMap_mem_function hG hm) (columnMap_range hG hm)

/-- The ground map from naturals to their check names, as a set. -/
noncomputable def checkNameGraph (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  definableGraph (ω : V) (checkName ∅) (by definability)

instance checkNameGraph_isFunction : IsFunction (checkNameGraph V) := definableGraph_isFunction _ _ _

theorem checkNameGraph_value {k : V} (hk : k ∈ (ω : V)) : (checkNameGraph V) ‘ k = checkName ∅ k :=
  value_definableGraph _ _ _ hk

theorem domain_checkNameGraph : domain (checkNameGraph V) = ω := domain_definableGraph _ _ _

/-- Under choice the stage-`n` set injects into the check of the nice names of stage `n`. -/
theorem stageSet_cardLE_names (hAC : InternalChoice V) {n : V} (hn : n ∈ (ω : V)) :
    stageSet hG hn ≤# (flContext G hG).check (flNames n) := by
  let S := flContext G hG
  have hω : S.check (ω : V) = (ω : S.Model) := S.checkEmbedding.map_omega
  have hwo : IsWellOrderable (S.check (flNames n)) :=
    (wellOrderable_iff_cardLE_ordinal _).mpr ⟨S.check (flCardinal n), inferInstance,
      S.checkEmbedding.map_cardLE (flNiceNames_cardLE hAC n)⟩
  have hC : IsFunction (S.check (checkNameGraph V)) := S.checkEmbedding.map_function _
  have hk2 : ∀ x y : V, S.check ⟨x, y⟩ₖ = ⟨S.check x, S.check y⟩ₖ :=
    fun x y ↦ S.checkEmbedding.map_kpair x y
  have hval : ∀ k ∈ (ω : V), (S.check (checkNameGraph V)) ‘ (S.check k) = S.check (checkName ∅ k) := by
    intro k hk
    have h := S.checkEmbedding.map_value (checkNameGraph V) k (by rw [domain_checkNameGraph]; exact hk)
    rw [checkNameGraph_value hk] at h
    exact h.symm
  let Q : S.Model → S.Model → Prop := fun x τ ↦ ∀ y, y ∈ x ↔ ∃ k ∈ (ω : S.Model), y = k ∧
    ∃ q ∈ stageGeneric hG hn, ⟨(S.check (checkNameGraph V)) ‘ k, q⟩ₖ ∈ τ
  have hQ : ℒₛₑₜ-relation Q := by definability
  apply cardLE_of_separating_relation hwo Q hQ
  · intro x hx
    obtain ⟨τ, hτ, rfl⟩ := (mem_stageSet_iff hG hn x).mp hx
    refine ⟨S.check τ, (S.check_mem_iff τ _).mpr hτ, ?_⟩
    intro y
    rw [S.mem_ofName_iff]
    constructor
    · rintro ⟨ν, s, hsG, hνs, rfl⟩
      obtain ⟨k, hk, s', hs', he⟩ := (mem_flNames hn).mp hτ _ hνs
      obtain ⟨hν, hss'⟩ := kpair_iff.mp he
      subst hss'
      refine ⟨S.check k, by rw [← hω]; exact (S.check_mem_iff k ω).mpr hk,
        congrArg S.ofName (Subtype.ext hν), S.check s, (mem_stageGeneric_iff hG hn _).mpr ⟨s, hsG, hs', rfl⟩, ?_⟩
      rw [hval k hk, ← hk2, S.check_mem_iff]
      rw [hν] at hνs
      exact hνs
    · rintro ⟨k', hk', hyk, q, hq, hmem⟩
      rw [← hω] at hk'
      obtain ⟨k, hk, rfl⟩ := (S.mem_check_iff ω k').mp hk'
      obtain ⟨s, hsG, hs, rfl⟩ := (mem_stageGeneric_iff hG hn q).mp hq
      rw [hval k hk, ← hk2, S.check_mem_iff] at hmem
      rw [hyk]
      exact ⟨⟨checkName ∅ k, hereditarilySymmetric_checkName fl_poset flGroup_group flFilter_normal fl_top k⟩,
        s, hsG, hmem, rfl⟩
  · intro x _ z _ τ _ hx hz
    apply S.extensionality
    intro y
    exact (hx y).trans (hz y).symm

theorem stageSet_countable (hAC : InternalChoice V) {n : V} (hn : n ∈ (ω : V)) :
    IsInternallyCountable (stageSet hG hn) :=
  (stageSet_cardLE_names hG hAC hn).trans
    (((flContext G hG).checkEmbedding.map_cardLE (flNiceNames_cardLE hAC n)).trans
      (check_flCardinal_cardLE_omega hG hn))

end FefermanLevyModel
end ZFVP
