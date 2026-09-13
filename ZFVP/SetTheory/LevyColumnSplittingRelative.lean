import ZFVP.SetTheory.LevyColumnSplitting

/-! Relative column splitting: a column collapse on `C'` splits at a sub-column set `C ⊆ C'` into
the product of the column collapses on `C` and on `C' \ C`, by inverse dense embeddings. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ C C' : V} (hCC' : C ⊆ C')

theorem levyColumns_mono {p : V} (hp : p ∈ levyColumns κ C) (h : C ⊆ C') : p ∈ levyColumns κ C' := by
  obtain ⟨hpL, hcut⟩ := (mem_levyColumns_iff _ _ _).mp hp
  refine (mem_levyColumns_iff _ _ _).mpr ⟨hpL, SetTheory.subset_antisymm (levyCut_subset _ _) ?_⟩
  intro z hz
  obtain ⟨n, α, γ, hn, _, rfl⟩ := levyCollapse_mem_shape hpL hz
  exact (kpair_mem_levyCut_iff _ _ _ _).mpr ⟨hz, kpair_mem_iff.mpr ⟨hn, h _ (column_mem_of_levyColumns hp hz)⟩⟩

theorem levyUpper_mem_levyColumns_sdiff {p : V} (hp : p ∈ levyColumns κ C') :
    levyUpper C p ∈ levyColumns κ (C' \ C) := by
  have hpL := levyColumns_subset κ C' p hp
  refine (mem_levyColumns_iff _ _ _).mpr ⟨levyCollapse_subset hpL (levyUpper_subset C p), ?_⟩
  apply SetTheory.subset_antisymm (levyCut_subset _ _)
  intro z hz
  obtain ⟨n, α, γ, hn, _, rfl⟩ := levyCollapse_mem_shape hpL (levyUpper_subset C p z hz)
  obtain ⟨hzp, hx⟩ := (kpair_mem_levyUpper_iff _ _ _ _).mp hz
  refine (kpair_mem_levyCut_iff _ _ _ _).mpr ⟨hz, kpair_mem_iff.mpr ⟨hn, mem_sdiff_iff.mpr
    ⟨column_mem_of_levyColumns hp hzp, fun hαC ↦ hx (kpair_mem_iff.mpr ⟨hn, hαC⟩)⟩⟩⟩

include hCC' in
theorem union_mem_levyColumns_of_sdiff {a b : V} (ha : a ∈ levyColumns κ C) (hb : b ∈ levyColumns κ (C' \ C)) :
    a ∪ b ∈ levyColumns κ C' := by
  have hab : a ∪ b ∈ levyCollapse κ := by
    refine levyCollapse_union (levyColumns_subset κ C a ha) (levyColumns_subset κ _ b hb) ?_
    intro x y z hxy hxz
    obtain ⟨n, α, γ, _, _, he⟩ := levyCollapse_mem_shape (levyColumns_subset κ C a ha) hxy
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact ((mem_sdiff_iff.mp (column_mem_of_levyColumns hb hxz)).2 (column_mem_of_levyColumns ha hxy)).elim
  refine (mem_levyColumns_iff _ _ _).mpr ⟨hab, SetTheory.subset_antisymm (levyCut_subset _ _) ?_⟩
  intro z hz
  obtain ⟨n, α, γ, hn, _, rfl⟩ := levyCollapse_mem_shape hab hz
  refine (kpair_mem_levyCut_iff _ _ _ _).mpr ⟨hz, kpair_mem_iff.mpr ⟨hn, ?_⟩⟩
  rcases mem_union_iff.mp hz with h | h
  · exact hCC' _ (column_mem_of_levyColumns ha h)
  · exact (mem_sdiff_iff.mp (column_mem_of_levyColumns hb h)).1

theorem levyCut_union_sdiff {a b : V} (ha : a ∈ levyColumns κ C) (hb : b ∈ levyColumns κ (C' \ C)) :
    levyCut C (a ∪ b) = a := by
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨hzu, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
    rcases mem_union_iff.mp hzu with h | h
    · exact h
    · exfalso
      obtain ⟨n, α, γ, _, _, he⟩ := levyCollapse_mem_shape (levyColumns_subset κ _ b hb) h
      obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
      exact (mem_sdiff_iff.mp (column_mem_of_levyColumns hb h)).2 (kpair_mem_iff.mp hx).2
  · intro hz
    have hz' : z ∈ levyCut C a := by rw [((mem_levyColumns_iff _ _ _).mp ha).2]; exact hz
    exact levyCut_mono (fun w hw ↦ mem_union_iff.mpr (Or.inl hw)) z hz'

theorem levyUpper_union_sdiff {a b : V} (ha : a ∈ levyColumns κ C) (hb : b ∈ levyColumns κ (C' \ C)) :
    levyUpper C (a ∪ b) = b := by
  apply mem_ext
  intro z
  rw [mem_levyUpper_iff, levyCut_union_sdiff ha hb, mem_union_iff]
  constructor
  · rintro ⟨h, hna⟩
    rcases h with h | h
    · exact (hna h).elim
    · exact h
  · intro hz
    refine ⟨Or.inr hz, fun hza ↦ ?_⟩
    obtain ⟨n, α, γ, _, _, rfl⟩ := levyCollapse_mem_shape (levyColumns_subset κ _ b hb) hz
    exact (mem_sdiff_iff.mp (column_mem_of_levyColumns hb hz)).2 (column_mem_of_levyColumns ha hza)

/-- The relative product of column collapses. -/
noncomputable def columnProductRel (κ C C' : V) : V := levyColumns κ C ×ˢ levyColumns κ (C' \ C)

noncomputable def columnProductRelOrder (κ C C' : V) : V :=
  productOrder (levyColumns κ C) (levyColumnsOrder κ C) (levyColumns κ (C' \ C)) (levyColumnsOrder κ (C' \ C))

theorem columnProductRelOrder_iff {a b a' b' : V} :
    ⟨⟨a, b⟩ₖ, ⟨a', b'⟩ₖ⟩ₖ ∈ columnProductRelOrder κ C C' ↔
      a ∈ levyColumns κ C ∧ b ∈ levyColumns κ (C' \ C) ∧ a' ∈ levyColumns κ C ∧ b' ∈ levyColumns κ (C' \ C) ∧
        a' ⊆ a ∧ b' ⊆ b := by
  unfold columnProductRelOrder levyColumnsOrder
  rw [pair_mem_productOrder_iff, pair_mem_reverseInclusionOrder, pair_mem_reverseInclusionOrder]
  constructor
  · rintro ⟨ha, hb, ha', hb', ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩
    exact ⟨ha, hb, ha', hb', h1, h2⟩
  · rintro ⟨ha, hb, ha', hb', h1, h2⟩
    exact ⟨ha, hb, ha', hb', ⟨ha, ha', h1⟩, ⟨hb, hb', h2⟩⟩

/-- The relative splitting map on the column collapse `C'`. -/
noncomputable def columnSplitRel (κ C C' : V) : V :=
  definableGraph (levyColumns κ C') (fun p ↦ ⟨levyCut C p, levyUpper C p⟩ₖ)
    (by unfold levyUpper levyCut; definability)

theorem columnSplitRel_value {p : V} (hp : p ∈ levyColumns κ C') :
    (columnSplitRel κ C C') ‘ p = ⟨levyCut C p, levyUpper C p⟩ₖ :=
  value_definableGraph _ _ _ hp

theorem levyCut_mem_levyColumns_of_columns {p : V} (hp : p ∈ levyColumns κ C') : levyCut C p ∈ levyColumns κ C :=
  levyCut_mem_levyColumns (levyColumns_subset κ C' p hp)

include hCC' in
/-- Relative column splitting is a dense embedding. -/
theorem columnSplitRel_denseEmbedding :
    IsDenseEmbedding (levyColumns κ C') (levyColumnsOrder κ C') (columnProductRel κ C C')
      (columnProductRelOrder κ C C') (columnSplitRel κ C C') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply definableGraph_mem_function_of_mapsTo
    intro p hp
    exact kpair_mem_iff.mpr ⟨levyCut_mem_levyColumns_of_columns hp, levyUpper_mem_levyColumns_sdiff hp⟩
  · intro p hp q hq hqp
    obtain ⟨_, _, hpq⟩ := (pair_mem_reverseInclusionOrder _ _ _).mp hqp
    rw [columnSplitRel_value hp, columnSplitRel_value hq]
    exact columnProductRelOrder_iff.mpr ⟨levyCut_mem_levyColumns_of_columns hq, levyUpper_mem_levyColumns_sdiff hq,
      levyCut_mem_levyColumns_of_columns hp, levyUpper_mem_levyColumns_sdiff hp, levyCut_mono hpq, levyUpper_mono hpq⟩
  · intro p hp q hq hinc hc
    rw [columnSplitRel_value hp, columnSplitRel_value hq] at hc
    obtain ⟨z, hz, hz1, hz2⟩ := hc
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨_, _, _, _, h1, h2⟩ := columnProductRelOrder_iff.mp hz1
    obtain ⟨_, _, _, _, h3, h4⟩ := columnProductRelOrder_iff.mp hz2
    apply hinc
    have hab := union_mem_levyColumns_of_sdiff hCC' ha hb
    refine ⟨a ∪ b, hab, (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hab, hp, ?_⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hab, hq, ?_⟩⟩
    · rw [← levyCut_union_levyUpper C p]
      intro z hz
      rcases mem_union_iff.mp hz with h | h
      · exact mem_union_iff.mpr (Or.inl (h1 z h))
      · exact mem_union_iff.mpr (Or.inr (h2 z h))
    · rw [← levyCut_union_levyUpper C q]
      intro z hz
      rcases mem_union_iff.mp hz with h | h
      · exact mem_union_iff.mpr (Or.inl (h3 z h))
      · exact mem_union_iff.mpr (Or.inr (h4 z h))
  · intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    have hab := union_mem_levyColumns_of_sdiff hCC' ha hb
    refine ⟨a ∪ b, hab, ?_⟩
    rw [columnSplitRel_value hab, levyCut_union_sdiff ha hb, levyUpper_union_sdiff ha hb]
    exact columnProductRelOrder_iff.mpr ⟨ha, hb, ha, hb, fun z hz ↦ hz, fun z hz ↦ hz⟩

/-- The relative joining map. -/
noncomputable def columnJoinRel (κ C C' : V) : V :=
  definableGraph (columnProductRel κ C C') (fun z ↦ kpair.π₁ z ∪ kpair.π₂ z) (by definability)

theorem columnJoinRel_value {a b : V} (ha : a ∈ levyColumns κ C) (hb : b ∈ levyColumns κ (C' \ C)) :
    (columnJoinRel κ C C') ‘ ⟨a, b⟩ₖ = a ∪ b := by
  unfold columnJoinRel columnProductRel
  rw [value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨ha, hb⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

include hCC' in
/-- Relative column joining is a dense embedding. -/
theorem columnJoinRel_denseEmbedding :
    IsDenseEmbedding (columnProductRel κ C C') (columnProductRelOrder κ C C') (levyColumns κ C')
      (levyColumnsOrder κ C') (columnJoinRel κ C C') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply definableGraph_mem_function_of_mapsTo
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact union_mem_levyColumns_of_sdiff hCC' ha hb
  · intro z hz z' hz' hzz'
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_prod_iff.mp hz'
    obtain ⟨_, _, _, _, h1, h2⟩ := columnProductRelOrder_iff.mp hzz'
    rw [columnJoinRel_value ha hb, columnJoinRel_value ha' hb']
    refine (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨union_mem_levyColumns_of_sdiff hCC' ha' hb',
      union_mem_levyColumns_of_sdiff hCC' ha hb, ?_⟩
    intro w hw
    rcases mem_union_iff.mp hw with h | h
    · exact mem_union_iff.mpr (Or.inl (h1 w h))
    · exact mem_union_iff.mpr (Or.inr (h2 w h))
  · intro z hz z' hz' hinc hc
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_prod_iff.mp hz'
    rw [columnJoinRel_value ha hb, columnJoinRel_value ha' hb'] at hc
    obtain ⟨r, hr, hr1, hr2⟩ := hc
    obtain ⟨_, _, h1⟩ := (pair_mem_reverseInclusionOrder _ _ _).mp hr1
    obtain ⟨_, _, h2⟩ := (pair_mem_reverseInclusionOrder _ _ _).mp hr2
    apply hinc
    refine ⟨⟨levyCut C r, levyUpper C r⟩ₖ, kpair_mem_iff.mpr ⟨levyCut_mem_levyColumns_of_columns hr,
      levyUpper_mem_levyColumns_sdiff hr⟩, ?_, ?_⟩
    · refine columnProductRelOrder_iff.mpr ⟨levyCut_mem_levyColumns_of_columns hr, levyUpper_mem_levyColumns_sdiff hr, ha, hb, ?_, ?_⟩
      · rw [← levyCut_union_sdiff ha hb]
        exact levyCut_mono h1
      · rw [← levyUpper_union_sdiff ha hb]
        exact levyUpper_mono h1
    · refine columnProductRelOrder_iff.mpr ⟨levyCut_mem_levyColumns_of_columns hr, levyUpper_mem_levyColumns_sdiff hr, ha', hb', ?_, ?_⟩
      · rw [← levyCut_union_sdiff ha' hb']
        exact levyCut_mono h2
      · rw [← levyUpper_union_sdiff ha' hb']
        exact levyUpper_mono h2
  · intro p hp
    refine ⟨⟨levyCut C p, levyUpper C p⟩ₖ, kpair_mem_iff.mpr ⟨levyCut_mem_levyColumns_of_columns hp,
      levyUpper_mem_levyColumns_sdiff hp⟩, ?_⟩
    rw [columnJoinRel_value (levyCut_mem_levyColumns_of_columns hp) (levyUpper_mem_levyColumns_sdiff hp),
      levyCut_union_levyUpper]
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hp, hp, fun z hz ↦ hz⟩

end

end ZFVP
