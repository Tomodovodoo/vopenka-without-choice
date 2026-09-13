import ZFVP.SetTheory.LevyCollapseUpper
import ZFVP.SetTheory.ProductForcing
import ZFVP.SetTheory.DenseEmbedding

/-! Column splitting of the Levy collapse: for any set `C` of columns, a condition is the union of
its restriction to the columns in `C` and its restriction to the remaining columns, and this
decomposition is a dense embedding (an isomorphism) between `Coll(ω, <κ)` and the product of the
two column collapses. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Conditions supported on the columns `C`. -/
noncomputable def levyColumns (κ C : V) : V := {p ∈ levyCollapse κ ; levyCut C p = p}

theorem mem_levyColumns_iff (κ C p : V) : p ∈ levyColumns κ C ↔ p ∈ levyCollapse κ ∧ levyCut C p = p :=
  mem_sep_iff

theorem levyColumns_subset (κ C : V) : levyColumns κ C ⊆ levyCollapse κ := sep_subset

/-- Elements of a Levy condition are pairs `⟨⟨n, α⟩, γ⟩` with `α ∈ κ`. -/
theorem levyCollapse_mem_shape {κ p z : V} (hp : p ∈ levyCollapse κ) (hz : z ∈ p) :
    ∃ n α γ : V, n ∈ (ω : V) ∧ α ∈ κ ∧ z = ⟨⟨n, α⟩ₖ, γ⟩ₖ := by
  obtain ⟨hfp, _⟩ := (mem_levyCollapse_iff κ p).mp hp
  have hz' := ((mem_finitePartialFunctions _ _ _).mp hfp).1 z hz
  obtain ⟨x, hx, γ, _, rfl⟩ := mem_prod_iff.mp hz'
  obtain ⟨n, hn, α, hα, rfl⟩ := mem_prod_iff.mp hx
  exact ⟨n, α, γ, hn, hα, rfl⟩

theorem levyCut_levyCut (C p : V) : levyCut C (levyCut C p) = levyCut C p := by
  unfold levyCut
  rw [restrict_restrict_eq_restrict_inter, inter_eq_right_of_subset (fun z hz ↦ hz)]

theorem levyCut_mem_levyColumns {κ C p : V} (hp : p ∈ levyCollapse κ) : levyCut C p ∈ levyColumns κ C :=
  (mem_levyColumns_iff _ _ _).mpr ⟨levyCollapse_subset hp (levyCut_subset C p), levyCut_levyCut C p⟩

theorem levyUpper_mem_levyColumns_compl {κ C p : V} (hp : p ∈ levyCollapse κ) :
    levyUpper C p ∈ levyColumns κ (κ \ C) := by
  refine (mem_levyColumns_iff _ _ _).mpr ⟨levyCollapse_subset hp (levyUpper_subset C p), ?_⟩
  apply SetTheory.subset_antisymm (levyCut_subset _ _)
  intro z hz
  obtain ⟨n, α, γ, hn, hα, rfl⟩ := levyCollapse_mem_shape hp (levyUpper_subset C p z hz)
  obtain ⟨hzp, hx⟩ := (kpair_mem_levyUpper_iff _ _ _ _).mp hz
  refine (kpair_mem_levyCut_iff _ _ _ _).mpr ⟨hz, kpair_mem_iff.mpr ⟨hn, mem_sdiff_iff.mpr ⟨hα, ?_⟩⟩⟩
  intro hαC
  exact hx (kpair_mem_iff.mpr ⟨hn, hαC⟩)

theorem column_mem_of_levyColumns {κ C a n α γ : V} (ha : a ∈ levyColumns κ C)
    (h : ⟨⟨n, α⟩ₖ, γ⟩ₖ ∈ a) : α ∈ C := by
  obtain ⟨_, hcut⟩ := (mem_levyColumns_iff _ _ _).mp ha
  rw [← hcut] at h
  exact (kpair_mem_iff.mp ((kpair_mem_levyCut_iff _ _ _ _).mp h).2).2

theorem union_mem_of_levyColumns {κ C a b : V} (ha : a ∈ levyColumns κ C)
    (hb : b ∈ levyColumns κ (κ \ C)) : a ∪ b ∈ levyCollapse κ := by
  refine levyCollapse_union (levyColumns_subset κ C a ha) (levyColumns_subset κ _ b hb) ?_
  intro x y z hxy hxz
  obtain ⟨n, α, γ, _, _, he⟩ := levyCollapse_mem_shape (levyColumns_subset κ C a ha) hxy
  obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
  have h1 := column_mem_of_levyColumns ha hxy
  have h2 := column_mem_of_levyColumns hb hxz
  exact ((mem_sdiff_iff.mp h2).2 h1).elim

theorem levyCut_union_levyColumns {κ C a b : V} (ha : a ∈ levyColumns κ C)
    (hb : b ∈ levyColumns κ (κ \ C)) : levyCut C (a ∪ b) = a := by
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
      have := column_mem_of_levyColumns hb h
      exact (mem_sdiff_iff.mp this).2 (kpair_mem_iff.mp hx).2
  · intro hz
    have hz' : z ∈ levyCut C a := by rw [((mem_levyColumns_iff _ _ _).mp ha).2]; exact hz
    exact levyCut_mono (fun w hw ↦ mem_union_iff.mpr (Or.inl hw)) z hz'

theorem levyUpper_union_levyColumns {κ C a b : V} (ha : a ∈ levyColumns κ C)
    (hb : b ∈ levyColumns κ (κ \ C)) : levyUpper C (a ∪ b) = b := by
  apply mem_ext
  intro z
  rw [mem_levyUpper_iff, levyCut_union_levyColumns ha hb, mem_union_iff]
  constructor
  · rintro ⟨h, hna⟩
    rcases h with h | h
    · exact (hna h).elim
    · exact h
  · intro hz
    refine ⟨Or.inr hz, fun hza ↦ ?_⟩
    obtain ⟨n, α, γ, _, _, rfl⟩ := levyCollapse_mem_shape (levyColumns_subset κ _ b hb) hz
    exact (mem_sdiff_iff.mp (column_mem_of_levyColumns hb hz)).2 (column_mem_of_levyColumns ha hza)

/-- The order on a column collapse. -/
noncomputable def levyColumnsOrder (κ C : V) : V := reverseInclusionOrder (levyColumns κ C)

/-- The product of the two column collapses. -/
noncomputable def columnProduct (κ C : V) : V := levyColumns κ C ×ˢ levyColumns κ (κ \ C)

noncomputable def columnProductOrder (κ C : V) : V :=
  productOrder (levyColumns κ C) (levyColumnsOrder κ C) (levyColumns κ (κ \ C)) (levyColumnsOrder κ (κ \ C))

/-- The splitting map `p ↦ ⟨p ↾ C, p ↾ (κ \ C)⟩`. -/
noncomputable def columnSplit (κ C : V) : V :=
  definableGraph (levyCollapse κ) (fun p ↦ ⟨levyCut C p, levyUpper C p⟩ₖ)
    (by unfold levyUpper levyCut; definability)

theorem columnSplit_value {κ C p : V} (hp : p ∈ levyCollapse κ) :
    (columnSplit κ C) ‘ p = ⟨levyCut C p, levyUpper C p⟩ₖ :=
  value_definableGraph _ _ _ hp

theorem columnProductOrder_iff {κ C a b a' b' : V} :
    ⟨⟨a, b⟩ₖ, ⟨a', b'⟩ₖ⟩ₖ ∈ columnProductOrder κ C ↔
      a ∈ levyColumns κ C ∧ b ∈ levyColumns κ (κ \ C) ∧ a' ∈ levyColumns κ C ∧ b' ∈ levyColumns κ (κ \ C) ∧
        a' ⊆ a ∧ b' ⊆ b := by
  unfold columnProductOrder levyColumnsOrder
  rw [pair_mem_productOrder_iff, pair_mem_reverseInclusionOrder, pair_mem_reverseInclusionOrder]
  constructor
  · rintro ⟨ha, hb, ha', hb', ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩
    exact ⟨ha, hb, ha', hb', h1, h2⟩
  · rintro ⟨ha, hb, ha', hb', h1, h2⟩
    exact ⟨ha, hb, ha', hb', ⟨ha, ha', h1⟩, ⟨hb, hb', h2⟩⟩

/-- Column splitting is a dense embedding of the Levy collapse into the product of the column
collapses. -/
theorem columnSplit_denseEmbedding (κ C : V) :
    IsDenseEmbedding (levyCollapse κ) (levyOrder κ) (columnProduct κ C) (columnProductOrder κ C)
      (columnSplit κ C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply definableGraph_mem_function_of_mapsTo
    intro p hp
    exact kpair_mem_iff.mpr ⟨levyCut_mem_levyColumns hp, levyUpper_mem_levyColumns_compl hp⟩
  · intro p hp q hq hqp
    obtain ⟨_, _, hpq⟩ := (pair_mem_reverseInclusionOrder _ _ _).mp hqp
    rw [columnSplit_value hp, columnSplit_value hq]
    exact columnProductOrder_iff.mpr ⟨levyCut_mem_levyColumns hq, levyUpper_mem_levyColumns_compl hq,
      levyCut_mem_levyColumns hp, levyUpper_mem_levyColumns_compl hp, levyCut_mono hpq, levyUpper_mono hpq⟩
  · intro p hp q hq hinc hc
    rw [columnSplit_value hp, columnSplit_value hq] at hc
    obtain ⟨z, hz, hz1, hz2⟩ := hc
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨_, _, _, _, h1, h2⟩ := columnProductOrder_iff.mp hz1
    obtain ⟨_, _, _, _, h3, h4⟩ := columnProductOrder_iff.mp hz2
    apply hinc
    have hab := union_mem_of_levyColumns ha hb
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
    have hab := union_mem_of_levyColumns ha hb
    refine ⟨a ∪ b, hab, ?_⟩
    rw [columnSplit_value hab, levyCut_union_levyColumns ha hb, levyUpper_union_levyColumns ha hb]
    exact columnProductOrder_iff.mpr ⟨ha, hb, ha, hb, fun z hz ↦ hz, fun z hz ↦ hz⟩

/-- The joining map `⟨a, b⟩ ↦ a ∪ b`. -/
noncomputable def columnJoin (κ C : V) : V :=
  definableGraph (columnProduct κ C) (fun z ↦ kpair.π₁ z ∪ kpair.π₂ z) (by definability)

theorem columnJoin_value {κ C a b : V} (ha : a ∈ levyColumns κ C) (hb : b ∈ levyColumns κ (κ \ C)) :
    (columnJoin κ C) ‘ ⟨a, b⟩ₖ = a ∪ b := by
  unfold columnJoin columnProduct
  rw [value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨ha, hb⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

/-- Column joining is a dense embedding of the product of the column collapses into the Levy
collapse. -/
theorem columnJoin_denseEmbedding (κ C : V) :
    IsDenseEmbedding (columnProduct κ C) (columnProductOrder κ C) (levyCollapse κ) (levyOrder κ)
      (columnJoin κ C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply definableGraph_mem_function_of_mapsTo
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact union_mem_of_levyColumns ha hb
  · intro z hz z' hz' hzz'
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_prod_iff.mp hz'
    obtain ⟨_, _, _, _, h1, h2⟩ := columnProductOrder_iff.mp hzz'
    rw [columnJoin_value ha hb, columnJoin_value ha' hb']
    refine (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨union_mem_of_levyColumns ha' hb',
      union_mem_of_levyColumns ha hb, ?_⟩
    intro w hw
    rcases mem_union_iff.mp hw with h | h
    · exact mem_union_iff.mpr (Or.inl (h1 w h))
    · exact mem_union_iff.mpr (Or.inr (h2 w h))
  · intro z hz z' hz' hinc hc
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_prod_iff.mp hz'
    rw [columnJoin_value ha hb, columnJoin_value ha' hb'] at hc
    obtain ⟨r, hr, hr1, hr2⟩ := hc
    obtain ⟨_, _, h1⟩ := (pair_mem_reverseInclusionOrder _ _ _).mp hr1
    obtain ⟨_, _, h2⟩ := (pair_mem_reverseInclusionOrder _ _ _).mp hr2
    apply hinc
    refine ⟨⟨levyCut C r, levyUpper C r⟩ₖ, kpair_mem_iff.mpr ⟨levyCut_mem_levyColumns hr,
      levyUpper_mem_levyColumns_compl hr⟩, ?_, ?_⟩
    · refine columnProductOrder_iff.mpr ⟨levyCut_mem_levyColumns hr, levyUpper_mem_levyColumns_compl hr, ha, hb, ?_, ?_⟩
      · rw [← levyCut_union_levyColumns ha hb]
        exact levyCut_mono h1
      · rw [← levyUpper_union_levyColumns ha hb]
        exact levyUpper_mono h1
    · refine columnProductOrder_iff.mpr ⟨levyCut_mem_levyColumns hr, levyUpper_mem_levyColumns_compl hr, ha', hb', ?_, ?_⟩
      · rw [← levyCut_union_levyColumns ha' hb']
        exact levyCut_mono h2
      · rw [← levyUpper_union_levyColumns ha' hb']
        exact levyUpper_mono h2
  · intro p hp
    refine ⟨⟨levyCut C p, levyUpper C p⟩ₖ, kpair_mem_iff.mpr ⟨levyCut_mem_levyColumns hp,
      levyUpper_mem_levyColumns_compl hp⟩, ?_⟩
    rw [columnJoin_value (levyCut_mem_levyColumns hp) (levyUpper_mem_levyColumns_compl hp),
      levyCut_union_levyUpper]
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hp, hp, fun z hz ↦ hz⟩

end ZFVP
