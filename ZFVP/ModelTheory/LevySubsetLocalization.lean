import ZFVP.ModelTheory.LevyCollapseReals

/-! Localization of subsets of a small ground set: every subset of `θ̌`, `θ < κ`, in the Levy
extension lies in some bounded stage `V[G_ξ]`. This is the real-localization argument with the
index set `ω` replaced by `θ`: the tagged decision conditions carry a maximal antichain whose
slices have bounded supports, and `κ` is regular. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The disjoint union of `θ` copies of a forcing preorder. -/
noncomputable def taggedOrderOn (θ P R : V) : V :=
  {z ∈ (θ ×ˢ P) ×ˢ (θ ×ˢ P) ;
    kpair.π₁ (kpair.π₁ z) = kpair.π₁ (kpair.π₂ z) ∧
      ⟨kpair.π₂ (kpair.π₁ z), kpair.π₂ (kpair.π₂ z)⟩ₖ ∈ R}

theorem kpair_mem_taggedOrderOn_iff (θ P R n p m q : V) :
    ⟨⟨n, p⟩ₖ, ⟨m, q⟩ₖ⟩ₖ ∈ taggedOrderOn θ P R ↔
      n ∈ θ ∧ p ∈ P ∧ m ∈ θ ∧ q ∈ P ∧ n = m ∧ ⟨p, q⟩ₖ ∈ R := by
  unfold taggedOrderOn
  simp only [mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

theorem taggedOrderOn_preorder {θ P R : V} (hR : IsForcingPreorder P R) :
    IsForcingPreorder (θ ×ˢ P) (taggedOrderOn θ P R) := by
  refine ⟨sep_subset, ?_, ?_⟩
  · intro z hz
    obtain ⟨n, hn, p, hp, rfl⟩ := mem_prod_iff.mp hz
    exact (kpair_mem_taggedOrderOn_iff θ P R n p n p).mpr ⟨hn, hp, hn, hp, rfl, hR.2.1 p hp⟩
  · intro z hz z' hz' z'' hz'' h1 h2
    obtain ⟨n, hn, p, hp, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨m, hm, q, hq, rfl⟩ := mem_prod_iff.mp hz'
    obtain ⟨k, hk, r, hr, rfl⟩ := mem_prod_iff.mp hz''
    obtain ⟨_, _, _, _, hnm, hpq⟩ := (kpair_mem_taggedOrderOn_iff θ P R n p m q).mp h1
    obtain ⟨_, _, _, _, hmk, hqr⟩ := (kpair_mem_taggedOrderOn_iff θ P R m q k r).mp h2
    exact (kpair_mem_taggedOrderOn_iff θ P R n p k r).mpr
      ⟨hn, hp, hk, hr, hnm.trans hmk, hR.2.2 p hp q hq r hr hpq hqr⟩

theorem taggedCompatibleOn_iff {θ P R n p m q : V} (hn : n ∈ θ) (hp : p ∈ P) (hm : m ∈ θ)
    (hq : q ∈ P) :
    ForcingCompatible (θ ×ˢ P) (taggedOrderOn θ P R) ⟨n, p⟩ₖ ⟨m, q⟩ₖ ↔
      n = m ∧ ForcingCompatible P R p q := by
  constructor
  · rintro ⟨z, hz, h1, h2⟩
    obtain ⟨k, hk, r, hr, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨_, _, _, _, hkn, hrp⟩ := (kpair_mem_taggedOrderOn_iff θ P R k r n p).mp h1
    obtain ⟨_, _, _, _, hkm, hrq⟩ := (kpair_mem_taggedOrderOn_iff θ P R k r m q).mp h2
    exact ⟨hkn.symm.trans hkm, r, hr, hrp, hrq⟩
  · rintro ⟨rfl, r, hr, hrp, hrq⟩
    exact ⟨⟨n, r⟩ₖ, kpair_mem_iff.mpr ⟨hn, hr⟩,
      (kpair_mem_taggedOrderOn_iff θ P R n r n p).mpr ⟨hn, hr, hn, hp, rfl, hrp⟩,
      (kpair_mem_taggedOrderOn_iff θ P R n r n q).mpr ⟨hn, hr, hn, hq, rfl, hrq⟩⟩

/-- The tagged decision conditions `(n, p)`, `n ∈ θ`, with `p` deciding `ň ∈ τ`. -/
noncomputable def taggedDecisionsOn (θ P R τ : V) : V :=
  sep (θ ×ˢ P) (fun z ↦ kpair.π₂ z ∈ decisionSet P R τ (kpair.π₁ z))
    (by have := decisionSet_definable_one P R τ; definability)

theorem kpair_mem_taggedDecisionsOn_iff (θ P R τ n p : V) :
    ⟨n, p⟩ₖ ∈ taggedDecisionsOn θ P R τ ↔ n ∈ θ ∧ p ∈ P ∧ p ∈ decisionSet P R τ n := by
  unfold taggedDecisionsOn
  simp only [mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

theorem antichainSliceOn_maximal {θ P R τ B : V}
    (hB : IsMaximalAntichainIn (θ ×ˢ P) (taggedOrderOn θ P R) (taggedDecisionsOn θ P R τ) B)
    {n : V} (hn : n ∈ θ) :
    IsMaximalAntichainIn P R (decisionSet P R τ n) (antichainSlice P B n) := by
  refine ⟨⟨sep_subset, ?_⟩, ?_, ?_⟩
  · intro a ha b hb hne hc
    obtain ⟨haP, haB⟩ := mem_sep_iff.mp ha
    obtain ⟨hbP, hbB⟩ := mem_sep_iff.mp hb
    have hne' : ⟨n, a⟩ₖ ≠ ⟨n, b⟩ₖ := fun h ↦ hne (kpair_iff.mp h).2
    exact hB.1.2 _ haB _ hbB hne' ((taggedCompatibleOn_iff hn haP hn hbP).mpr ⟨rfl, hc⟩)
  · intro a ha
    obtain ⟨_, haB⟩ := mem_sep_iff.mp ha
    exact ((kpair_mem_taggedDecisionsOn_iff θ P R τ n a).mp (hB.2.1 _ haB)).2.2
  · intro d hd
    have hdP : d ∈ P := by
      rcases mem_union_iff.mp hd with h | h
      · exact (mem_sep_iff.mp h).1
      · exact (mem_forcingNegation_iff _ _ _ _).mp h |>.1
    obtain ⟨z, hz, hc⟩ := hB.2.2 ⟨n, d⟩ₖ ((kpair_mem_taggedDecisionsOn_iff θ P R τ n d).mpr ⟨hn, hdP, hd⟩)
    obtain ⟨m, hm, q, hq, rfl⟩ := mem_prod_iff.mp (hB.1.1 _ hz)
    obtain ⟨rfl, hc'⟩ := (taggedCompatibleOn_iff hm hq hn hdP).mp hc
    exact ⟨q, mem_sep_iff.mpr ⟨hq, hz⟩, hc'⟩

/-- The subcollapse name of the subset: the pairs `(ň, q)`, `n ∈ θ`, with `q` in the `n`-th
slice forcing `ň ∈ τ`. -/
noncomputable def subsetSubName (θ P R τ B ξ : V) : V :=
  {z ∈ (repl (checkName ∅) (by definability) θ) ×ˢ levyCollapse ξ ;
    ∃ n ∈ θ, kpair.π₁ z = checkName ∅ n ∧ kpair.π₂ z ∈ antichainSlice P B n ∧
      ForcesCheckedMember P R ∅ τ (kpair.π₂ z) n}

theorem kpair_mem_subsetSubName_iff (θ P R τ B ξ σ q : V) :
    ⟨σ, q⟩ₖ ∈ subsetSubName θ P R τ B ξ ↔ (∃ m ∈ θ, σ = checkName ∅ m) ∧ q ∈ levyCollapse ξ ∧
      ∃ n ∈ θ, σ = checkName ∅ n ∧ q ∈ antichainSlice P B n ∧
        ForcesCheckedMember P R ∅ τ q n := by
  unfold subsetSubName
  simp only [mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, repl_spec, and_assoc]

theorem subsetSubName_isName (θ P R τ B ξ : V) :
    IsForcingName (levyCollapse ξ) (subsetSubName θ P R τ B ξ) := by
  rw [forcingName_iff]
  intro z hz
  obtain ⟨x, hx, q, hq, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨n, _, rfl⟩ := (repl_spec _).mp hx
  exact ⟨checkName ∅ n, q, hq, rfl, checkName_isName (empty_mem_levyCollapse ξ) n⟩

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- Every subset of `θ̌`, `θ < κ`, in the extension lies in some `V[G_ξ]` with `ξ < κ`. -/
theorem levy_subset_localized {θ : V} (hθ : θ ∈ κ) (x : (levyContext κ hG).Model)
    (hx : x ⊆ (levyContext κ hG).check θ) :
    ∃ ξ : V, ∃ hξ : ξ ∈ κ,
      haveI : IsOrdinal ξ := IsOrdinal.of_mem hξ
      InLevySubmodel ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG x := by
  obtain ⟨τ, rfl⟩ := (levyContext κ hG).ofName_surjective x
  have hR := (levyCollapse_poset κ).1
  have hFsub : ∀ n, memberDecisions (levyCollapse κ) (levyOrder κ) ∅ τ.val n ⊆ levyCollapse κ :=
    fun _ ↦ sep_subset
  have hdense : ∀ n, ForcingDense (levyCollapse κ) (levyOrder κ)
      (decisionSet (levyCollapse κ) (levyOrder κ) τ.val n) :=
    fun n ↦ forcing_decisions_dense hR (hFsub n)
  obtain ⟨B, hB⟩ := exists_maximalAntichain (taggedOrderOn_preorder hR)
    (sep_subset : taggedDecisionsOn θ (levyCollapse κ) (levyOrder κ) τ.val ⊆ θ ×ˢ levyCollapse κ)
    (wellOrderable_of_internalChoice hAC _)
  have hmax : ∀ n ∈ θ, IsMaximalAntichainIn (levyCollapse κ) (levyOrder κ)
      (decisionSet (levyCollapse κ) (levyOrder κ) τ.val n) (antichainSlice (levyCollapse κ) B n) :=
    fun n hn ↦ antichainSliceOn_maximal hB hn
  have hbound : ∀ n ∈ θ, ∃ ξ ∈ κ, ∀ p ∈ antichainSlice (levyCollapse κ) B n, ordinalSupport p ⊆ ξ :=
    fun n hn ↦ levyAntichain_supports_bounded hAC hU hc hω hκ (hmax n hn).1
  let bound := leastOrdinalOrZero
    (fun n β ↦ β ∈ κ ∧ ∀ p ∈ antichainSlice (levyCollapse κ) B n, ordinalSupport p ⊆ β) (by definability)
  have hboundspec : ∀ n ∈ θ, bound n ∈ κ ∧
      ∀ p ∈ antichainSlice (levyCollapse κ) B n, ordinalSupport p ⊆ bound n := by
    intro n hn
    obtain ⟨ξ, hξ, hsub⟩ := hbound n hn
    have : IsOrdinal ξ := IsOrdinal.of_mem hξ
    exact (leastOrdinalOrZero_spec
      (fun n β ↦ β ∈ κ ∧ ∀ p ∈ antichainSlice (levyCollapse κ) B n, ordinalSupport p ⊆ β)
      (by definability) n ⟨ξ, inferInstance, hξ, hsub⟩).2.1
  have hreg := measurable_regular hκ (IsOrdinal.toIsTransitive.transitive _ hω) hU hc
  have hF : ℒₛₑₜ-function₁ bound := leastOrdinalOrZero_definable _ _
  let g := definableGraph θ bound hF
  have hg : g ∈ κ ^ θ := by
    apply mem_function_of_mem_function_of_subset (definableGraph_mem_function θ _ hF)
    intro y hy
    obtain ⟨n, hn, rfl⟩ := (repl_spec hF).mp hy
    exact (hboundspec n hn).1
  obtain ⟨ξ, hξκ, hξ⟩ := regularCardinal_maps_bounded hreg hθ hg
  have hξord : IsOrdinal ξ := IsOrdinal.of_mem hξκ
  have hξsub : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξκ
  have hAξ : ∀ n ∈ θ, ∀ p ∈ antichainSlice (levyCollapse κ) B n, p ∈ levyCollapse ξ := by
    intro n hn p hp
    have hpP : p ∈ levyCollapse κ := (mem_sep_iff.mp hp).1
    have hb := hξ n hn
    rw [value_definableGraph θ _ hF hn] at hb
    have hsupp : ordinalSupport p ⊆ ξ :=
      subset_trans ((hboundspec n hn).2 p hp) (IsOrdinal.toIsTransitive.transitive _ hb)
    rw [← levyCut_eq_of_support hpP hsupp]
    exact levyCut_mem hpP
  refine ⟨ξ, hξκ, ?_⟩
  have hν := subsetSubName_isName θ (levyCollapse κ) (levyOrder κ) τ.val B ξ
  refine (inLevySubmodel_iff ξ hξsub hG _).mpr ⟨⟨_, hν⟩, ?_⟩
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨n, hn, rfl⟩ := ((levyContext κ hG).mem_check_iff θ z).mp (hx z hz)
    obtain ⟨p, hpG, hp⟩ := ((levyContext κ hG).checkedMember_truth τ n).mp hz
    obtain ⟨a, ha, haG⟩ := generic_meets_maximalAntichain hR hG (hdense n) (hmax n hn)
    have haF : a ∈ memberDecisions (levyCollapse κ) (levyOrder κ) ∅ τ.val n := by
      rcases mem_union_iff.mp ((hmax n hn).2.1 a ha) with h | h
      · exact h
      · exfalso
        obtain ⟨r, hr, hra, hrp⟩ := externalForcingFilter_compatible hG.1 haG hpG
        have hrF : r ∈ memberDecisions (levyCollapse κ) (levyOrder κ) ∅ τ.val n :=
          mem_sep_iff.mpr ⟨hr, (forcingFormula_regular hR memberFormula _).2.1 p hp r hr hrp⟩
        exact forcingNegation_disjoint hR (forcingNegation_mono hR h hr hra) hrF
    refine ((levyContext κ hG).mem_ofName_iff _ _).mpr
      ⟨⟨checkName ∅ n, checkName_isName (levyCollapse_top κ).1 n⟩, a, haG, ?_, rfl⟩
    exact (kpair_mem_subsetSubName_iff _ _ _ _ _ _ _ _).mpr
      ⟨⟨n, hn, rfl⟩, hAξ n hn a ha, n, hn, rfl, ha, (mem_sep_iff.mp haF).2⟩
  · intro hz
    obtain ⟨σ, q, hqG, hσq, rfl⟩ := ((levyContext κ hG).mem_ofName_iff _ z).mp hz
    obtain ⟨_, _, n, hn, hσ, _, hforce⟩ := (kpair_mem_subsetSubName_iff _ _ _ _ _ _ _ _).mp hσq
    have hσ' : σ = ⟨checkName ∅ n, checkName_isName (levyCollapse_top κ).1 n⟩ := Subtype.ext hσ
    rw [hσ']
    exact ((levyContext κ hG).checkedMember_truth τ n).mpr ⟨q, hqG, hforce⟩

end

end ZFVP
