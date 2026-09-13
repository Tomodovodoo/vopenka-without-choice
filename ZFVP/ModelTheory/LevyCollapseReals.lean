import ZFVP.ModelTheory.LevyCollapseSubmodel
import ZFVP.ModelTheory.ForcingSmallUltrafilter
import ZFVP.ModelTheory.GenericRegularForcing
import ZFVP.SetTheory.LevyCollapseAntichainSupport

/-! Every real of the Levy collapse extension lies in a bounded stage `V[G_β]`
(lem:Solovay-localization, the real-parameter step): the decisions about `ň ∈ τ` for all `n`
at once carry a maximal antichain of the tagged poset `ω × P`, whose slices are maximal
antichains of size below `κ` with supports bounded below `κ` uniformly in `n`; by regularity
one bound works for all `n`, and the slices determine a name for the subcollapse below it. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A generic filter meets every maximal antichain of a dense set. -/
theorem generic_meets_maximalAntichain {P R D A : V} {G : Set V} (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (hD : ForcingDense P R D)
    (hA : IsMaximalAntichainIn P R D A) : ∃ a ∈ A, a ∈ G := by
  have hE : ForcingDense P R {q ∈ P ; ∃ a ∈ A, ⟨q, a⟩ₖ ∈ R} := by
    refine ⟨sep_subset, fun p hp ↦ ?_⟩
    obtain ⟨d, hd, hdp⟩ := hD.2 p hp
    obtain ⟨a, ha, r, hr, hra, hrd⟩ := hA.2.2 d hd
    exact ⟨r, mem_sep_iff.mpr ⟨hr, a, ha, hra⟩, hR.2.2 r hr d (hD.1 d hd) p hp hrd hdp⟩
  obtain ⟨q, hqG, hqE⟩ := hG.2 _ hE
  obtain ⟨_, a, ha, hqa⟩ := mem_sep_iff.mp hqE
  exact ⟨a, ha, hG.1.2.2.1 q hqG a (hA.1.1 a ha) hqa⟩

/-- The disjoint union of `ω` copies of a forcing preorder. -/
noncomputable def taggedOrder (P R : V) : V :=
  {z ∈ ((ω : V) ×ˢ P) ×ˢ ((ω : V) ×ˢ P) ;
    kpair.π₁ (kpair.π₁ z) = kpair.π₁ (kpair.π₂ z) ∧
      ⟨kpair.π₂ (kpair.π₁ z), kpair.π₂ (kpair.π₂ z)⟩ₖ ∈ R}

theorem kpair_mem_taggedOrder_iff (P R n p m q : V) :
    ⟨⟨n, p⟩ₖ, ⟨m, q⟩ₖ⟩ₖ ∈ taggedOrder P R ↔
      n ∈ (ω : V) ∧ p ∈ P ∧ m ∈ (ω : V) ∧ q ∈ P ∧ n = m ∧ ⟨p, q⟩ₖ ∈ R := by
  unfold taggedOrder
  simp only [mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

theorem taggedOrder_preorder {P R : V} (hR : IsForcingPreorder P R) :
    IsForcingPreorder ((ω : V) ×ˢ P) (taggedOrder P R) := by
  refine ⟨sep_subset, ?_, ?_⟩
  · intro z hz
    obtain ⟨n, hn, p, hp, rfl⟩ := mem_prod_iff.mp hz
    exact (kpair_mem_taggedOrder_iff P R n p n p).mpr ⟨hn, hp, hn, hp, rfl, hR.2.1 p hp⟩
  · intro z hz z' hz' z'' hz'' h1 h2
    obtain ⟨n, hn, p, hp, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨m, hm, q, hq, rfl⟩ := mem_prod_iff.mp hz'
    obtain ⟨k, hk, r, hr, rfl⟩ := mem_prod_iff.mp hz''
    obtain ⟨_, _, _, _, hnm, hpq⟩ := (kpair_mem_taggedOrder_iff P R n p m q).mp h1
    obtain ⟨_, _, _, _, hmk, hqr⟩ := (kpair_mem_taggedOrder_iff P R m q k r).mp h2
    exact (kpair_mem_taggedOrder_iff P R n p k r).mpr
      ⟨hn, hp, hk, hr, hnm.trans hmk, hR.2.2 p hp q hq r hr hpq hqr⟩

theorem taggedCompatible_iff {P R n p m q : V} (hn : n ∈ (ω : V)) (hp : p ∈ P) (hm : m ∈ (ω : V))
    (hq : q ∈ P) :
    ForcingCompatible ((ω : V) ×ˢ P) (taggedOrder P R) ⟨n, p⟩ₖ ⟨m, q⟩ₖ ↔
      n = m ∧ ForcingCompatible P R p q := by
  constructor
  · rintro ⟨z, hz, h1, h2⟩
    obtain ⟨k, hk, r, hr, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨_, _, _, _, hkn, hrp⟩ := (kpair_mem_taggedOrder_iff P R k r n p).mp h1
    obtain ⟨_, _, _, _, hkm, hrq⟩ := (kpair_mem_taggedOrder_iff P R k r m q).mp h2
    exact ⟨hkn.symm.trans hkm, r, hr, hrp, hrq⟩
  · rintro ⟨rfl, r, hr, hrp, hrq⟩
    exact ⟨⟨n, r⟩ₖ, kpair_mem_iff.mpr ⟨hn, hr⟩,
      (kpair_mem_taggedOrder_iff P R n r n p).mpr ⟨hn, hr, hn, hp, rfl, hrp⟩,
      (kpair_mem_taggedOrder_iff P R n r n q).mpr ⟨hn, hr, hn, hq, rfl, hrq⟩⟩

/-- The conditions deciding `ň ∈ τ`. -/
noncomputable def decisionSet (P R τ n : V) : V :=
  memberDecisions P R ∅ τ n ∪ forcingNegation P R (memberDecisions P R ∅ τ n)

instance decisionSet_definable_one (P R τ : V) : ℒₛₑₜ-function₁[V] (decisionSet P R τ) := by
  have h := memberDecisions_definable_one P R ∅ τ
  unfold decisionSet
  definability

/-- The tagged decision conditions `(n, p)` with `p` deciding `ň ∈ τ`. -/
noncomputable def taggedDecisions (P R τ : V) : V :=
  sep ((ω : V) ×ˢ P) (fun z ↦ kpair.π₂ z ∈ decisionSet P R τ (kpair.π₁ z))
    (by have := decisionSet_definable_one P R τ; definability)

theorem kpair_mem_taggedDecisions_iff (P R τ n p : V) :
    ⟨n, p⟩ₖ ∈ taggedDecisions P R τ ↔ n ∈ (ω : V) ∧ p ∈ P ∧ p ∈ decisionSet P R τ n := by
  unfold taggedDecisions
  simp only [mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

/-- The `n`-th slice of a tagged antichain. -/
noncomputable def antichainSlice (P B n : V) : V := {p ∈ P ; ⟨n, p⟩ₖ ∈ B}

instance antichainSlice_definable : ℒₛₑₜ-function₃[V] antichainSlice := by
  have hd : ℒₛₑₜ-relation₄[V] (fun S P B n ↦ ∀ p, p ∈ S ↔ p ∈ P ∧ ⟨n, p⟩ₖ ∈ B) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = antichainSlice (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  exact ⟨fun h p ↦ (h p).trans (show p ∈ antichainSlice (v 1) (v 2) (v 3) ↔ _ from mem_sep_iff),
    fun h p ↦ (h p).trans (show p ∈ antichainSlice (v 1) (v 2) (v 3) ↔ _ from mem_sep_iff).symm⟩

theorem antichainSlice_maximal {P R τ B : V}
    (hB : IsMaximalAntichainIn ((ω : V) ×ˢ P) (taggedOrder P R) (taggedDecisions P R τ) B)
    {n : V} (hn : n ∈ (ω : V)) :
    IsMaximalAntichainIn P R (decisionSet P R τ n) (antichainSlice P B n) := by
  refine ⟨⟨sep_subset, ?_⟩, ?_, ?_⟩
  · intro a ha b hb hne hc
    obtain ⟨haP, haB⟩ := mem_sep_iff.mp ha
    obtain ⟨hbP, hbB⟩ := mem_sep_iff.mp hb
    have hne' : ⟨n, a⟩ₖ ≠ ⟨n, b⟩ₖ := fun h ↦ hne (kpair_iff.mp h).2
    exact hB.1.2 _ haB _ hbB hne' ((taggedCompatible_iff hn haP hn hbP).mpr ⟨rfl, hc⟩)
  · intro a ha
    obtain ⟨_, haB⟩ := mem_sep_iff.mp ha
    exact ((kpair_mem_taggedDecisions_iff P R τ n a).mp (hB.2.1 _ haB)).2.2
  · intro d hd
    have hdP : d ∈ P := by
      rcases mem_union_iff.mp hd with h | h
      · exact (mem_sep_iff.mp h).1
      · exact (mem_forcingNegation_iff _ _ _ _).mp h |>.1
    obtain ⟨z, hz, hc⟩ := hB.2.2 ⟨n, d⟩ₖ ((kpair_mem_taggedDecisions_iff P R τ n d).mpr ⟨hn, hdP, hd⟩)
    obtain ⟨m, hm, q, hq, rfl⟩ := mem_prod_iff.mp (hB.1.1 _ hz)
    obtain ⟨rfl, hc'⟩ := (taggedCompatible_iff hm hq hn hdP).mp hc
    exact ⟨q, mem_sep_iff.mpr ⟨hq, hz⟩, hc'⟩

/-- The subcollapse name of the real: the pairs `(ň, q)` with `q` in the `n`-th slice
forcing `ň ∈ τ`. -/
noncomputable def realSubName (P R τ B ξ : V) : V :=
  {z ∈ (repl (checkName ∅) (by definability) (ω : V)) ×ˢ levyCollapse ξ ;
    ∃ n ∈ (ω : V), kpair.π₁ z = checkName ∅ n ∧ kpair.π₂ z ∈ antichainSlice P B n ∧
      ForcesCheckedMember P R ∅ τ (kpair.π₂ z) n}

theorem kpair_mem_realSubName_iff (P R τ B ξ σ q : V) :
    ⟨σ, q⟩ₖ ∈ realSubName P R τ B ξ ↔ (∃ m ∈ (ω : V), σ = checkName ∅ m) ∧ q ∈ levyCollapse ξ ∧
      ∃ n ∈ (ω : V), σ = checkName ∅ n ∧ q ∈ antichainSlice P B n ∧
        ForcesCheckedMember P R ∅ τ q n := by
  unfold realSubName
  simp only [mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, repl_spec, and_assoc]

theorem realSubName_isName (P R τ B ξ : V) :
    IsForcingName (levyCollapse ξ) (realSubName P R τ B ξ) := by
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
/-- Every real of the extension lies in some `V[G_ξ]` with `ξ < κ`. -/
theorem levy_real_localized (x : (levyContext κ hG).Model)
    (hx : x ⊆ (levyContext κ hG).check (ω : V)) :
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
  obtain ⟨B, hB⟩ := exists_maximalAntichain (taggedOrder_preorder hR)
    (sep_subset : taggedDecisions (levyCollapse κ) (levyOrder κ) τ.val ⊆ (ω : V) ×ˢ levyCollapse κ)
    (wellOrderable_of_internalChoice hAC _)
  have hmax : ∀ n ∈ (ω : V), IsMaximalAntichainIn (levyCollapse κ) (levyOrder κ)
      (decisionSet (levyCollapse κ) (levyOrder κ) τ.val n) (antichainSlice (levyCollapse κ) B n) :=
    fun n hn ↦ antichainSlice_maximal hB hn
  have hbound : ∀ n ∈ (ω : V), ∃ ξ ∈ κ, ∀ p ∈ antichainSlice (levyCollapse κ) B n, ordinalSupport p ⊆ ξ :=
    fun n hn ↦ levyAntichain_supports_bounded hAC hU hc hω hκ (hmax n hn).1
  let bound := leastOrdinalOrZero
    (fun n β ↦ β ∈ κ ∧ ∀ p ∈ antichainSlice (levyCollapse κ) B n, ordinalSupport p ⊆ β) (by definability)
  have hboundspec : ∀ n ∈ (ω : V), bound n ∈ κ ∧
      ∀ p ∈ antichainSlice (levyCollapse κ) B n, ordinalSupport p ⊆ bound n := by
    intro n hn
    obtain ⟨ξ, hξ, hsub⟩ := hbound n hn
    have : IsOrdinal ξ := IsOrdinal.of_mem hξ
    exact (leastOrdinalOrZero_spec
      (fun n β ↦ β ∈ κ ∧ ∀ p ∈ antichainSlice (levyCollapse κ) B n, ordinalSupport p ⊆ β)
      (by definability) n ⟨ξ, inferInstance, hξ, hsub⟩).2.1
  have hreg := measurable_regular hκ (IsOrdinal.toIsTransitive.transitive _ hω) hU hc
  have hF : ℒₛₑₜ-function₁ bound := leastOrdinalOrZero_definable _ _
  let g := definableGraph ω bound hF
  have hg : g ∈ κ ^ (ω : V) := by
    apply mem_function_of_mem_function_of_subset (definableGraph_mem_function ω _ hF)
    intro y hy
    obtain ⟨n, hn, rfl⟩ := (repl_spec hF).mp hy
    exact (hboundspec n hn).1
  obtain ⟨ξ, hξκ, hξ⟩ := regularCardinal_maps_bounded hreg hω hg
  have hξord : IsOrdinal ξ := IsOrdinal.of_mem hξκ
  have hξsub : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξκ
  have hAξ : ∀ n ∈ (ω : V), ∀ p ∈ antichainSlice (levyCollapse κ) B n, p ∈ levyCollapse ξ := by
    intro n hn p hp
    have hpP : p ∈ levyCollapse κ := (mem_sep_iff.mp hp).1
    have hb := hξ n hn
    rw [value_definableGraph ω _ hF hn] at hb
    have hsupp : ordinalSupport p ⊆ ξ :=
      subset_trans ((hboundspec n hn).2 p hp) (IsOrdinal.toIsTransitive.transitive _ hb)
    rw [← levyCut_eq_of_support hpP hsupp]
    exact levyCut_mem hpP
  refine ⟨ξ, hξκ, ?_⟩
  have hν := realSubName_isName (levyCollapse κ) (levyOrder κ) τ.val B ξ
  refine (inLevySubmodel_iff ξ hξsub hG _).mpr ⟨⟨_, hν⟩, ?_⟩
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨n, hn, rfl⟩ := ((levyContext κ hG).mem_check_iff ω z).mp (hx z hz)
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
    exact (kpair_mem_realSubName_iff _ _ _ _ _ _ _).mpr
      ⟨⟨n, hn, rfl⟩, hAξ n hn a ha, n, hn, rfl, ha, (mem_sep_iff.mp haF).2⟩
  · intro hz
    obtain ⟨σ, q, hqG, hσq, rfl⟩ := ((levyContext κ hG).mem_ofName_iff _ z).mp hz
    obtain ⟨_, _, n, hn, hσ, _, hforce⟩ := (kpair_mem_realSubName_iff _ _ _ _ _ _ _).mp hσq
    have hσ' : σ = ⟨checkName ∅ n, checkName_isName (levyCollapse_top κ).1 n⟩ := Subtype.ext hσ
    rw [hσ']
    exact ((levyContext κ hG).checkedMember_truth τ n).mpr ⟨q, hqG, hforce⟩

end

end ZFVP
