import ZFVP.ModelTheory.LevyCollapseReals
import ZFVP.SetTheory.LevyCollapseSmallSets
import ZFVP.ModelTheory.ForcingModelGeneric
import ZFVP.SetTheory.WellOrderedSurjection
import ZFVP.SetTheory.Hartogs
import ZFVP.SetTheory.CountableUnions

/-! The Levy collapse at a measurable `κ` makes `κ` the first uncountable ordinal of the
extension (lem:Solovay-regularity, second paragraph): every `β < κ` is collapsed to `ω` by the
generic column, and every function from `ω` into `κ̌` is bounded because its values are decided
by antichains of size below `κ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The `n`-th slice of a tagged set. -/
noncomputable def taggedSlice (P T n : V) : V := {p ∈ P ; ⟨n, p⟩ₖ ∈ T}

theorem taggedSlice_maximal {P R T B : V} (hT : T ⊆ (ω : V) ×ˢ P)
    (hB : IsMaximalAntichainIn ((ω : V) ×ˢ P) (taggedOrder P R) T B) {n : V} (hn : n ∈ (ω : V)) :
    IsMaximalAntichainIn P R (taggedSlice P T n) (antichainSlice P B n) := by
  refine ⟨⟨sep_subset, ?_⟩, ?_, ?_⟩
  · intro a ha b hb hne hc
    obtain ⟨haP, haB⟩ := mem_sep_iff.mp ha
    obtain ⟨hbP, hbB⟩ := mem_sep_iff.mp hb
    have hne' : ⟨n, a⟩ₖ ≠ ⟨n, b⟩ₖ := fun h ↦ hne (kpair_iff.mp h).2
    exact hB.1.2 _ haB _ hbB hne' ((taggedCompatible_iff hn haP hn hbP).mpr ⟨rfl, hc⟩)
  · intro a ha
    obtain ⟨haP, haB⟩ := mem_sep_iff.mp ha
    exact mem_sep_iff.mpr ⟨haP, hB.2.1 _ haB⟩
  · intro d hd
    obtain ⟨hdP, hdT⟩ := mem_sep_iff.mp hd
    obtain ⟨z, hz, hc⟩ := hB.2.2 ⟨n, d⟩ₖ hdT
    obtain ⟨m, hm, q, hq, rfl⟩ := mem_prod_iff.mp (hB.1.1 _ hz)
    obtain ⟨rfl, hc'⟩ := (taggedCompatible_iff hm hq hn hdP).mp hc
    exact ⟨q, mem_sep_iff.mpr ⟨hq, hz⟩, hc'⟩

/-- A generic filter meets a maximal antichain of a downward closed set that it meets. -/
theorem generic_meets_maximalAntichain_of_meets {P R D A : V} {G : Set V}
    (hR : IsForcingPreorder P R) (hG : IsExternalForcingGeneric P R G)
    (hD : IsForcingDownwardClosed P R D) (hDP : D ⊆ P) (hA : IsMaximalAntichainIn P R D A)
    {p₀ : V} (hp₀ : p₀ ∈ G) (hp₀D : p₀ ∈ D) : ∃ a ∈ A, a ∈ G := by
  have hE : ForcingDense P R {q ∈ P ; (∃ a ∈ A, ⟨q, a⟩ₖ ∈ R) ∨ ∀ t ∈ D, ¬ForcingCompatible P R q t} := by
    refine ⟨sep_subset, fun p hp ↦ ?_⟩
    by_cases hc : ∃ t ∈ D, ForcingCompatible P R p t
    · obtain ⟨t, ht, r, hr, hrp, hrt⟩ := hc
      have hrD : r ∈ D := hD t ht r hr hrt
      obtain ⟨a, ha, s, hs, hsa, hsr⟩ := hA.2.2 r hrD
      exact ⟨s, mem_sep_iff.mpr ⟨hs, Or.inl ⟨a, ha, hsa⟩⟩, hR.2.2 s hs r hr p hp hsr hrp⟩
    · push Not at hc
      exact ⟨p, mem_sep_iff.mpr ⟨hp, Or.inr hc⟩, hR.2.1 p hp⟩
  obtain ⟨q, hqG, hqE⟩ := hG.2 _ hE
  obtain ⟨hqP, h | h⟩ := mem_sep_iff.mp hqE
  · obtain ⟨a, ha, hqa⟩ := h
    exact ⟨a, ha, hG.1.2.2.1 q hqG a (hA.1.1 a ha) hqa⟩
  · exact (h p₀ hp₀D (externalForcingFilter_compatible hG.1 hqG hp₀)).elim

/-- The tagged deciders `(n, p)` of the value of `σ` at `ň`. -/
noncomputable def valueDeciders (P R σ κ : V) : V :=
  {z ∈ (ω : V) ×ˢ P ; ∃ α ∈ κ, ForcesCheckedFunctionValue P R ∅ σ (kpair.π₂ z) (kpair.π₁ z) α}

theorem kpair_mem_valueDeciders_iff (P R σ κ n p : V) :
    ⟨n, p⟩ₖ ∈ valueDeciders P R σ κ ↔ n ∈ (ω : V) ∧ p ∈ P ∧
      ∃ α ∈ κ, ForcesCheckedFunctionValue P R ∅ σ p n α := by
  unfold valueDeciders
  simp only [mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

/-- The values decided by the `n`-th slice of a tagged antichain. -/
noncomputable def decidedValues (P R σ κ B n : V) : V :=
  {α ∈ κ ; ∃ a ∈ antichainSlice P B n, ForcesCheckedFunctionValue P R ∅ σ a n α}

theorem decidedValues_definable_one (P R σ κ B : V) : ℒₛₑₜ-function₁[V] (decidedValues P R σ κ B) := by
  have hd : ℒₛₑₜ-relation[V] (fun S n ↦ ∀ α, α ∈ S ↔ α ∈ κ ∧
    ∃ a ∈ antichainSlice P B n, ForcesCheckedFunctionValue P R ∅ σ a n α) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = decidedValues P R σ κ B (v 1) ↔ _
  rw [mem_ext_iff]
  exact ⟨fun h α ↦ (h α).trans (show α ∈ decidedValues P R σ κ B (v 1) ↔ _ from mem_sep_iff),
    fun h α ↦ (h α).trans (show α ∈ decidedValues P R σ κ B (v 1) ↔ _ from mem_sep_iff).symm⟩

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

include hAC hU hc hω hκ in
/-- Antichains of the Levy collapse have size below `κ`. -/
theorem levyAntichain_small {A : V} (hA : IsForcingAntichain (levyCollapse κ) (levyOrder κ) A) :
    ∃ μ ∈ κ, A ≤# μ := by
  have hwo := wellOrderable_of_internalChoice hAC A
  have hμeq := wellOrderedCardinal_cardEQ hwo
  have hμ := wellOrderedCardinal_initial hwo
  have := hμ.1
  refine ⟨wellOrderedCardinal A, ?_, hμeq.ge⟩
  rcases IsOrdinal.mem_trichotomy (α := wellOrderedCardinal A) (β := κ) with h | h | h
  · exact h
  · exact (levyAntichain_not_cardLE hAC hU hc hω hκ hA (h ▸ hμeq.le)).elim
  · exact (levyAntichain_not_cardLE hAC hU hc hω hκ hA
      ((cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ h)).trans hμeq.le)).elim

variable {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- Every ordinal below `κ` is countable in the extension. -/
theorem levy_check_countable {β : V} (hβ : β ∈ κ) :
    IsInternallyCountable ((levyContext κ hG).check β) := by
  let A := levyContext κ hG
  have hβord : IsOrdinal β := IsOrdinal.of_mem hβ
  by_cases h0 : (∅ : V) ∈ β
  swap
  · have hβe : β = ∅ := by
      ext z
      constructor
      · intro hz
        exact (h0 (IsOrdinal.empty_mem_iff_nonempty.mpr ⟨⟨z, hz⟩⟩)).elim
      · intro hz
        exact (not_mem_empty hz).elim
    rw [hβe, A.check_empty]
    exact cardLE_empty _
  have hωc : A.check ω = (ω : A.Model) := A.checkEmbedding.map_omega
  let g : A.Model := {z ∈ (ω : A.Model) ×ˢ A.check β ;
    ∃ p ∈ A.genericSet, ⟨⟨kpair.π₁ z, A.check β⟩ₖ, kpair.π₂ z⟩ₖ ∈ p}
  have hmem : ∀ n γ : V, n ∈ (ω : V) → γ ∈ β →
      (⟨A.check n, A.check γ⟩ₖ ∈ g ↔ ∃ p ∈ G, ⟨⟨n, β⟩ₖ, γ⟩ₖ ∈ p) := by
    intro n γ hn hγ
    have hnω : A.check n ∈ (ω : A.Model) := by rw [← hωc]; exact (A.check_mem_iff n ω).mpr hn
    have hγβ : A.check γ ∈ A.check β := (A.check_mem_iff γ β).mpr hγ
    constructor
    · intro h
      obtain ⟨_, p', hp', hmem⟩ := mem_sep_iff.mp h
      obtain ⟨p, hp, rfl⟩ := (A.mem_genericSet_iff p').mp hp'
      refine ⟨p, hp, ?_⟩
      simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hmem
      rw [← A.check_kpair, ← A.check_kpair, A.check_mem_iff] at hmem
      exact hmem
    · rintro ⟨p, hp, hmem⟩
      refine mem_sep_iff.mpr ⟨kpair_mem_iff.mpr ⟨hnω, hγβ⟩, A.check p,
        (A.mem_genericSet_iff _).mpr ⟨p, hp, rfl⟩, ?_⟩
      simp only [kpair.π₁_kpair, kpair.π₂_kpair]
      rw [← A.check_kpair, ← A.check_kpair, A.check_mem_iff]
      exact hmem
  have hgfun : g ∈ A.check β ^ (ω : A.Model) := by
    apply mem_function.intro
    · intro z hz
      exact (mem_sep_iff.mp hz).1
    · intro x hx
      rw [← hωc] at hx
      obtain ⟨n, hn, rfl⟩ := (A.mem_check_iff ω x).mp hx
      obtain ⟨p, hpG, hpD⟩ := hG.2 _ (levyColumn_total_dense hβ h0 hn)
      obtain ⟨_, γ, hγp⟩ := mem_sep_iff.mp hpD
      have hγβ : γ ∈ β := levyCollapse_value (hG.1.1 p hpG) hγp
      refine ⟨A.check γ, (hmem n γ hn hγβ).mpr ⟨p, hpG, hγp⟩, ?_⟩
      intro y hy
      have hyβ : y ∈ A.check β := (kpair_mem_iff.mp ((mem_sep_iff.mp hy).1)).2
      obtain ⟨γ', hγ', rfl⟩ := (A.mem_check_iff β y).mp hyβ
      obtain ⟨q, hqG, hq⟩ := (hmem n γ' hn hγ').mp hy
      obtain ⟨r, hrG, hrp, hrq⟩ := hG.1.2.2.2 p hpG q hqG
      have hr := hG.1.1 r hrG
      have hrfun : IsFunction r :=
        ((mem_finitePartialFunctions _ _ r).mp (levyCollapse_finitePartialFunction hr)).2.1
      have h1 : ⟨⟨n, β⟩ₖ, γ⟩ₖ ∈ r := ((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2 _ hγp
      have h2 : ⟨⟨n, β⟩ₖ, γ'⟩ₖ ∈ r := ((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2 _ hq
      rw [IsFunction.unique (hf := hrfun) h2 h1]
  have hrange : range g = A.check β := by
    apply SetTheory.subset_antisymm (range_subset_of_mem_function hgfun)
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := (A.mem_check_iff β y).mp hy
    obtain ⟨p, hpG, hpD⟩ := hG.2 _ (levyColumn_value_dense hβ hγ)
    obtain ⟨_, n, hn, hnp⟩ := mem_sep_iff.mp hpD
    exact mem_range_of_kpair_mem ((hmem n γ hn hγ).mpr ⟨p, hpG, hnp⟩)
  exact cardLE_of_surjective_function (ordinal_wellOrderable (ω : A.Model)) hgfun hrange

include hAC hU hc hω hκ in
/-- Functions from `ω` into `κ̌` in the extension are bounded below `κ̌`. -/
theorem levy_function_bounded (h : (levyContext κ hG).Model)
    (hh : h ∈ (levyContext κ hG).check κ ^ (ω : (levyContext κ hG).Model)) :
    ∃ ξ ∈ κ, ∀ x ∈ (ω : (levyContext κ hG).Model), h ‘ x ∈ (levyContext κ hG).check ξ := by
  let A := levyContext κ hG
  obtain ⟨σ, rfl⟩ := A.ofName_surjective h
  have hR := (levyCollapse_poset κ).1
  have hωc : A.check ω = (ω : A.Model) := A.checkEmbedding.map_omega
  have hreg := measurable_regular hκ (IsOrdinal.toIsTransitive.transitive _ hω) hU hc
  have hσfun := IsFunction.of_mem hh
  -- the deciders of the value at `n`
  set T : V := valueDeciders (levyCollapse κ) (levyOrder κ) σ.val κ with hTdef
  have hTsub : T ⊆ (ω : V) ×ˢ levyCollapse κ := sep_subset
  have hmemT : ∀ n p, ⟨n, p⟩ₖ ∈ T ↔ n ∈ (ω : V) ∧ p ∈ levyCollapse κ ∧
      ∃ α ∈ κ, ForcesCheckedFunctionValue (levyCollapse κ) (levyOrder κ) ∅ σ.val p n α :=
    fun n p ↦ kpair_mem_valueDeciders_iff _ _ _ _ n p
  obtain ⟨B, hB⟩ := exists_maximalAntichain (taggedOrder_preorder hR) hTsub
    (wellOrderable_of_internalChoice hAC _)
  have hslice : ∀ n ∈ (ω : V), IsMaximalAntichainIn (levyCollapse κ) (levyOrder κ)
      (taggedSlice (levyCollapse κ) T n) (antichainSlice (levyCollapse κ) B n) :=
    fun n hn ↦ taggedSlice_maximal hTsub hB hn
  have hdown : ∀ n, IsForcingDownwardClosed (levyCollapse κ) (levyOrder κ)
      (taggedSlice (levyCollapse κ) T n) := by
    intro n p hp q hq hqp
    obtain ⟨hpP, hpT⟩ := mem_sep_iff.mp hp
    obtain ⟨hn, _, α, hα, hforce⟩ := (hmemT n p).mp hpT
    refine mem_sep_iff.mpr ⟨hq, (hmemT n q).mpr ⟨hn, hq, α, hα, ?_⟩⟩
    exact (forcingFormula_regular hR functionValueFormula _).2.1 p hforce q hq hqp
  -- the decided values at `n`
  set S : V → V := decidedValues (levyCollapse κ) (levyOrder κ) σ.val κ B with hSdef
  have hmemS : ∀ n α, α ∈ S n ↔ α ∈ κ ∧ ∃ a ∈ antichainSlice (levyCollapse κ) B n,
      ForcesCheckedFunctionValue (levyCollapse κ) (levyOrder κ) ∅ σ.val a n α := fun n α ↦ mem_sep_iff
  have hSsmall : ∀ n ∈ (ω : V), ∃ ξ ∈ κ, S n ⊆ ξ := by
    intro n hn
    obtain ⟨μ, hμ, hAμ⟩ := levyAntichain_small hAC hU hc hω hκ (hslice n hn).1
    -- the value map on the antichain
    let f : V := {z ∈ antichainSlice (levyCollapse κ) B n ×ˢ κ ;
      ForcesCheckedFunctionValue (levyCollapse κ) (levyOrder κ) ∅ σ.val (kpair.π₁ z) n (kpair.π₂ z)}
    have hmemf : ∀ a α, ⟨a, α⟩ₖ ∈ f ↔ a ∈ antichainSlice (levyCollapse κ) B n ∧ α ∈ κ ∧
        ForcesCheckedFunctionValue (levyCollapse κ) (levyOrder κ) ∅ σ.val a n α := by
      intro a α
      simp only [f, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]
    have hffun : f ∈ S n ^ antichainSlice (levyCollapse κ) B n := by
      apply mem_function.intro
      · intro z hz
        obtain ⟨a, ha, α, hα, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
        obtain ⟨_, _, hforce⟩ := (hmemf a α).mp hz
        exact kpair_mem_iff.mpr ⟨ha, (hmemS n α).mpr ⟨hα, a, ha, hforce⟩⟩
      · intro a ha
        have haT := (hslice n hn).2.1 a ha
        obtain ⟨_, _, α, hα, hforce⟩ := (hmemT n a).mp (mem_sep_iff.mp haT).2
        refine ⟨α, (hmemf a α).mpr ⟨ha, hα, hforce⟩, fun α' hα' ↦ ?_⟩
        obtain ⟨_, _, hforce'⟩ := (hmemf a α').mp hα'
        exact forcesCheckedFunctionValue_unique hR (levyCollapse_top κ) σ.property hforce' hforce
    have hrange : range f = S n := by
      apply SetTheory.subset_antisymm (range_subset_of_mem_function hffun)
      intro α hα
      obtain ⟨hακ, a, ha, hforce⟩ := (hmemS n α).mp hα
      exact mem_range_of_kpair_mem ((hmemf a α).mpr ⟨ha, hακ, hforce⟩)
    have hle : S n ≤# μ :=
      (cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC _) hffun hrange).trans hAμ
    exact regular_small_subset_bounded hreg (fun α hα ↦ ((hmemS n α).mp hα).1) hμ hle
  -- a uniform bound
  have hSdefin := decidedValues_definable_one (levyCollapse κ) (levyOrder κ) σ.val κ B
  let bound := leastOrdinalOrZero (fun n β ↦ β ∈ κ ∧ S n ⊆ β) (by rw [hSdef]; definability)
  have hboundspec : ∀ n ∈ (ω : V), bound n ∈ κ ∧ S n ⊆ bound n := by
    intro n hn
    obtain ⟨ξ, hξ, hsub⟩ := hSsmall n hn
    have : IsOrdinal ξ := IsOrdinal.of_mem hξ
    exact (leastOrdinalOrZero_spec (fun n β ↦ β ∈ κ ∧ S n ⊆ β) (by rw [hSdef]; definability) n
      ⟨ξ, inferInstance, hξ, hsub⟩).2.1
  have hF : ℒₛₑₜ-function₁ bound := leastOrdinalOrZero_definable _ _
  let gr := definableGraph ω bound hF
  have hgr : gr ∈ κ ^ (ω : V) := by
    apply mem_function_of_mem_function_of_subset (definableGraph_mem_function ω _ hF)
    intro y hy
    obtain ⟨n, hn, rfl⟩ := (repl_spec hF).mp hy
    exact (hboundspec n hn).1
  obtain ⟨ξ, hξκ, hξ⟩ := regularCardinal_maps_bounded hreg hω hgr
  have hξord : IsOrdinal ξ := IsOrdinal.of_mem hξκ
  refine ⟨ξ, hξκ, fun x hx ↦ ?_⟩
  rw [← hωc] at hx
  obtain ⟨n, hn, rfl⟩ := (A.mem_check_iff ω x).mp hx
  -- the actual value
  have hval : (A.ofName σ) ‘ (A.check n) ∈ A.check κ := function_value_mem hh (by rw [← hωc]; exact (A.check_mem_iff n ω).mpr hn)
  obtain ⟨α, hα, hαv⟩ := (A.mem_check_iff κ _).mp hval
  obtain ⟨p, hpG, hforce⟩ := (A.checkedFunctionValue_truth σ n α).mpr ⟨hσfun, hαv⟩
  have hpT : p ∈ taggedSlice (levyCollapse κ) T n :=
    mem_sep_iff.mpr ⟨hG.1.1 p hpG, (hmemT n p).mpr ⟨hn, hG.1.1 p hpG, α, hα, hforce⟩⟩
  obtain ⟨a, ha, haG⟩ := generic_meets_maximalAntichain_of_meets hR hG (hdown n) sep_subset
    (hslice n hn) hpG hpT
  obtain ⟨_, _, α', hα', hforce'⟩ := (hmemT n a).mp (mem_sep_iff.mp ((hslice n hn).2.1 a ha)).2
  obtain ⟨r, hrG, hra, hrp⟩ := hG.1.2.2.2 a haG p hpG
  have hr := hG.1.1 r hrG
  have hreg' := forcingFormula_regular hR functionValueFormula
  have h1 := hreg' _ |>.2.1 a hforce' r hr hra
  have h2 := hreg' _ |>.2.1 p hforce r hr hrp
  have hαα' : α' = α := forcesCheckedFunctionValue_unique hR (levyCollapse_top κ) σ.property h1 h2
  have hαS : α ∈ S n := (hmemS n α).mpr ⟨hα, a, ha, hαα' ▸ hforce'⟩
  have hb := hξ n hn
  rw [value_definableGraph ω _ hF hn] at hb
  rw [hαv]
  exact (A.check_mem_iff α ξ).mpr (IsOrdinal.toIsTransitive.transitive _ hb _ ((hboundspec n hn).2 _ hαS))

include hAC hU hc hω hκ in
/-- `κ̌` is the first uncountable ordinal of the extension. -/
theorem levy_check_hartogs : hartogsNumber (ω : (levyContext κ hG).Model) = (levyContext κ hG).check κ := by
  let A := levyContext κ hG
  have hκord : IsOrdinal (A.check κ) := (A.check_ordinal_iff κ).mpr inferInstance
  rw [hartogsNumber_eq_iff]
  refine ⟨hκord, ?_, ?_⟩
  · rintro ⟨e, he, hinj⟩
    have := IsFunction.of_mem he
    have hde : domain e = A.check κ := domain_eq_of_mem_function he
    have hempty0 : (∅ : A.Model) ∈ A.check κ := by
      rw [← A.check_empty]
      exact (A.check_mem_iff ∅ κ).mpr (IsOrdinal.toIsTransitive.mem_trans empty_mem_ω hω)
    -- the inverse map, extended by `∅`
    let h : A.Model := {z ∈ (ω : A.Model) ×ˢ A.check κ ;
      ⟨kpair.π₂ z, kpair.π₁ z⟩ₖ ∈ e ∨ (kpair.π₁ z ∉ range e ∧ kpair.π₂ z = ∅)}
    have hmemh : ∀ y x, ⟨y, x⟩ₖ ∈ h ↔ y ∈ (ω : A.Model) ∧ x ∈ A.check κ ∧
        (⟨x, y⟩ₖ ∈ e ∨ (y ∉ range e ∧ x = ∅)) := by
      intro y x
      simp only [h, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]
    have hhfun : h ∈ A.check κ ^ (ω : A.Model) := by
      apply mem_function.intro
      · intro z hz
        exact (mem_sep_iff.mp hz).1
      · intro y hy
        by_cases hyr : y ∈ range e
        · obtain ⟨x, hxy⟩ := mem_range_iff.mp hyr
          have hx : x ∈ A.check κ := hde ▸ mem_domain_of_kpair_mem hxy
          refine ⟨x, (hmemh y x).mpr ⟨hy, hx, Or.inl hxy⟩, fun x' hx' ↦ ?_⟩
          obtain ⟨_, _, hx'e | ⟨hnr, _⟩⟩ := (hmemh y x').mp hx'
          · exact hinj x' x y hx'e hxy
          · exact (hnr hyr).elim
        · refine ⟨∅, (hmemh y ∅).mpr ⟨hy, hempty0, Or.inr ⟨hyr, rfl⟩⟩, fun x' hx' ↦ ?_⟩
          obtain ⟨_, _, hx'e | ⟨_, hx'⟩⟩ := (hmemh y x').mp hx'
          · exact (hyr (mem_range_of_kpair_mem hx'e)).elim
          · exact hx'
    obtain ⟨ξ, hξκ, hbound⟩ := levy_function_bounded hAC hU hc hω hκ hG h hhfun
    have hξ : A.check ξ ∈ A.check κ := (A.check_mem_iff ξ κ).mpr hξκ
    have hyξ : e ‘ (A.check ξ) ∈ (ω : A.Model) := function_value_mem he hξ
    have hpair : ⟨A.check ξ, e ‘ (A.check ξ)⟩ₖ ∈ e := kpair_value_mem (by rw [hde]; exact hξ)
    have := IsFunction.of_mem hhfun
    have hhval : h ‘ (e ‘ (A.check ξ)) = A.check ξ :=
      value_eq_of_kpair_mem ((hmemh _ _).mpr ⟨hyξ, hξ, Or.inl hpair⟩)
    have := hbound _ hyξ
    rw [hhval] at this
    exact mem_irrefl _ this
  · intro β hβ hnot
    by_contra hsub
    have : IsOrdinal β := hβ
    rcases IsOrdinal.subset_or_supset (α := A.check κ) (β := β) with h | h
    · exact hsub h
    · rcases IsOrdinal.subset_iff.mp h with h' | h'
      · exact hsub (h' ▸ subset_refl _)
      · obtain ⟨β₀, hβ₀, rfl⟩ := (A.mem_check_iff κ β).mp h'
        exact hnot (levy_check_countable hG hβ₀)

end

end ZFVP
