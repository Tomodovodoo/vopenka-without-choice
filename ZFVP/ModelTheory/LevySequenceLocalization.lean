import ZFVP.ModelTheory.LevyRangeCover
import ZFVP.ModelTheory.SolovayLocalization

/-! Countable sequences of the Levy extension lie in a bounded stage: a function from `ω̌` into a
checked set `θ̌` in `V[G]` is decided value by value on the slices of one maximal antichain of
tagged deciders, each slice is an antichain of the collapse and so has supports bounded below
`κ`, and `κ` is regular, so all the slices live in `Col(ω, <ξ)` for a single `ξ < κ`. The pairs
of a check of an argument-value pair with a deciding condition of the slice then form a name for
the subcollapse below `ξ`, whose value is the function, so the function lies in `V[G_ξ]`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The subcollapse name of a function from `ω̌` to `θ̌`: the pairs `(⟨n, α⟩ˇ, q)` with `q` in the
`n`-th slice of the antichain `B` forcing the value of `σ` at `ň` to be `α̌`. -/
noncomputable def sequenceSubName (θ P R σ B ξ : V) : V :=
  {z ∈ (repl (checkName ∅) (by definability) ((ω : V) ×ˢ θ)) ×ˢ levyCollapse ξ ;
    ∃ n ∈ (ω : V), ∃ α ∈ θ, kpair.π₁ z = checkName ∅ ⟨n, α⟩ₖ ∧
      kpair.π₂ z ∈ antichainSlice P B n ∧
      ForcesCheckedFunctionValue P R ∅ σ (kpair.π₂ z) n α}

theorem kpair_mem_sequenceSubName_iff (θ P R σ B ξ ν q : V) :
    ⟨ν, q⟩ₖ ∈ sequenceSubName θ P R σ B ξ ↔
      (∃ w ∈ (ω : V) ×ˢ θ, ν = checkName ∅ w) ∧ q ∈ levyCollapse ξ ∧
        ∃ n ∈ (ω : V), ∃ α ∈ θ, ν = checkName ∅ ⟨n, α⟩ₖ ∧ q ∈ antichainSlice P B n ∧
          ForcesCheckedFunctionValue P R ∅ σ q n α := by
  unfold sequenceSubName
  simp only [mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, repl_spec, and_assoc]

theorem sequenceSubName_isName (θ P R σ B ξ : V) :
    IsForcingName (levyCollapse ξ) (sequenceSubName θ P R σ B ξ) := by
  rw [forcingName_iff]
  intro z hz
  obtain ⟨x, hx, q, hq, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨w, _, rfl⟩ := (repl_spec _).mp hx
  exact ⟨checkName ∅ w, q, hq, rfl, checkName_isName (empty_mem_levyCollapse ξ) w⟩

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- Every function from `ω̌` into a checked set in the Levy extension lies in a bounded stage
`V[G_ξ]`, `ξ < κ`. -/
theorem levy_sequence_localized {θ : V} (f : (levyContext κ hG).Model)
    (hf : f ∈ (levyContext κ hG).check θ ^ (levyContext κ hG).check (ω : V)) :
    IsLocalized hG f := by
  let A := levyContext κ hG
  obtain ⟨σ, rfl⟩ := A.ofName_surjective f
  have hR := (levyCollapse_poset κ).1
  have hffun := IsFunction.of_mem hf
  have hdom : domain (A.ofName σ) = A.check (ω : V) := domain_eq_of_mem_function hf
  -- the tagged conditions deciding a value at an argument in `ω`
  let T : V := sep ((ω : V) ×ˢ levyCollapse κ)
    (IsValueDecider (levyCollapse κ) (levyOrder κ) σ.val (ω : V) θ) inferInstance
  have hTsub : T ⊆ (ω : V) ×ˢ levyCollapse κ := sep_subset
  have hmemT : ∀ n p, ⟨n, p⟩ₖ ∈ T ↔ n ∈ (ω : V) ∧ p ∈ levyCollapse κ ∧
      ∃ α ∈ θ, ForcesCheckedFunctionValue (levyCollapse κ) (levyOrder κ) ∅ σ.val p n α := by
    intro n p
    rw [mem_sep_iff]
    unfold IsValueDecider
    rw [kpair.π₁_kpair, kpair.π₂_kpair, kpair_mem_iff]
    constructor
    · rintro ⟨⟨hn, hp⟩, -, hα⟩
      exact ⟨hn, hp, hα⟩
    · rintro ⟨hn, hp, hα⟩
      exact ⟨⟨hn, hp⟩, ⟨hn, hp⟩, hα⟩
  obtain ⟨B, hB⟩ := exists_maximalAntichain (taggedOrderOn_preorder hR) hTsub
    (wellOrderable_of_internalChoice hAC _)
  have hslice : ∀ n ∈ (ω : V), IsMaximalAntichainIn (levyCollapse κ) (levyOrder κ)
      (taggedSlice (levyCollapse κ) T n) (antichainSlice (levyCollapse κ) B n) :=
    fun n hn ↦ taggedSliceOn_maximal hTsub hB hn
  have hdown : ∀ n, IsForcingDownwardClosed (levyCollapse κ) (levyOrder κ)
      (taggedSlice (levyCollapse κ) T n) := by
    intro n p hp q hq hqp
    obtain ⟨hpP, hpT⟩ := mem_sep_iff.mp hp
    obtain ⟨hn, -, α, hα, hforce⟩ := (hmemT n p).mp hpT
    refine mem_sep_iff.mpr ⟨hq, (hmemT n q).mpr ⟨hn, hq, α, hα, ?_⟩⟩
    exact (forcingFormula_regular hR functionValueFormula _).2.1 p hforce q hq hqp
  -- the supports of the slices are bounded below `κ`, uniformly by regularity
  have hbnd : ∀ n ∈ (ω : V), ∃ ζ ∈ κ,
      ∀ p ∈ antichainSlice (levyCollapse κ) B n, ordinalSupport p ⊆ ζ :=
    fun n hn ↦ levyAntichain_supports_bounded hAC hU hc hω hκ (hslice n hn).1
  let bound := leastOrdinalOrZero
    (fun n β ↦ β ∈ κ ∧ ∀ p ∈ antichainSlice (levyCollapse κ) B n, ordinalSupport p ⊆ β)
    (by definability)
  have hboundspec : ∀ n ∈ (ω : V), bound n ∈ κ ∧
      ∀ p ∈ antichainSlice (levyCollapse κ) B n, ordinalSupport p ⊆ bound n := by
    intro n hn
    obtain ⟨ζ, hζ, hsub⟩ := hbnd n hn
    have : IsOrdinal ζ := IsOrdinal.of_mem hζ
    exact (leastOrdinalOrZero_spec
      (fun n β ↦ β ∈ κ ∧ ∀ p ∈ antichainSlice (levyCollapse κ) B n, ordinalSupport p ⊆ β)
      (by definability) n ⟨ζ, inferInstance, hζ, hsub⟩).2.1
  have hreg := measurable_regular hκ (IsOrdinal.toIsTransitive.transitive _ hω) hU hc
  have hFdef : ℒₛₑₜ-function₁ bound := leastOrdinalOrZero_definable _ _
  let gr := definableGraph (ω : V) bound hFdef
  have hgr : gr ∈ κ ^ (ω : V) := by
    apply mem_function_of_mem_function_of_subset (definableGraph_mem_function (ω : V) _ hFdef)
    intro y hy
    obtain ⟨n, hn, rfl⟩ := (repl_spec hFdef).mp hy
    exact (hboundspec n hn).1
  obtain ⟨ξ, hξκ, hξ⟩ := regularCardinal_maps_bounded hreg hω hgr
  have hξord : IsOrdinal ξ := IsOrdinal.of_mem hξκ
  have hξsub : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξκ
  have hAξ : ∀ n ∈ (ω : V), ∀ p ∈ antichainSlice (levyCollapse κ) B n, p ∈ levyCollapse ξ := by
    intro n hn p hp
    have hpP : p ∈ levyCollapse κ := (mem_sep_iff.mp hp).1
    have hb := hξ n hn
    rw [value_definableGraph (ω : V) _ hFdef hn] at hb
    have hsupp : ordinalSupport p ⊆ ξ :=
      subset_trans ((hboundspec n hn).2 p hp) (IsOrdinal.toIsTransitive.transitive _ hb)
    rw [← levyCut_eq_of_support hpP hsupp]
    exact levyCut_mem hpP
  -- the function is the value of the subcollapse name
  refine ⟨ξ, hξκ, ?_⟩
  have hν := sequenceSubName_isName θ (levyCollapse κ) (levyOrder κ) σ.val B ξ
  refine (inLevySubmodel_iff ξ hξsub hG _).mpr ⟨⟨_, hν⟩, ?_⟩
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hf z hz)
    obtain ⟨n, hn, rfl⟩ := (A.mem_check_iff _ _).mp hx
    obtain ⟨α, hα, rfl⟩ := (A.mem_check_iff _ _).mp hy
    have hαv : (A.ofName σ) ‘ (A.check n) = A.check α := value_eq_of_kpair_mem hz
    obtain ⟨p, hpG, hforce⟩ := (A.checkedFunctionValue_truth σ n α).mpr ⟨hffun, hαv⟩
    have hpT : p ∈ taggedSlice (levyCollapse κ) T n :=
      mem_sep_iff.mpr ⟨hG.1.1 p hpG, (hmemT n p).mpr ⟨hn, hG.1.1 p hpG, α, hα, hforce⟩⟩
    obtain ⟨a, ha, haG⟩ := generic_meets_maximalAntichain_of_meets hR hG (hdown n) sep_subset
      (hslice n hn) hpG hpT
    obtain ⟨-, -, α', hα', hforce'⟩ := (hmemT n a).mp (mem_sep_iff.mp ((hslice n hn).2.1 a ha)).2
    obtain ⟨r, hrG, hra, hrp⟩ := hG.1.2.2.2 a haG p hpG
    have hr := hG.1.1 r hrG
    have hreg' := forcingFormula_regular hR functionValueFormula
    have h1 := hreg' _ |>.2.1 a hforce' r hr hra
    have h2 := hreg' _ |>.2.1 p hforce r hr hrp
    have hαα' : α' = α := forcesCheckedFunctionValue_unique hR (levyCollapse_top κ) σ.property h1 h2
    rw [← A.check_kpair]
    refine (A.mem_ofName_iff _ _).mpr ⟨⟨checkName ∅ ⟨n, α⟩ₖ,
      checkName_isName (levyCollapse_top κ).1 _⟩, a, haG, ?_, rfl⟩
    exact (kpair_mem_sequenceSubName_iff _ _ _ _ _ _ _ _).mpr
      ⟨⟨⟨n, α⟩ₖ, kpair_mem_iff.mpr ⟨hn, hα⟩, rfl⟩, hAξ n hn a ha, n, hn, α, hα, rfl, ha,
        hαα' ▸ hforce'⟩
  · intro hz
    obtain ⟨ν', q, hqG, hνq, rfl⟩ := (A.mem_ofName_iff _ z).mp hz
    obtain ⟨-, -, n, hn, α, hα, hνeq, -, hforce⟩ :=
      (kpair_mem_sequenceSubName_iff _ _ _ _ _ _ _ _).mp hνq
    have hν' : ν' = ⟨checkName ∅ ⟨n, α⟩ₖ, checkName_isName (levyCollapse_top κ).1 _⟩ :=
      Subtype.ext hνeq
    rw [hν']
    show A.check ⟨n, α⟩ₖ ∈ A.ofName σ
    obtain ⟨-, hval⟩ := (A.checkedFunctionValue_truth σ n α).mp ⟨q, hqG, hforce⟩
    have hnd : A.check n ∈ domain (A.ofName σ) := by
      rw [hdom]
      exact (A.check_mem_iff n (ω : V)).mpr hn
    have hpair := kpair_value_mem hnd
    rw [hval] at hpair
    rw [A.check_kpair]
    exact hpair

end

end ZFVP
