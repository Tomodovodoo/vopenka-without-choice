import ZFVP.ModelTheory.LevyCollapseOmegaOne
import ZFVP.ModelTheory.LevySubsetLocalization
import ZFVP.SetTheory.InverseFunction

/-! The chain-condition cover property of the Levy collapse: the range of a function in `V[G]`
from a checked set `Ď` into a checked set `θ̌` is covered by the check of a ground set of size at
most `|D × κ|`, the set of values decided on a maximal antichain of deciders. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The slice of a maximal antichain of a tagged set is a maximal antichain of the slice. -/
theorem taggedSliceOn_maximal {θ P R T B : V} (hT : T ⊆ θ ×ˢ P)
    (hB : IsMaximalAntichainIn (θ ×ˢ P) (taggedOrderOn θ P R) T B) {n : V} (hn : n ∈ θ) :
    IsMaximalAntichainIn P R (taggedSlice P T n) (antichainSlice P B n) := by
  refine ⟨⟨sep_subset, ?_⟩, ?_, ?_⟩
  · intro a ha b hb hne hc
    obtain ⟨haP, haB⟩ := mem_sep_iff.mp ha
    obtain ⟨hbP, hbB⟩ := mem_sep_iff.mp hb
    have hne' : ⟨n, a⟩ₖ ≠ ⟨n, b⟩ₖ := fun h ↦ hne (kpair_inj h).2
    exact hB.1.2 _ haB _ hbB hne' ((taggedCompatibleOn_iff hn haP hn hbP).mpr ⟨rfl, hc⟩)
  · intro a ha
    obtain ⟨haP, haB⟩ := mem_sep_iff.mp ha
    exact mem_sep_iff.mpr ⟨haP, hB.2.1 _ haB⟩
  · intro d hd
    obtain ⟨hdP, hdT⟩ := mem_sep_iff.mp hd
    obtain ⟨b, hbB, hcomp⟩ := hB.2.2 _ hdT
    obtain ⟨m, hm, a, haP, rfl⟩ := mem_prod_iff.mp (hT b (hB.2.1 b hbB))
    obtain ⟨rfl, hca⟩ := (taggedCompatibleOn_iff hm haP hn hdP).mp hcomp
    exact ⟨a, mem_sep_iff.mpr ⟨haP, hbB⟩, hca⟩

/-- The conditions deciding a value of `σ` at a checked argument in `D`. -/
def IsValueDecider (P R σ D θ z : V) : Prop :=
  z ∈ D ×ˢ P ∧ ∃ α ∈ θ, ForcesCheckedFunctionValue P R ∅ σ (kpair.π₂ z) (kpair.π₁ z) α

instance isValueDecider_definable (P R σ D θ : V) : ℒₛₑₜ-predicate (IsValueDecider P R σ D θ) := by
  unfold IsValueDecider
  definability

/-- The values decided on the antichain slices. -/
def IsDecidedValue (P R σ D B θ α : V) : Prop :=
  α ∈ θ ∧ ∃ d ∈ D, ∃ a ∈ antichainSlice P B d, ForcesCheckedFunctionValue P R ∅ σ a d α

instance isDecidedValue_definable (P R σ D B θ : V) : ℒₛₑₜ-predicate (IsDecidedValue P R σ D B θ) := by
  unfold IsDecidedValue
  definability

/-- The injections of the antichain slice at `d` into `κ`. -/
noncomputable def antichainSliceInjections (P B κ d : V) : V := {f ∈ κ ^ antichainSlice P B d ; Injective f}

theorem antichainSliceInjections_definable_one (P B κ : V) : ℒₛₑₜ-function₁[V] (antichainSliceInjections P B κ) := by
  have h : ℒₛₑₜ-relation[V] (fun S d ↦ ∀ f, f ∈ S ↔ f ∈ κ ^ antichainSlice P B d ∧ Injective f) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = antichainSliceInjections P B κ (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [antichainSliceInjections, mem_sep_iff]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- The range of a function from `Ď` into `θ̌` in the Levy extension lies inside the check of a
ground set of size at most `|D × κ|`. -/
theorem levy_range_cover {D θ : V} (h : (levyContext κ hG).Model)
    (hh : h ∈ (levyContext κ hG).check θ ^ (levyContext κ hG).check D) :
    ∃ Y : V, Y ⊆ θ ∧ Y ≤# D ×ˢ κ ∧ range h ⊆ (levyContext κ hG).check Y := by
  let A := levyContext κ hG
  obtain ⟨σ, rfl⟩ := A.ofName_surjective h
  have hR := (levyCollapse_poset κ).1
  have hσfun := IsFunction.of_mem hh
  let P := levyCollapse κ
  let R := levyOrder κ
  -- the deciders and a maximal antichain of them
  let T : V := sep (D ×ˢ P) (IsValueDecider P R σ.val D θ) inferInstance
  have hTsub : T ⊆ D ×ˢ P := sep_subset
  have hmemT : ∀ d p, ⟨d, p⟩ₖ ∈ T ↔ d ∈ D ∧ p ∈ P ∧
      ∃ α ∈ θ, ForcesCheckedFunctionValue P R ∅ σ.val p d α := by
    intro d p
    rw [mem_sep_iff]
    unfold IsValueDecider
    rw [kpair.π₁_kpair, kpair.π₂_kpair, kpair_mem_iff]
    constructor
    · rintro ⟨⟨hd, hp⟩, -, hα⟩
      exact ⟨hd, hp, hα⟩
    · rintro ⟨hd, hp, hα⟩
      exact ⟨⟨hd, hp⟩, ⟨hd, hp⟩, hα⟩
  obtain ⟨B, hB⟩ := exists_maximalAntichain (taggedOrderOn_preorder hR) hTsub
    (wellOrderable_of_internalChoice hAC _)
  have hslice : ∀ d ∈ D, IsMaximalAntichainIn P R (taggedSlice P T d) (antichainSlice P B d) :=
    fun d hd ↦ taggedSliceOn_maximal hTsub hB hd
  have hdown : ∀ d, IsForcingDownwardClosed P R (taggedSlice P T d) := by
    intro d p hp q hq hqp
    obtain ⟨hpP, hpT⟩ := mem_sep_iff.mp hp
    obtain ⟨hd, -, α, hα, hforce⟩ := (hmemT d p).mp hpT
    refine mem_sep_iff.mpr ⟨hq, (hmemT d q).mpr ⟨hd, hq, α, hα, ?_⟩⟩
    exact (forcingFormula_regular hR functionValueFormula _).2.1 p hforce q hq hqp
  -- the decided values
  let Y : V := sep θ (IsDecidedValue P R σ.val D B θ) inferInstance
  have hmemY : ∀ α, α ∈ Y ↔ α ∈ θ ∧ ∃ d ∈ D, ∃ a ∈ antichainSlice P B d,
      ForcesCheckedFunctionValue P R ∅ σ.val a d α := by
    intro α
    rw [mem_sep_iff]
    unfold IsDecidedValue
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1, h⟩⟩
  have hBsub : B ⊆ D ×ˢ P := fun z hz ↦ hTsub z (hB.2.1 z hz)
  refine ⟨Y, sep_subset, ?_, ?_⟩
  · -- `Y ≤# B ≤# D × κ`
    have hYB : Y ≤# B := by
      refine cardLE_of_separating_relation (wellOrderable_of_internalChoice hAC B)
        (fun α z ↦ z ∈ B ∧ ForcesCheckedFunctionValue P R ∅ σ.val (kpair.π₂ z) (kpair.π₁ z) α)
        (by definability) ?_ ?_
      · intro α hα
        obtain ⟨-, d, hd, a, ha, hforce⟩ := (hmemY α).mp hα
        refine ⟨⟨d, a⟩ₖ, (mem_sep_iff.mp ha).2, (mem_sep_iff.mp ha).2, ?_⟩
        rw [kpair.π₁_kpair, kpair.π₂_kpair]
        exact hforce
      · intro α hα β hβ z hz h1 h2
        exact forcesCheckedFunctionValue_unique hR (levyCollapse_top κ) σ.property h1.2 h2.2
    have hBD : B ≤# D ×ˢ κ := by
      have hinj : ∀ d ∈ D, IsNonempty (antichainSliceInjections P B κ d) := by
        intro d hd
        obtain ⟨μ, hμ, hle⟩ := levyAntichain_small hAC hU hc hω hκ (hslice d hd).1
        have hle' : antichainSlice P B d ≤# κ :=
          hle.trans (cardLE_of_subset (IsOrdinal.toIsTransitive.transitive μ hμ))
        obtain ⟨f, hf, hfinj⟩ := hle'
        exact ⟨⟨f, mem_sep_iff.mpr ⟨hf, hfinj⟩⟩⟩
      obtain ⟨g, hgf, hgd, hgval⟩ :=
        choice_for_definable_family hAC D _ (antichainSliceInjections_definable_one P B κ) hinj
      refine cardLE_of_separating_relation (wellOrderable_of_internalChoice hAC _)
        (fun z w ↦ w = ⟨kpair.π₁ z, (g ‘ (kpair.π₁ z)) ‘ (kpair.π₂ z)⟩ₖ) (by definability) ?_ ?_
      · intro z hz
        obtain ⟨d, hd, a, ha, rfl⟩ := mem_prod_iff.mp (hBsub z hz)
        have hgd' := mem_sep_iff.mp (hgval d hd)
        refine ⟨⟨d, (g ‘ d) ‘ a⟩ₖ, kpair_mem_iff.mpr ⟨hd, ?_⟩, ?_⟩
        · exact function_value_mem hgd'.1 (mem_sep_iff.mpr ⟨ha, hz⟩)
        · rw [kpair.π₁_kpair, kpair.π₂_kpair]
      · intro z hz z' hz' w hw h1 h2
        obtain ⟨d, hd, a, ha, rfl⟩ := mem_prod_iff.mp (hBsub z hz)
        obtain ⟨d', hd', a', ha', rfl⟩ := mem_prod_iff.mp (hBsub z' hz')
        rw [kpair.π₁_kpair, kpair.π₂_kpair] at h1 h2
        rw [h1] at h2
        obtain ⟨hdd, hval⟩ := kpair_inj h2
        subst hdd
        have hgd' := mem_sep_iff.mp (hgval d hd)
        have haS : a ∈ antichainSlice P B d := mem_sep_iff.mpr ⟨ha, hz⟩
        have ha'S : a' ∈ antichainSlice P B d := mem_sep_iff.mpr ⟨ha', hz'⟩
        rw [injective_value_eq hgd'.1 hgd'.2 haS ha'S hval]
    exact hYB.trans hBD
  · -- the actual values are decided on the antichains
    intro y hy
    obtain ⟨d', hd'y⟩ := mem_range_iff.mp hy
    obtain ⟨d'', hd'', y', hy', he⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hh _ hd'y)
    obtain ⟨rfl, rfl⟩ := kpair_inj he
    obtain ⟨d, hd, rfl⟩ := (A.mem_check_iff _ _).mp hd''
    obtain ⟨α, hα, rfl⟩ := (A.mem_check_iff _ _).mp hy'
    have hαv : (A.ofName σ) ‘ (A.check d) = A.check α := value_eq_of_kpair_mem hd'y
    obtain ⟨p, hpG, hforce⟩ := (A.checkedFunctionValue_truth σ d α).mpr ⟨hσfun, hαv⟩
    have hpT : p ∈ taggedSlice P T d :=
      mem_sep_iff.mpr ⟨hG.1.1 p hpG, (hmemT d p).mpr ⟨hd, hG.1.1 p hpG, α, hα, hforce⟩⟩
    obtain ⟨a, ha, haG⟩ := generic_meets_maximalAntichain_of_meets hR hG (hdown d) sep_subset
      (hslice d hd) hpG hpT
    obtain ⟨-, -, α', hα', hforce'⟩ := (hmemT d a).mp (mem_sep_iff.mp ((hslice d hd).2.1 a ha)).2
    obtain ⟨r, hrG, hra, hrp⟩ := hG.1.2.2.2 a haG p hpG
    have hr := hG.1.1 r hrG
    have hreg' := forcingFormula_regular hR functionValueFormula
    have h1 := hreg' _ |>.2.1 a hforce' r hr hra
    have h2 := hreg' _ |>.2.1 p hforce r hr hrp
    have hαα' : α' = α := forcesCheckedFunctionValue_unique hR (levyCollapse_top κ) σ.property h1 h2
    exact (A.check_mem_iff _ _).mpr ((hmemY α).mpr ⟨hα, d, hd, a, ha, hαα' ▸ hforce'⟩)

end

end ZFVP
