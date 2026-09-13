import ZFVP.SetTheory.UltrapowerSmallValues
import ZFVP.SetTheory.UltrapowerSeed
import ZFVP.ModelTheory.CriticalPoint

/-! # The critical point of the ultrapower by a normal fine measure

For a normal fine measure `U` on `P_κ(lam)` the canonical map of the internal ultrapower fixes
every ordinal below `κ` (`ultraEmbedding_fixes_ordinal`) and moves `κ`. This module proves the
second half and puts the two together.

The witness is the trace function `x ↦ x ∩ κ`. Fineness makes every `β ∈ κ` a member of its
collapse; normality makes every member of its collapse an ordinal below `κ`. So the collapse of
the trace function is `κ` itself, while the collapse of the constant function at `κ` is
`(ultraEmbedding) ‘ κ`. If those two agreed the two functions would be a.e. equal, so some member
of `P_κ(lam)` would contain `κ`, which is impossible because members of `P_κ(lam)` inject into
ordinals below `κ` and `κ` is initial. No regularity of `κ` is used.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The part of `x` below `κ`. This is the value of the trace function. -/
noncomputable def traceBelow (κ x : V) : V := x ∩ κ

theorem traceBelow_definable_one (κ : V) : ℒₛₑₜ-function₁[V] (traceBelow κ) := by
  unfold traceBelow
  definability

/-- The trace function of the ultrapower: `x` goes to `x ∩ κ`. -/
noncomputable def traceFunction (P κ : V) : V :=
  definableGraph P (traceBelow κ) (traceBelow_definable_one κ)

theorem value_traceFunction {P κ x : V} (hx : x ∈ P) : (traceFunction P κ) ‘ x = x ∩ κ :=
  value_definableGraph P (traceBelow κ) (traceBelow_definable_one κ) hx

theorem traceFunction_mem_ultraFunctions {P A κ : V} (hκA : κ ∈ A)
    (hsubset : ∀ w z, z ∈ A → w ⊆ z → w ∈ A) : traceFunction P κ ∈ A ^ P := by
  refine definableGraph_mem_function_of_mapsTo P A (traceBelow κ) (traceBelow_definable_one κ) ?_
  intro x _
  refine hsubset _ κ hκA ?_
  intro y hy
  exact (mem_inter_iff.mp hy).2

/-- The collapse of the trace function is `κ`. -/
theorem ultraCollapse_traceFunction (hAC : InternalChoice V) {U A κ lam : V} [IsOrdinal κ]
    [IsTransitive A] (hU : IsNormalFineMeasure κ lam U) (hω : (ω : V) ∈ κ) (hA : IsNonempty A)
    (h0 : (∅ : V) ∈ lam) (hκA : κ ∈ A) (hκ : κ ⊆ A) (hlam : κ ⊆ lam)
    (hsubset : ∀ w z, z ∈ A → w ⊆ z → w ∈ A) :
    (ultraCollapse (smallSubsetsBelow κ lam) U A) ‘
      (traceFunction (smallSubsetsBelow κ lam) κ) = κ := by
  set P : V := smallSubsetsBelow κ lam with hP
  have hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P) :=
    ultraMemRelation_wellFounded hAC hU.1 hU.2.1 hω
  have hf : traceFunction P κ ∈ A ^ P := traceFunction_mem_ultraFunctions hκA hsubset
  have hfix : ∀ α ∈ κ, (ultraEmbedding P U A) ‘ α = α :=
    ultraEmbedding_fixes_ordinal hAC hU.1 hU.2.1 hω hA hκ
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨g, hg, hgmem, hgval⟩ := (mem_ultraCollapse_value hwf hf).mp hz
    have hset : ultraMem P g (traceFunction P κ) ∈ U := hgmem
    -- the trace of `x` is a subset of `x`, so `g` is regressive almost everywhere
    have hreg : UltraMem P U g (SetTheory.identity P) := by
      show ultraMem P g (SetTheory.identity P) ∈ U
      rw [ultraMem_identity_eq]
      refine hU.upward hset (fun x hx ↦ (mem_sep_iff.mp hx).1) ?_
      intro x hx
      obtain ⟨hxP, hv⟩ := (mem_ultraMem_iff P g (traceFunction P κ) x).mp hx
      rw [value_traceFunction hxP] at hv
      exact mem_sep_iff.mpr ⟨hxP, (mem_inter_iff.mp hv).1⟩
    obtain ⟨ξ, -, hgeq⟩ := ultraMem_identity_eq_constant hU h0 hg hreg
    -- the constancy set meets the regressive set, and there the value lies in `κ`
    have hξκ : ξ ∈ κ := by
      obtain ⟨x, hx⟩ := hU.1.nonempty_of_mem (hU.1.inter hgeq hset)
      rw [mem_inter_iff, mem_ultraAgree_iff, mem_ultraMem_iff] at hx
      obtain ⟨⟨hxP, hv⟩, -, hmem⟩ := hx
      rw [value_constantGraph P ξ hxP] at hv
      rw [value_traceFunction hxP, hv] at hmem
      exact (mem_inter_iff.mp hmem).2
    have hξA : ξ ∈ A := hκ ξ hξκ
    have hcol : (ultraCollapse P U A) ‘ g = (ultraCollapse P U A) ‘ (constantGraph P ξ) :=
      ultraCollapse_eq_of_ultraEq hwf hU.1 hg (constantGraph_mem_ultraFunctions hξA) hgeq
    have hzξ : z = ξ := by
      rw [← hgval, hcol, ← value_ultraEmbedding (P := P) (U := U) hξA]
      exact hfix ξ hξκ
    rw [hzξ]
    exact hξκ
  · intro hz
    have hzA : z ∈ A := hκ z hz
    refine (mem_ultraCollapse_value hwf hf).mpr
      ⟨constantGraph P z, constantGraph_mem_ultraFunctions hzA, ?_, ?_⟩
    · show ultraMem P (constantGraph P z) (traceFunction P κ) ∈ U
      refine hU.upward (normalFineMeasure_fine hU (hlam z hz))
        (ultraMem_subset P (constantGraph P z) (traceFunction P κ)) ?_
      intro x hx
      obtain ⟨hxP, hzx⟩ := mem_sep_iff.mp hx
      refine (mem_ultraMem_iff P (constantGraph P z) (traceFunction P κ) x).mpr ⟨hxP, ?_⟩
      rw [value_constantGraph P z hxP, value_traceFunction hxP]
      exact mem_inter_iff.mpr ⟨hzx, hz⟩
    · rw [← value_ultraEmbedding (P := P) (U := U) hzA]
      exact hfix z hz

/-- The canonical map moves `κ`. -/
theorem ultraEmbedding_moves_kappa (hAC : InternalChoice V) {U A κ lam : V} [IsOrdinal κ]
    [IsTransitive A] (hinit : IsInitialOrdinal κ) (hU : IsNormalFineMeasure κ lam U)
    (hω : (ω : V) ∈ κ) (hA : IsNonempty A) (h0 : (∅ : V) ∈ lam) (hκA : κ ∈ A) (hκ : κ ⊆ A)
    (hlam : κ ⊆ lam) (hsubset : ∀ w z, z ∈ A → w ⊆ z → w ∈ A) :
    (ultraEmbedding (smallSubsetsBelow κ lam) U A) ‘ κ ≠ κ := by
  set P : V := smallSubsetsBelow κ lam with hP
  intro heq
  have hf : traceFunction P κ ∈ A ^ P := traceFunction_mem_ultraFunctions hκA hsubset
  have hcol : (ultraCollapse P U A) ‘ (traceFunction P κ) = κ :=
    ultraCollapse_traceFunction hAC hU hω hA h0 hκA hκ hlam hsubset
  have h1 : (ultraCollapse P U A) ‘ (constantGraph P κ)
      = (ultraCollapse P U A) ‘ (traceFunction P κ) := by
    rw [← value_ultraEmbedding (P := P) (U := U) hκA, heq, hcol]
  have h2 : UltraEq P U (constantGraph P κ) (traceFunction P κ) :=
    (ultraCollapse_eq_iff hAC hU.1 hU.2.1 hω hA (constantGraph_mem_ultraFunctions hκA) hf).mp h1
  obtain ⟨x, hx⟩ := hU.1.nonempty_of_mem h2
  rw [mem_ultraAgree_iff] at hx
  obtain ⟨hxP, hv⟩ := hx
  rw [value_constantGraph P κ hxP, value_traceFunction hxP] at hv
  -- `κ ⊆ x` and `x` injects into an ordinal below `κ`, contradicting initiality
  have hsub : κ ⊆ x := by
    intro β hβ
    rw [hv] at hβ
    exact (mem_inter_iff.mp hβ).1
  obtain ⟨-, μ, hμ, hle⟩ := (mem_smallSubsetsBelow_iff κ lam x).mp hxP
  exact hinit.2 μ hμ ((cardLE_of_subset hsub).trans hle)

/-- `κ` is the critical point of the canonical map of the ultrapower. -/
theorem ultraEmbedding_criticalPoint (hAC : InternalChoice V) {U A κ lam : V} [IsOrdinal κ]
    [IsTransitive A] (hinit : IsInitialOrdinal κ) (hU : IsNormalFineMeasure κ lam U)
    (hω : (ω : V) ∈ κ) (hA : IsNonempty A) (h0 : (∅ : V) ∈ lam) (hκA : κ ∈ A) (hκ : κ ⊆ A)
    (hlam : κ ⊆ lam) (hsubset : ∀ w z, z ∈ A → w ⊆ z → w ∈ A) :
    IsCriticalPoint A (ultraEmbedding (smallSubsetsBelow κ lam) U A) κ := by
  set P : V := smallSubsetsBelow κ lam with hP
  refine ⟨inferInstance, ⟨hκA, ultraEmbedding_moves_kappa hAC hinit hU hω hA h0 hκA hκ hlam
    hsubset⟩, ?_⟩
  intro β hβ hmoved
  have : IsOrdinal β := hβ
  rcases IsOrdinal.subset_or_supset κ β with h | h
  · exact h
  · rcases IsOrdinal.subset_iff.mp h with rfl | hβκ
    · exact subset_refl _
    · exact absurd (ultraEmbedding_fixes_ordinal hAC hU.1 hU.2.1 hω hA hκ β hβκ) hmoved.2

end ZFVP
