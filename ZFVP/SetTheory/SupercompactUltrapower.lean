import ZFVP.SetTheory.UltrapowerElementary
import ZFVP.SetTheory.UltrapowerCritical
import ZFVP.SetTheory.UltrapowerClosure
import ZFVP.SetTheory.StageSmallSubsets
import ZFVP.SetTheory.FiniteCofinality
import ZFVP.SetTheory.CnAbsoluteness

/-! # The ultrapower of a rank stage by a supercompactness measure

This module puts together the pieces of the ultrapower construction. Take `κ` supercompact in
the measure sense (`IsSupercompact`, `ZFVP.SetTheory.SupercompactMeasure`), an ordinal `lam` at
or above `κ`, and a regular cardinal `θ` above `lam`. The measure `U` on `P_κ(lam)` given by
supercompactness yields an ultrapower of the rank stage `hierarchy θ`, and the collapse target
`M` of that ultrapower together with the canonical map `j` satisfies all four properties one
asks of a supercompactness embedding:

* `M` is transitive and nonempty;
* `j : hierarchy θ → M` is a coded elementary embedding of membership structures;
* `κ` is the critical point of `j`, and `j` fixes every ordinal below `κ`;
* `M` is closed under `lam`-indexed families, in the range form and in the subset form.

Every step is imported. `ultraEmbedding_codedMembershipEmbedding` gives elementarity,
`ultraEmbedding_criticalPoint` and `ultraEmbedding_fixes_ordinal` give the critical point,
`range_mem_ultraTarget` and `mem_ultraTarget_of_subset_cardLE` give the closure. The work here
is discharging their hypotheses about the stage `hierarchy θ`: transitivity is
`hierarchy_transitive`, membership of `κ` is `ordinal_mem_hierarchy_iff`, closure under subsets
is `subset_mem_hierarchy_limit` through `regularCardinal_succ_closed`, and closure under small
subsets is `small_subset_mem_hierarchy`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The internal ultrapower of a rank stage by a supercompactness measure. -/
theorem supercompact_ultrapower_stage (hAC : InternalChoice V) {κ lam θ : V}
    (h : IsSupercompact κ) (hlam : IsOrdinal lam) (hκlam : κ ⊆ lam) (h0 : (∅ : V) ∈ lam)
    (hθ : IsRegularCardinal θ) (hlamθ : lam ∈ θ) (hκθ : κ ∈ θ) :
    ∃ M j : V, IsTransitive M ∧ IsNonempty M ∧
      IsCodedMembershipEmbedding (hierarchy θ) M j ∧
      IsCriticalPoint (hierarchy θ) j κ ∧
      (∀ s, s ∈ M ^ lam → range s ∈ M) ∧
      (∀ y, y ⊆ M → IsNonempty y → y ≤# lam → y ∈ M) ∧
      (∀ α ∈ κ, j ‘ α = α) := by
  have hκord : IsOrdinal κ := h.isOrdinal
  have hθord : IsOrdinal θ := hθ.1.1
  have hAtrans : IsTransitive (hierarchy θ) := hierarchy_transitive θ
  obtain ⟨U, hU⟩ := h.measure hlam hκlam
  set A : V := hierarchy θ with hAdef
  set P : V := smallSubsetsBelow κ lam with hPdef
  -- the stage contains `κ` and every ordinal below `θ`
  have hκA : κ ∈ A := ordinal_mem_hierarchy_iff.mpr hκθ
  have hθsub : θ ⊆ A := fun x hx ↦ ordinal_subset_hierarchy θ x hx
  have hκθsub : κ ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hκθ
  have hκsub : κ ⊆ A := fun x hx ↦ hθsub _ (hκθsub _ hx)
  have hA : IsNonempty A := ⟨⟨κ, hκA⟩⟩
  -- the stage is closed under subsets and under small subsets
  have hsucc : ∀ β ∈ θ, succ β ∈ θ := fun _ hβ ↦ regularCardinal_succ_closed hθ hβ
  have hsubset : ∀ w z : V, z ∈ A → w ⊆ z → w ∈ A :=
    fun _ _ hz hw ↦ subset_mem_hierarchy_limit hsucc hz hw
  have hsmall : ∀ w : V, w ⊆ A → USmall κ w → w ∈ A :=
    fun _ hw hs ↦ small_subset_mem_hierarchy hθ hκθ hw hs
  -- the pieces of the measure
  have hUf : IsSetUltrafilter P U := hU.1
  have hcomp : IsOrdinalCompleteOn P κ U := hU.2.1
  have hω : (ω : V) ∈ κ := h.2.1
  have hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P) :=
    ultraMemRelation_wellFounded hAC hUf hcomp hω
  refine ⟨ultraTarget P U A, ultraEmbedding P U A, ultraTarget_transitive hwf,
    ultraTarget_nonempty hwf hA,
    ultraEmbedding_codedMembershipEmbedding hAC (κ := κ) hUf hcomp hω hA,
    ultraEmbedding_criticalPoint hAC h.1 hU hω hA h0 hκA hκsub hκlam hsubset,
    fun s hs ↦ range_mem_ultraTarget hAC hU hPdef hcomp hω hA hsmall h0 hs,
    fun y hy hne hcard ↦
      mem_ultraTarget_of_subset_cardLE hAC hU hPdef hcomp hω hA hsmall h0 hy hne hcard,
    ultraEmbedding_fixes_ordinal hAC hUf hcomp hω hA hκsub⟩

end ZFVP
