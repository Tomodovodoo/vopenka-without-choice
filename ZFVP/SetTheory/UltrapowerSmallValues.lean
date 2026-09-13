import ZFVP.SetTheory.UltrapowerEmbeddingMap

/-! Small values in the internal ultrapower.

An ultrafilter that is complete for intersections of fewer than `κ` of its members cannot spread
the values of a function over an ordinal `α` below `κ` without concentrating on one of them: if the
values lie in `α` almost everywhere then the function is almost everywhere constant. From that the
canonical map of the ultrapower fixes every ordinal below `κ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The set of indices where `f` misses the constant value `β`. This is the family fed to
completeness in `ultraEq_constantGraph_of_values_below`. -/
noncomputable def ultraMissSet (P f β : V) : V :=
  relativeComplement P (ultraAgree P f (constantGraph P β))

theorem ultraMissSet_definable_one (P f : V) : ℒₛₑₜ-function₁[V] (ultraMissSet P f) := by
  have h : ℒₛₑₜ-relation[V] (fun Y β : V ↦
      ∃ c, c = constantGraph P β ∧ ∃ a, a = ultraAgree P f c ∧ Y = relativeComplement P a) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = ultraMissSet P f (v 1) ↔ _
  unfold ultraMissSet
  constructor
  · intro hY
    exact ⟨_, rfl, _, rfl, hY⟩
  · rintro ⟨c, hc, a, ha, hY⟩
    rw [hY, ha, hc]

/-- The index set where `f` takes the constant value `β`. -/
theorem ultraAgree_constantGraph_right (P f β : V) :
    ultraAgree P f (constantGraph P β) = {p ∈ P ; f ‘ p = β} := by
  apply mem_ext
  intro p
  rw [mem_ultraAgree_iff, mem_sep_iff]
  constructor
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P β hp] at hv
    exact ⟨hp, hv⟩
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P β hp]
    exact ⟨hp, hv⟩

/-- Completeness in the form the ultrapower uses: a function whose values lie almost everywhere
below an ordinal smaller than the completeness degree is almost everywhere constant. -/
theorem ultraEq_constantGraph_of_values_below {P U A κ α f : V} [IsOrdinal κ]
    (hU : IsSetUltrafilter P U) (hcomp : IsOrdinalCompleteOn P κ U) (hα : α ∈ κ)
    (hf : f ∈ A ^ P) (hval : {p ∈ P ; f ‘ p ∈ α} ∈ U) :
    ∃ β ∈ α, UltraEq P U f (constantGraph P β) := by
  by_contra hcon
  push Not at hcon
  -- Missing every value below `α` is a family of `α`-many members of `U`.
  have hmiss : ∀ β ∈ α, ultraMissSet P f β ∈ U := by
    intro β hβ
    exact (ultraCompl_mem_iff hU (ultraAgree_subset P f (constantGraph P β))).mpr (hcon β hβ)
  set g : V := definableGraph α (ultraMissSet P f) (ultraMissSet_definable_one P f) with hgdef
  have hgf : g ∈ U ^ α :=
    definableGraph_mem_function_of_mapsTo _ _ _ (ultraMissSet_definable_one P f) hmiss
  have hint : indexedIntersection P α g ∈ U := hcomp α hα g hgf
  obtain ⟨p, hp⟩ := hU.nonempty_of_mem (hU.inter hint hval)
  rw [mem_inter_iff, mem_indexedIntersection_iff, mem_sep_iff] at hp
  -- At `p` the value of `f` is below `α`, so `f` does not miss it there.
  obtain ⟨⟨-, hall⟩, hpP, hfp⟩ := hp
  have hpm : p ∈ ultraMissSet P f (f ‘ p) := by
    have := hall (f ‘ p) hfp
    rwa [hgdef, value_definableGraph _ _ (ultraMissSet_definable_one P f) hfp] at this
  rw [ultraMissSet, mem_relativeComplement_iff, ultraAgree_constantGraph_right, mem_sep_iff] at hpm
  exact hpm.2 ⟨hpP, rfl⟩

/-- The canonical map fixes every ordinal below the completeness degree. -/
theorem ultraEmbedding_fixes_ordinal (hAC : InternalChoice V) {P U A κ : V} [IsOrdinal κ]
    [IsTransitive A] (hU : IsSetUltrafilter P U) (hcomp : IsOrdinalCompleteOn P κ U)
    (hω : (ω : V) ∈ κ) (hA : IsNonempty A) (hκA : κ ⊆ A) :
    ∀ α ∈ κ, (ultraEmbedding P U A) ‘ α = α := by
  have hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P) :=
    ultraMemRelation_wellFounded hAC hU hcomp hω
  have hPd : ℒₛₑₜ-predicate[V] (fun α : V ↦ α ∈ κ →
      ∃ m, m = ultraEmbedding P U A ∧ m ‘ α = α) := by definability
  have hall : ∀ α : Ordinal V, (α : V) ∈ κ → (ultraEmbedding P U A) ‘ (α : V) = (α : V) := by
    have key : ∀ α : Ordinal V, ((α : V) ∈ κ →
        ∃ m, m = ultraEmbedding P U A ∧ m ‘ (α : V) = (α : V)) := by
      refine transfinite_induction _ hPd ?_
      rintro α ih hακ
      refine ⟨_, rfl, ?_⟩
      have hαA : (α : V) ∈ A := hκA _ hακ
      rw [value_ultraEmbedding hαA]
      apply mem_ext
      intro z
      constructor
      · intro hz
        obtain ⟨k, hk, hkmem, hkval⟩ :=
          (mem_ultraCollapse_value hwf (constantGraph_mem_ultraFunctions hαA)).mp hz
        have hkval' : {p ∈ P ; k ‘ p ∈ (α : V)} ∈ U := by
          have := hkmem
          rwa [UltraMem, ultraMem_constantGraph_right] at this
        obtain ⟨β, hβ, hβeq⟩ :=
          ultraEq_constantGraph_of_values_below (A := A) hU hcomp hακ hk hkval'
        have : IsOrdinal β := IsOrdinal.of_mem hβ
        have hβA : (β : V) ∈ A := IsTransitive.mem_trans ‹IsTransitive A› hβ hαA
        have hβκ : β ∈ κ := IsOrdinal.toIsTransitive.mem_trans hβ hακ
        obtain ⟨m, hm, hmv⟩ := ih (IsOrdinal.toOrdinal β) hβ hβκ
        have hcol : (ultraCollapse P U A) ‘ k = (ultraCollapse P U A) ‘ (constantGraph P β) :=
          (ultraCollapse_eq_iff hAC hU hcomp hω hA hk
            (constantGraph_mem_ultraFunctions hβA)).mpr hβeq
        have hz' : z = β := by
          rw [← hkval, hcol, ← value_ultraEmbedding (P := P) (U := U) hβA, ← hm]
          exact hmv
        rw [hz']
        exact hβ
      · intro hz
        have : IsOrdinal z := IsOrdinal.of_mem hz
        have hzA : z ∈ A := IsTransitive.mem_trans ‹IsTransitive A› hz hαA
        have hzκ : z ∈ κ := IsOrdinal.toIsTransitive.mem_trans hz hακ
        obtain ⟨m, hm, hmv⟩ := ih (IsOrdinal.toOrdinal z) hz hzκ
        have hzval : (ultraCollapse P U A) ‘ (constantGraph P z) = z := by
          rw [← value_ultraEmbedding (P := P) (U := U) hzA, ← hm]
          exact hmv
        refine (mem_ultraCollapse_value hwf (constantGraph_mem_ultraFunctions hαA)).mpr
          ⟨constantGraph P z, constantGraph_mem_ultraFunctions hzA, ?_, hzval⟩
        exact (ultraMem_constantGraph_iff hU z (α : V)).mpr hz
    intro α hα
    obtain ⟨m, hm, hmv⟩ := key α hα
    rw [← hm]
    exact hmv
  intro α hα
  have : IsOrdinal α := IsOrdinal.of_mem hα
  exact hall (IsOrdinal.toOrdinal α) hα

end ZFVP
