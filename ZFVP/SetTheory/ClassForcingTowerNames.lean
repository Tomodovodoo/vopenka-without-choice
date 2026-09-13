import ZFVP.SetTheory.ClassForcingTowerStages
import ZFVP.SetTheory.ForcingNames

/-! Names for the proper-class direct limit are internal sets of pairs.
Replacement bounds the stages occurring anywhere in their hereditary
name support. Every such name is therefore a name for a bounded set
forcing, whose final stage is densely embedded. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def classNameConditionSupport (τ : V) : V :=
  ⋃ˢ repl range (by definability) (nameClosure τ)

instance classNameConditionSupport_definable : ℒₛₑₜ-function₁[V] classNameConditionSupport := by
  unfold classNameConditionSupport
  definability

theorem mem_classNameConditionSupport (τ c : V) : c ∈ classNameConditionSupport τ ↔
    ∃ σ ∈ nameClosure τ, ∃ υ : V, ⟨υ, c⟩ₖ ∈ σ := by
  simp only [classNameConditionSupport, mem_sUnion_iff]
  constructor
  · rintro ⟨B, hB, hc⟩
    obtain ⟨σ, hσ, rfl⟩ := (repl_spec _).mp hB
    obtain ⟨υ, hυ⟩ := mem_range_iff.mp hc
    exact ⟨σ, hσ, υ, hυ⟩
  · rintro ⟨σ, hσ, υ, hυ⟩
    exact ⟨_, (repl_spec _).mpr ⟨σ, hσ, rfl⟩, mem_range_of_kpair_mem hυ⟩

theorem classNameConditionSupport_mono {σ τ : V} (hσ : σ ∈ nameClosure τ) :
    classNameConditionSupport σ ⊆ classNameConditionSupport τ := by
  intro c hc
  obtain ⟨υ, hυ, ν, hν⟩ := (mem_classNameConditionSupport _ _).mp hc
  exact (mem_classNameConditionSupport _ _).mpr
    ⟨υ, nameClosure_mem_mono hσ υ hυ, ν, hν⟩

noncomputable def taggedNameStageBound (τ : V) : V :=
  ⋃ˢ repl (fun c ↦ succ (kpair.π₁ c)) (by definability) (classNameConditionSupport τ)

instance taggedNameStageBound_definable : ℒₛₑₜ-function₁[V] taggedNameStageBound := by
  unfold taggedNameStageBound
  definability

theorem support_index_mem_taggedNameStageBound {τ c : V}
    (hc : c ∈ classNameConditionSupport τ) : kpair.π₁ c ∈ taggedNameStageBound τ :=
  mem_sUnion_iff.mpr ⟨_, (repl_spec _).mpr ⟨c, hc, rfl⟩, mem_succ_self _⟩

theorem taggedNameStageBound_mono {σ τ : V} (hσ : σ ∈ nameClosure τ) :
    taggedNameStageBound σ ⊆ taggedNameStageBound τ := by
  intro β hβ
  obtain ⟨B, hB, hβB⟩ := mem_sUnion_iff.mp hβ
  obtain ⟨c, hc, rfl⟩ := (repl_spec _).mp hB
  exact mem_sUnion_iff.mpr ⟨_, (repl_spec _).mpr
    ⟨c, classNameConditionSupport_mono hσ c hc, rfl⟩, hβB⟩

namespace DefinableForcingTower

variable (T : DefinableForcingTower V)

def IsName (τ : V) : Prop :=
  ∀ σ ∈ nameClosure τ, ∀ z ∈ σ,
    ∃ υ c : V, T.Condition c ∧ z = ⟨υ, c⟩ₖ

instance isName_definable : ℒₛₑₜ-predicate T.IsName := by
  unfold IsName
  definability

theorem IsName.conditionSupport {τ : V} (hτ : T.IsName τ)
    {c : V} (hc : c ∈ classNameConditionSupport τ) : T.Condition c := by
  obtain ⟨σ, hσ, υ, hυ⟩ := (mem_classNameConditionSupport _ _).mp hc
  obtain ⟨ν, d, hd, he⟩ := hτ σ hσ _ hυ
  have hcd := (kpair_iff.mp he).2
  exact hcd ▸ hd

theorem IsName.subname {τ σ : V} (hτ : T.IsName τ) (hσ : σ ∈ nameClosure τ) :
    T.IsName σ := fun υ hυ ↦ hτ υ (nameClosure_mem_mono hσ υ hυ)

theorem IsName.bound_ordinal {τ : V} (hτ : T.IsName τ) :
    IsOrdinal (taggedNameStageBound τ) := IsOrdinal.sUnion (by
  intro B hB
  obtain ⟨c, hc, rfl⟩ := (repl_spec _).mp hB
  let := (T.condition_spec (hτ.conditionSupport T hc)).1
  infer_instance)

theorem IsName.bounded {τ : V} (hτ : T.IsName τ) :
    IsForcingName (T.boundedConditions (taggedNameStageBound τ)) τ := by
  let := hτ.bound_ordinal T
  intro σ hσ z hz
  obtain ⟨υ, c, hc, rfl⟩ := hτ σ hσ z hz
  have hsupport : c ∈ classNameConditionSupport τ :=
    (mem_classNameConditionSupport _ _).mpr ⟨σ, hσ, υ, hz⟩
  have hs := T.condition_spec hc
  let := hs.1
  have hbound := support_index_mem_taggedNameStageBound hsupport
  refine ⟨υ, c, ?_, rfl⟩
  rw [hs.2.2]
  exact T.tagged_mem_boundedConditions
    (IsOrdinal.toIsTransitive.transitive _ hbound) hs.2.1

theorem isName_of_bounded {τ θ : V} [IsOrdinal θ]
    (hτ : IsForcingName (T.boundedConditions θ) τ) : T.IsName τ := by
  intro σ hσ z hz
  obtain ⟨υ, c, hc, he⟩ := hτ σ hσ z hz
  exact ⟨υ, c, T.boundedConditions_condition hc, he⟩

theorem isName_iff_bounded (τ : V) : T.IsName τ ↔
    ∃ θ : V, IsOrdinal θ ∧ IsForcingName (T.boundedConditions θ) τ := by
  constructor
  · intro hτ
    exact ⟨taggedNameStageBound τ, hτ.bound_ordinal T, hτ.bounded T⟩
  · rintro ⟨θ, hθ, hτ⟩
    let := hθ
    exact T.isName_of_bounded hτ

theorem IsName.setStage_reduction {τ : V} (hτ : T.IsName τ) :
    ∃ θ : V, IsOrdinal θ ∧
      IsForcingName (T.boundedConditions θ) τ ∧
      IsForcingPreorder (T.boundedConditions θ) (T.boundedOrder θ) ∧
      IsForcingTop (T.boundedConditions θ) (T.boundedOrder θ) T.one ∧
      IsDenseEmbedding (T.P θ) (T.R θ) (T.boundedConditions θ)
        (T.boundedOrder θ) (T.stageEmbedding θ) := by
  let := hτ.bound_ordinal T
  exact ⟨taggedNameStageBound τ, inferInstance, hτ.bounded T,
    T.bounded_preorder _, T.bounded_top _, T.stageEmbedding_dense _⟩

theorem conditions_proper (C : V) : ∃ c : V, T.Condition c ∧ c ∉ C := by
  let i := rank C
  let := rank_ordinal C
  refine ⟨⟨i, T.top i⟩ₖ,
    (T.condition_pair _ _).mpr ⟨inferInstance, (T.top_spec i inferInstance).1⟩, ?_⟩
  intro hc
  have hi : rank i ∈ rank C :=
    IsOrdinal.toIsTransitive.mem_trans (rank_kpair_left_lt i (T.top i)) (rank_mem hc)
  rw [rank_of_ordinal i] at hi
  exact mem_irrefl i hi

end DefinableForcingTower
end ZFVP
