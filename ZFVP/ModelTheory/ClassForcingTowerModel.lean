import ZFVP.ModelTheory.ClassForcingTowerBoundedModels
import ZFVP.ModelTheory.MembershipDirectedLimit

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower

variable (T : DefinableForcingTower V) {G : Set V}
  (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)

noncomputable def directedSystem : MembershipDirectedSystem (Ordinal V) where
  Model := (fun i ↦ (T.boundedContext hG i.val).Model)
  modelStructure := fun _ ↦ inferInstance
  inclusion := fun h ↦ T.boundedInclusion hG h
  identity := fun _ ↦ T.boundedInclusion_self hG
  composition := fun h k ↦ T.boundedInclusion_comp hG h k

/-- The proper-class extension, formed from the coherent set-stage
extensions. Its elements are equivalence classes of bounded names. -/
def ClassModel := (T.directedSystem hG).Limit

noncomputable instance classModelStructure : SetStructure (T.ClassModel hG) :=
  MembershipDirectedSystem.limitStructure _

instance classModelNonempty : Nonempty (T.ClassModel hG) := by
  exact ⟨(T.directedSystem hG).fromStage (IsOrdinal.toOrdinal (∅ : V))
    ((T.boundedContext hG ∅).check ∅)⟩

noncomputable def fromBoundedStage (i : V) [IsOrdinal i] :
    MembershipEndExtension (T.boundedContext hG i).Model (T.ClassModel hG) :=
  (T.directedSystem hG).stageEmbedding (IsOrdinal.toOrdinal i)

theorem fromBoundedStage_coherent {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j)
    (x : (T.boundedContext hG i).Model) :
    T.fromBoundedStage hG j (T.boundedInclusion hG hij x) = T.fromBoundedStage hG i x :=
  (T.directedSystem hG).fromStage_coherent
    (show IsOrdinal.toOrdinal i ≤ IsOrdinal.toOrdinal j from hij) x

abbrev Name := {τ : V // T.IsName τ}

noncomputable def ofClassName (τ : T.Name) : T.ClassModel hG := by
  have := τ.property.bound_ordinal T
  exact T.fromBoundedStage hG (taggedNameStageBound τ.val)
    ((T.boundedContext hG (taggedNameStageBound τ.val)).ofName ⟨τ.val, τ.property.bounded T⟩)

theorem ofClassName_at (τ : T.Name) {i : V} [IsOrdinal i]
    (hτ : IsForcingName (T.boundedConditions i) τ.val) :
    T.ofClassName hG τ =
      T.fromBoundedStage hG i ((T.boundedContext hG i).ofName ⟨τ.val, hτ⟩) := by
  have := τ.property.bound_ordinal T
  let b := taggedNameStageBound τ.val
  have : IsOrdinal (b ∪ i) := ordinal_union_ordinal _ _
  have hb : b ⊆ b ∪ i := subset_union_left _ _
  have hi : i ⊆ b ∪ i := subset_union_right _ _
  have hleft := T.fromBoundedStage_coherent hG hb
    ((T.boundedContext hG b).ofName ⟨τ.val, τ.property.bounded T⟩)
  have hright := T.fromBoundedStage_coherent hG hi
    ((T.boundedContext hG i).ofName ⟨τ.val, hτ⟩)
  have heleft := congrArg (T.fromBoundedStage hG (b ∪ i))
    (T.boundedInclusion_ofName hG hb ⟨τ.val, τ.property.bounded T⟩)
  have heright := congrArg (T.fromBoundedStage hG (b ∪ i))
    (T.boundedInclusion_ofName hG hi ⟨τ.val, hτ⟩)
  exact hleft.symm.trans (heleft.trans (heright.symm.trans hright))

theorem ofClassName_surjective : Function.Surjective (T.ofClassName hG) := by
  intro x
  obtain ⟨i, y, hy⟩ := (T.directedSystem hG).stage_cover x
  change (T.boundedContext hG i.val).Model at y
  change x = T.fromBoundedStage hG i.val y at hy
  obtain ⟨τ, hτ⟩ := (T.boundedContext hG i.val).ofName_surjective y
  change ForcingName (T.boundedConditions i.val) at τ
  let ν : T.Name := ⟨τ.val, T.isName_of_bounded (θ := i.val) τ.property⟩
  refine ⟨ν, ?_⟩
  have hν := T.ofClassName_at hG (i := i.val) ν τ.property
  have hτ' := congrArg (T.fromBoundedStage hG i.val) hτ
  exact hν.trans (hτ'.trans hy.symm)

theorem ofClassName_eq_iff_at (σ τ : T.Name) {i : V} [IsOrdinal i]
    (hσ : IsForcingName (T.boundedConditions i) σ.val)
    (hτ : IsForcingName (T.boundedConditions i) τ.val) :
    T.ofClassName hG σ = T.ofClassName hG τ ↔
      (T.boundedContext hG i).ofName ⟨σ.val, hσ⟩ =
        (T.boundedContext hG i).ofName ⟨τ.val, hτ⟩ := by
  rw [T.ofClassName_at hG σ hσ, T.ofClassName_at hG τ hτ]
  exact (T.fromBoundedStage hG i).injective.eq_iff

theorem ofClassName_mem_iff_at (σ τ : T.Name) {i : V} [IsOrdinal i]
    (hσ : IsForcingName (T.boundedConditions i) σ.val)
    (hτ : IsForcingName (T.boundedConditions i) τ.val) :
    T.ofClassName hG σ ∈ T.ofClassName hG τ ↔
      (T.boundedContext hG i).ofName ⟨σ.val, hσ⟩ ∈
        (T.boundedContext hG i).ofName ⟨τ.val, hτ⟩ := by
  rw [T.ofClassName_at hG σ hσ, T.ofClassName_at hG τ hτ]
  exact (T.fromBoundedStage hG i).mem_iff _ _

noncomputable def classCheck : MembershipEndExtension V (T.ClassModel hG) where
  toFun := fun x ↦ T.fromBoundedStage hG ∅ ((T.boundedContext hG ∅).check x)
  injective := (T.fromBoundedStage hG ∅).injective.comp
    (T.boundedContext hG ∅).checkEmbedding.injective
  mem_iff := fun x y ↦ ((T.fromBoundedStage hG ∅).mem_iff _ _).trans
    ((T.boundedContext hG ∅).check_mem_iff x y)
  endExtension := by
    intro x y hy
    obtain ⟨z, hz, rfl⟩ := (T.fromBoundedStage hG ∅).endExtension _ y hy
    obtain ⟨a, ha, rfl⟩ := (T.boundedContext hG ∅).checkEmbedding.endExtension x z hz
    exact ⟨a, ha, rfl⟩

theorem classCheck_at (i : V) [IsOrdinal i] (x : V) :
    T.classCheck hG x = T.fromBoundedStage hG i ((T.boundedContext hG i).check x) := by
  have he := T.fromBoundedStage_coherent hG (empty_subset i)
    ((T.boundedContext hG ∅).check x)
  exact he.symm.trans (congrArg (T.fromBoundedStage hG i)
    (T.boundedInclusion_check hG (empty_subset i) x))

end DefinableForcingTower
end ZFVP
