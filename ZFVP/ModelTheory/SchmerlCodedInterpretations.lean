import ZFVP.ModelTheory.SchmerlCodedRubinSource
import ZFVP.ModelTheory.SchmerlInfinitaryClassSentence

/-! Internal sets interpreting the ordinal order and Keisler class tree of
an arbitrary coded binary model. Membership remains the represented relation. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local irreducible] codedSatisfies codedUnary codedBinary

noncomputable def codedUnarySet (M φ : V) : V := {x ∈ structureDomain M ; codedUnary M φ x}

theorem mem_codedUnarySet (M φ x : V) :
    x ∈ codedUnarySet M φ ↔ x ∈ structureDomain M ∧ codedUnary M φ x := mem_sep_iff

instance codedUnarySet_definable : ℒₛₑₜ-function₂[V] codedUnarySet := by
  have h : ℒₛₑₜ-relation₃[V] (fun P M φ ↦ ∀ x, x ∈ P ↔ x ∈ structureDomain M ∧ codedUnary M φ x) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_codedUnarySet]
  rfl

noncomputable def codedBinaryOn (M φ A B : V) : V :=
  {p ∈ A ×ˢ B ; codedBinary M φ (kpair.π₁ p) (kpair.π₂ p)}

theorem pair_mem_codedBinaryOn (M φ A B x y : V) :
    ⟨x, y⟩ₖ ∈ codedBinaryOn M φ A B ↔ x ∈ A ∧ y ∈ B ∧ codedBinary M φ x y := by
  simp only [codedBinaryOn, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

instance codedBinaryOn_definable : ℒₛₑₜ-function₄[V] codedBinaryOn := by
  have h : ℒₛₑₜ-relation₅[V] (fun R M φ A B ↦ ∀ p, p ∈ R ↔
      p ∈ A ×ˢ B ∧ codedBinary M φ (kpair.π₁ p) (kpair.π₂ p)) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [codedBinaryOn, mem_sep_iff]
  rfl

theorem codedBinaryOn_subset (M φ A B : V) : codedBinaryOn M φ A B ⊆ A ×ˢ B :=
  fun _ hp ↦ (mem_sep_iff.mp hp).1

noncomputable def codedOrdinals (M : V) : V := codedUnarySet M (encodeMembershipFormula ordinalNodeFormula)

noncomputable def codedOrdinalOrder (M : V) : V :=
  codedBinaryOn M (encodeMembershipFormula ordinalOrderFormula) (codedOrdinals M) (codedOrdinals M)

noncomputable def codedClassNodes (M : V) : V := codedUnarySet M (encodeMembershipFormula classNodeFormula)

noncomputable def codedClassOrder (M : V) : V :=
  codedBinaryOn M (encodeMembershipFormula classOrderFormula) (codedClassNodes M) (codedClassNodes M)

noncomputable def codedClassLevels (M : V) : V :=
  codedBinaryOn M (encodeMembershipFormula classRankFormula) (codedClassNodes M) (codedOrdinals M)

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp
attribute [local irreducible] codedUnarySet codedBinaryOn

instance codedOrdinals_definable : ℒₛₑₜ-function₁[V] codedOrdinals := by unfold codedOrdinals; definability
instance codedOrdinalOrder_definable : ℒₛₑₜ-function₁[V] codedOrdinalOrder := by unfold codedOrdinalOrder; definability
instance codedClassNodes_definable : ℒₛₑₜ-function₁[V] codedClassNodes := by unfold codedClassNodes; definability
instance codedClassOrder_definable : ℒₛₑₜ-function₁[V] codedClassOrder := by unfold codedClassOrder; definability
instance codedClassLevels_definable : ℒₛₑₜ-function₁[V] codedClassLevels := by unfold codedClassLevels; definability

end ZFVP.Schmerl

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

variable {W : Type*} [SetStructure W] (R : BinaryRelationRepresentation (V := V) W)

theorem codedUnary_iff (φ : SetTheorySemisentence 1) (x : W) :
    codedUnary R.code (encodeMembershipFormula φ) (R.equiv x).val ↔ φ.Evalb ![x] := by
  have he : (fun i ↦ (R.equiv ((![x] : Fin 1 → W) i)).val) = ![(R.equiv x).val] := by
    funext i
    fin_cases i
    rfl
  have h := R.satisfies_iff φ ![x]
  rw [he] at h
  exact h

theorem codedBinary_iff (φ : SetTheorySemisentence 2) (x y : W) :
    codedBinary R.code (encodeMembershipFormula φ) (R.equiv x).val (R.equiv y).val ↔ φ.Evalb ![x, y] := by
  have he : (fun i ↦ (R.equiv ((![x, y] : Fin 2 → W) i)).val) = ![(R.equiv x).val, (R.equiv y).val] := by
    funext i
    fin_cases i <;> rfl
  have h := R.satisfies_iff φ ![x, y]
  rw [he] at h
  exact h

theorem mem_unarySet_iff (φ : SetTheorySemisentence 1) (x : W) :
    (R.equiv x).val ∈ codedUnarySet R.code (encodeMembershipFormula φ) ↔ φ.Evalb ![x] := by
  rw [mem_codedUnarySet, R.codedUnary_iff]
  exact and_iff_right (by simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain]
    using (R.equiv x).property)

theorem mem_unarySet_iff_exists (φ : SetTheorySemisentence 1) (p : V) :
    p ∈ codedUnarySet R.code (encodeMembershipFormula φ) ↔
      ∃ x : W, (R.equiv x).val = p ∧ φ.Evalb ![x] := by
  constructor
  · intro hp
    have hpD : p ∈ R.carrier := by
      simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using
        ((mem_codedUnarySet _ _ _).mp hp).1
    let x : W := R.equiv.symm ⟨p, hpD⟩
    have hx : (R.equiv x).val = p := congrArg Subtype.val (R.equiv.apply_symm_apply _)
    exact ⟨x, hx, (R.mem_unarySet_iff φ x).mp (hx.symm ▸ hp)⟩
  · rintro ⟨x, rfl, hx⟩
    exact (R.mem_unarySet_iff φ x).mpr hx

variable [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem mem_ordinals_iff (p : V) : p ∈ codedOrdinals R.code ↔
    ∃ α : SetTheory.Ordinal W, (R.equiv α.val).val = p := by
  rw [codedOrdinals, R.mem_unarySet_iff_exists]
  constructor
  · rintro ⟨x, hx, hα⟩
    have hα' : IsOrdinal x := by simpa [ordinalNodeFormula] using hα
    exact ⟨⟨x, hα'⟩, hx⟩
  · rintro ⟨α, rfl⟩
    exact ⟨α.val, rfl, by simpa [ordinalNodeFormula] using α.ordinal⟩

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem ordinal_mem (α : SetTheory.Ordinal W) : (R.equiv α.val).val ∈ codedOrdinals R.code :=
  (R.mem_ordinals_iff _).mpr ⟨α, rfl⟩

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem ordinalOrder_iff (α β : SetTheory.Ordinal W) :
    ⟨(R.equiv α.val).val, (R.equiv β.val).val⟩ₖ ∈ codedOrdinalOrder R.code ↔ α ≤ β := by
  rw [codedOrdinalOrder, pair_mem_codedBinaryOn,
    and_iff_right (R.ordinal_mem α), and_iff_right (R.ordinal_mem β), R.codedBinary_iff]
  exact eval_ordinalOrderFormula α β

theorem mem_classNodes_iff (p : V) : p ∈ codedClassNodes R.code ↔
    ∃ t : ClassTreeNode W, (R.equiv t.code).val = p := by
  rw [codedClassNodes, R.mem_unarySet_iff_exists]
  constructor
  · rintro ⟨x, hx, ht⟩
    obtain ⟨t, rfl⟩ := (eval_classNodeFormula x).mp ht
    exact ⟨t, hx⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t.code, rfl, (eval_classNodeFormula _).mpr ⟨t, rfl⟩⟩

theorem classNode_mem (t : ClassTreeNode W) : (R.equiv t.code).val ∈ codedClassNodes R.code :=
  (R.mem_classNodes_iff _).mpr ⟨t, rfl⟩

theorem classOrder_iff (s t : ClassTreeNode W) :
    ⟨(R.equiv s.code).val, (R.equiv t.code).val⟩ₖ ∈ codedClassOrder R.code ↔ s ≤ t := by
  rw [codedClassOrder, pair_mem_codedBinaryOn, and_iff_right (R.classNode_mem s),
    and_iff_right (R.classNode_mem t), R.codedBinary_iff]
  exact eval_classOrderFormula s t

theorem classLevels_iff (t : ClassTreeNode W) (α : SetTheory.Ordinal W) :
    ⟨(R.equiv t.code).val, (R.equiv α.val).val⟩ₖ ∈ codedClassLevels R.code ↔ α = t.level := by
  rw [codedClassLevels, pair_mem_codedBinaryOn, and_iff_right (R.classNode_mem t),
    and_iff_right (R.ordinal_mem α), R.codedBinary_iff, eval_classRankFormula]
  exact ⟨SetTheory.Ordinal.ext, fun he ↦ congrArg SetTheory.Ordinal.val he⟩

end ZFVP.BinaryRelationRepresentation
