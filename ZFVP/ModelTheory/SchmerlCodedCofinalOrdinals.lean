import ZFVP.ModelTheory.SchmerlCodedTreeStructure

/-! The ordinal chain is obtained from the actual coded Rubin clause. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem codedUnarySet_isCodedDefinable (M : V) (φ : SetTheorySemisentence 1) :
    IsCodedDefinableSet M (codedUnarySet M (encodeMembershipFormula φ)) := by
  refine ⟨fun x hx ↦ ((mem_codedUnarySet _ _ _).mp hx).1, 0, by simp,
    encodeMembershipFormula φ, ?_, ∅, by simp [mem_function_iff, zero_def], ?_⟩
  · simpa only [num_succ_def, cast_zero_def] using encodeMembershipFormula_mem (V := V) φ
  · intro x hx
    rw [mem_codedUnarySet, and_iff_right hx]
    rfl

def ordinalPosetFormula : SetTheorySemisentence 2 :=
  f“x y. !ordinalNodeFormula x ∧ !ordinalNodeFormula y ∧ !ordinalOrderFormula x y”

def classPosetFormula : SetTheorySemisentence 2 :=
  f“x y. !classNodeFormula x ∧ !classNodeFormula y ∧ !classOrderFormula x y”

end ZFVP.Schmerl

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] (R : BinaryRelationRepresentation (V := V) W)

theorem relation_definable_of_formula {A : V} (φ : SetTheorySemisentence 2)
    (hA : A ⊆ R.carrier ×ˢ R.carrier)
    (hφ : ∀ x y : W, ⟨(R.equiv x).val, (R.equiv y).val⟩ₖ ∈ A ↔ φ.Evalb ![x, y]) :
    IsCodedDefinableRelation R.code A := by
  refine ⟨by simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using hA,
    0, by simp, encodeMembershipFormula φ, ?_, ∅, by simp [mem_function_iff, zero_def], ?_⟩
  · simpa only [num_succ_def, cast_zero_def] using encodeMembershipFormula_mem (V := V) φ
  · intro x hx y hy
    have hxD : x ∈ R.carrier := by simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using hx
    have hyD : y ∈ R.carrier := by simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using hy
    let a : W := R.equiv.symm ⟨x, hxD⟩
    let b : W := R.equiv.symm ⟨y, hyD⟩
    have ha : (R.equiv a).val = x := congrArg Subtype.val (R.equiv.apply_symm_apply _)
    have hb : (R.equiv b).val = y := congrArg Subtype.val (R.equiv.apply_symm_apply _)
    have h := (hφ a b).trans (R.codedBinary_iff φ a b).symm
    rw [ha, hb] at h
    exact h

theorem ordinalOrder_isCodedDefinable : IsCodedDefinableRelation R.code (codedOrdinalOrder R.code) := by
  apply R.relation_definable_of_formula ordinalPosetFormula
  · intro p hp
    have h := codedBinaryOn_subset R.code (encodeMembershipFormula ordinalOrderFormula)
      (codedOrdinals R.code) (codedOrdinals R.code) p hp
    rcases mem_prod_iff.mp h with ⟨x, hx, y, hy, rfl⟩
    exact kpair_mem_iff.mpr ⟨by
      simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using
        ((mem_codedUnarySet _ _ _).mp hx).1, by
      simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using
        ((mem_codedUnarySet _ _ _).mp hy).1⟩
  · intro x y
    rw [codedOrdinalOrder, pair_mem_codedBinaryOn, codedOrdinals, R.mem_unarySet_iff,
      R.mem_unarySet_iff, R.codedBinary_iff]
    simp [ordinalPosetFormula]

theorem classOrder_isCodedDefinable : IsCodedDefinableRelation R.code (codedClassOrder R.code) := by
  apply R.relation_definable_of_formula classPosetFormula
  · intro p hp
    have h := codedBinaryOn_subset R.code (encodeMembershipFormula classOrderFormula)
      (codedClassNodes R.code) (codedClassNodes R.code) p hp
    rcases mem_prod_iff.mp h with ⟨x, hx, y, hy, rfl⟩
    exact kpair_mem_iff.mpr ⟨by
      simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using
        ((mem_codedUnarySet _ _ _).mp hx).1, by
      simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using
        ((mem_codedUnarySet _ _ _).mp hy).1⟩
  · intro x y
    rw [codedClassOrder, pair_mem_codedBinaryOn, codedClassNodes, R.mem_unarySet_iff,
      R.mem_unarySet_iff, R.codedBinary_iff]
    simp [classPosetFormula]

variable [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_cofinal_ordinal_chain {κ : V} (h : IsCodedRubin R.code κ) :
    ∃ c, IsInternalCofinalStrictChain κ (codedOrdinals R.code) (codedOrdinalOrder R.code) c :=
  h.1 _ _ (codedUnarySet_isCodedDefinable R.code ordinalNodeFormula)
    R.ordinalOrder_isCodedDefinable R.ordinalOrder_poset R.ordinals_directedNoMax

end ZFVP.BinaryRelationRepresentation
