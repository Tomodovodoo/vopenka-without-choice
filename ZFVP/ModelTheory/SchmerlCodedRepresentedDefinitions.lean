import ZFVP.ModelTheory.SchmerlCodedInterpretations
import ZFVP.Syntax.StandardOmegaMembershipSyntax
import ZFVP.SetTheory.EndExtensionRelations
import ZFVP.SetTheory.EndExtensionWellOrdering

/-! Coded original-language definitions give external finite-parameter
definitions when ambient omega is standard. A membership end extension presents
the same arbitrary binary model on its checked carrier. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W]
variable (R : BinaryRelationRepresentation (V := V) W)

theorem predicate_of_isCodedDefinableSet (hω : HasStandardOmega V) {A : V}
    (h : IsCodedDefinableSet R.code A) :
    ℒₛₑₜ-predicate[W] (fun x ↦ (R.equiv x).val ∈ A) := by
  obtain ⟨_, n, hn, φ, hφ, b, hb, hdef⟩ := h
  obtain ⟨k, rfl⟩ := hω n hn
  have hφ' : IsMembershipFormulaCode ((k + 1 : ℕ) : V) φ := by
    simpa only [IsMembershipFormulaCode, num_succ_def] using (mem_formulaSet_iff _ _ _ _).mp hφ
  obtain ⟨ψ, hψ⟩ := binary_formula_representable_of_standardOmega hω hφ'
  let a : Fin k → W := fun i ↦ R.equiv.symm ⟨b ‘ (i.val : V), by
    simpa only [code, binaryRelationStructureCode_domain] using function_value_mem hb (natCast_mem_of_lt i.isLt)⟩
  have ha (i : Fin k) : (R.equiv (a i)).val = b ‘ (i.val : V) :=
    congrArg (fun z : BinaryRelationDomain R.carrier R.relation ↦ z.val) (R.equiv.apply_symm_apply _)
  have he : b = standardTuple (fun i ↦ (R.equiv (a i)).val) := by
    apply function_eq_of_values hb
      (standardTuple_mem_function _ (fun i ↦ by
        simpa only [code, binaryRelationStructureCode_domain] using (R.equiv (a i)).property))
    intro i hi
    obtain ⟨j, rfl⟩ := (mem_natCast_iff i k).mp hi
    rw [value_standardTuple, ha]
  apply (finite_parameter_definition_iff _).mpr
  refine ⟨k, ψ, a, fun x ↦ ?_⟩
  have hh := hdef (R.equiv x).val (by
    simpa only [code, binaryRelationStructureCode_domain] using (R.equiv x).property)
  rw [he] at hh
  have hs := hψ R.carrier R.relation R.carrier_nonempty (R.equiv ∘ (x :> a))
  have ht : standardTuple (fun i ↦ ((R.equiv ∘ (x :> a)) i).val) =
      assignmentPrepend (k : V) (standardTuple (fun i ↦ (R.equiv (a i)).val)) (R.equiv x).val := rfl
  rw [ht] at hs
  have hs' : codedSatisfies R.code (succ (k : V)) φ
      (assignmentPrepend (k : V) (standardTuple (fun i ↦ (R.equiv (a i)).val)) (R.equiv x).val) ↔
      ψ.Evalb (R.equiv ∘ (x :> a)) := by
    simpa only [codedSatisfies, code, num_succ_def] using hs
  exact (R.evalb_iff ψ (x :> a)).trans (hs'.symm.trans hh.symm)

variable {U : Type*} [SetStructure U] [Nonempty U] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def binaryDomainEndEquiv (j : MembershipEndExtension V U) (D E : V) :
    BinaryRelationDomain D E ≃ BinaryRelationDomain (j D) (j E) :=
  Equiv.ofBijective (fun x ↦ ⟨j x.val, (j.mem_iff _ _).mpr x.property⟩) (by
    constructor
    · intro x y he
      exact Subtype.ext (j.injective (congrArg Subtype.val he))
    · intro y
      obtain ⟨x, hx, he⟩ := j.endExtension D y.val y.property
      exact ⟨⟨x, hx⟩, Subtype.ext he.symm⟩)

noncomputable def endExtension (j : MembershipEndExtension V U) : BinaryRelationRepresentation (V := U) W where
  carrier := j R.carrier
  relation := j R.relation
  carrier_nonempty := (j.nonempty_iff R.carrier).mpr R.carrier_nonempty
  relation_subset := by
    rw [← j.map_prod]
    exact (j.subset_iff _ _).mpr R.relation_subset
  equiv := R.equiv.trans (binaryDomainEndEquiv j R.carrier R.relation)
  mem_iff x y := by
    rw [R.mem_iff]
    change ⟨(R.equiv x).val, (R.equiv y).val⟩ₖ ∈ R.relation ↔
      ⟨j (R.equiv x).val, j (R.equiv y).val⟩ₖ ∈ j R.relation
    rw [← j.map_kpair]
    exact (j.mem_iff _ _).symm

omit [Nonempty W] in
@[simp] theorem endExtension_equiv_val (j : MembershipEndExtension V U) (x : W) :
    ((R.endExtension j).equiv x).val = j (R.equiv x).val := rfl

omit [Nonempty W] in
theorem endExtension_codedUnarySet (j : MembershipEndExtension V U) (φ : SetTheorySemisentence 1) :
    j (codedUnarySet R.code (encodeMembershipFormula φ)) =
      codedUnarySet (R.endExtension j).code (encodeMembershipFormula φ) := by
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := j.endExtension _ p hp
    obtain ⟨x, hx, hφ⟩ := (R.mem_unarySet_iff_exists φ q).mp hq
    exact ((R.endExtension j).mem_unarySet_iff_exists φ _).mpr ⟨x, congrArg j hx, hφ⟩
  · intro hp
    obtain ⟨x, hx, hφ⟩ := ((R.endExtension j).mem_unarySet_iff_exists φ p).mp hp
    rw [← hx, R.endExtension_equiv_val, j.mem_iff]
    exact (R.mem_unarySet_iff φ x).mpr hφ

omit [Nonempty W] in
theorem endExtension_codedBinary (j : MembershipEndExtension V U) (φ : SetTheorySemisentence 2)
    {x y : V} (hx : x ∈ R.carrier) (hy : y ∈ R.carrier) :
    codedBinary (R.endExtension j).code (encodeMembershipFormula φ) (j x) (j y) ↔
      codedBinary R.code (encodeMembershipFormula φ) x y := by
  obtain ⟨a, ha⟩ := R.equiv.surjective ⟨x, hx⟩
  obtain ⟨b, hb⟩ := R.equiv.surjective ⟨y, hy⟩
  have hax : (R.equiv a).val = x := congrArg Subtype.val ha
  have hby : (R.equiv b).val = y := congrArg Subtype.val hb
  rw [← hax, ← hby, ← R.endExtension_equiv_val j a, ← R.endExtension_equiv_val j b]
  exact ((R.endExtension j).codedBinary_iff φ a b).trans (R.codedBinary_iff φ a b).symm

omit [Nonempty W] in
theorem endExtension_codedBinaryOn (j : MembershipEndExtension V U) (φ : SetTheorySemisentence 2)
    {A B : V} (hA : A ⊆ R.carrier) (hB : B ⊆ R.carrier) :
    j (codedBinaryOn R.code (encodeMembershipFormula φ) A B) =
      codedBinaryOn (R.endExtension j).code (encodeMembershipFormula φ) (j A) (j B) := by
  have he := j.map_separation (A ×ˢ B)
    (fun p ↦ codedBinary R.code (encodeMembershipFormula φ) (kpair.π₁ p) (kpair.π₂ p))
    (fun p ↦ codedBinary (R.endExtension j).code (encodeMembershipFormula φ) (kpair.π₁ p) (kpair.π₂ p))
    (by definability) (by definability) (by
      intro p hp
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp hp
      simp only [kpair.π₁_kpair, kpair.π₂_kpair, j.map_kpair]
      exact (R.endExtension_codedBinary j φ (hA x hx) (hB y hy)).symm)
  simpa only [codedBinaryOn, j.map_prod] using he

end ZFVP.BinaryRelationRepresentation
