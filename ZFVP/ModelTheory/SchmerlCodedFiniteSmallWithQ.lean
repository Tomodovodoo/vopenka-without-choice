import ZFVP.ModelTheory.SchmerlCodedDeadEndSemantics
import ZFVP.ModelTheory.SchmerlInfinitaryDeadEndWithQ

/-! The ambient countable traces give the finite-small clause and remain
countable after every membership end extension. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation
open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W)

theorem representedMemberTrace_mem (a x : W) :
    (R.equiv x).val ∈ codedMemberTrace R.code (R.equiv a).val ↔ x ∈ a := by
  rw [mem_codedMemberTrace]
  have hx : (R.equiv x).val ∈ structureDomain R.code := by
    simpa only [code, binaryRelationStructureCode_domain] using (R.equiv x).property
  rw [and_iff_right hx]
  exact (R.codedBinary_iff (“x a. x ∈ a” : SetTheorySemisentence 2) x a).trans (by simp)

theorem representedMemberTrace_countable (hsmall : IsCodedFinSmall R.code) {a : W}
    (ha : IsInternallyFinite a) : IsInternallyCountable (codedMemberTrace R.code (R.equiv a).val) := by
  apply hsmall _ (by simpa only [code, binaryRelationStructureCode_domain] using (R.equiv a).property)
  exact (R.codedUnary_iff internallyFiniteFormula a).mpr (by simpa using ha)

theorem representedQ_finiteSmall (hsmall : IsCodedFinSmall R.code) (a : W)
    (ha : IsInternallyFinite a) : ¬R.representedQ {x | x ∈ a} := by
  intro hQ
  exact hQ ⟨codedMemberTrace R.code (R.equiv a).val, R.representedMemberTrace_countable hsmall ha,
    fun x hx ↦ (R.representedMemberTrace_mem a x).mpr hx⟩

variable {U : Type*} [SetStructure U] [Nonempty U] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem endExtension_representedQ_finiteSmall (j : MembershipEndExtension V U)
    (hsmall : IsCodedFinSmall R.code) (a : W) (ha : IsInternallyFinite a) :
    ¬(R.endExtension j).representedQ {x | x ∈ a} := by
  intro hQ
  apply hQ
  refine ⟨j (codedMemberTrace R.code (R.equiv a).val), ?_, ?_⟩
  · simpa only [IsInternallyCountable, j.map_omega] using
      j.map_cardLE (R.representedMemberTrace_countable hsmall ha)
  · intro x hx
    rw [R.endExtension_equiv_val, j.mem_iff]
    exact (R.representedMemberTrace_mem a x).mpr hx

end ZFVP.BinaryRelationRepresentation
