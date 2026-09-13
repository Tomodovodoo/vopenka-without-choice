import ZFVP.ModelTheory.InternalBinaryQuotient
import ZFVP.Syntax.BinaryRelationInternalSemantics
import ZFVP.Syntax.MembershipSwap

/-! Raw atomic syntax descends through the actual quotient, including the
primitive logical equality token and the membership language's equality symbol. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def DirectNameAtomicHolds (E R n b r args : V) : Prop := ∃ i ∈ n, ∃ j ∈ n,
  args = boundPairArguments i j ∧
    (((r = equalityToken ∨ r = relationToken (0 : V)) ∧ ⟨b ‘ i, b ‘ j⟩ₖ ∈ E) ∨
      (r = relationToken (1 : V) ∧ ⟨b ‘ i, b ‘ j⟩ₖ ∈ R))

theorem quotientAssignment_mem {D E n b : V} (hb : b ∈ D ^ n) :
    compose b (internalQuotientProjection D E) ∈ internalQuotientCarrier D E ^ n :=
  compose_function hb (internalQuotientProjection_mem D E)

theorem quotientAssignment_value {D E n b i : V} (hb : b ∈ D ^ n) (hi : i ∈ n) :
    (compose b (internalQuotientProjection D E)) ‘ i = internalEquivalenceClass D E (b ‘ i) := by
  rw [value_compose_of_mem_function hb (internalQuotientProjection_mem D E) hi,
    internalQuotientProjection_value (function_value_mem hb hi)]

theorem quotientAssignment_prepend {D E n b x : V} (hn : n ∈ (ω : V)) (hb : b ∈ D ^ n) (hx : x ∈ D) :
    compose (assignmentPrepend n b x) (internalQuotientProjection D E) =
      assignmentPrepend n (compose b (internalQuotientProjection D E)) (internalEquivalenceClass D E x) := by
  rw [compose_assignmentPrepend hn hb (internalQuotientProjection_mem D E) hx,
    internalQuotientProjection_value hx]

theorem directNameAtomicHolds_quotient {D E R n b r args : V} (hE : IsInternalSetoid D E)
    (hR : IsInternalRelationCongruence D E R) (hn : n ∈ (ω : V)) (hb : b ∈ D ^ n)
    (ha : IsMembershipAtomicArguments n r args) :
    DirectNameAtomicHolds E R n b r args ↔
      AtomicHolds membershipLanguageCode ∅ (internalQuotientStructure D E R) ∅ n
        (compose b (internalQuotientProjection D E)) r args := by
  let Q := internalQuotientCarrier D E
  let S := internalQuotientEdges D E R
  let c := compose b (internalQuotientProjection D E)
  have hc : c ∈ Q ^ n := quotientAssignment_mem hb
  have heq {i j : V} (hi : i ∈ n) (hj : j ∈ n) :
      c ‘ i = c ‘ j ↔ ⟨b ‘ i, b ‘ j⟩ₖ ∈ E := by
    dsimp [c]
    rw [quotientAssignment_value hb hi, quotientAssignment_value hb hj]
    exact hE.classes_eq_iff (function_value_mem hb hi) (function_value_mem hb hj)
  have hmem {i j : V} (hi : i ∈ n) (hj : j ∈ n) :
      ⟨c ‘ i, c ‘ j⟩ₖ ∈ S ↔ ⟨b ‘ i, b ‘ j⟩ₖ ∈ R := by
    dsimp [c, S]
    rw [quotientAssignment_value hb hi, quotientAssignment_value hb hj]
    exact hE.quotient_edge_iff hR (function_value_mem hb hi) (function_value_mem hb hj)
  change _ ↔ AtomicHolds membershipLanguageCode ∅ (binaryRelationStructureCode Q S) ∅ n c r args
  constructor
  · rintro ⟨i, hi, j, hj, rfl, hh⟩
    rcases hh with ⟨hr, he⟩ | ⟨rfl, hm⟩
    · rcases hr with rfl | rfl
      · exact (binaryAtomic_logicalEquality hn hi hj Q S c).mpr ((heq hi hj).mpr he)
      · exact (binaryAtomic_relationEquality hn hi hj hc).mpr ((heq hi hj).mpr he)
    · exact (binaryAtomic_membership hn hi hj hc).mpr ((hmem hi hj).mpr hm)
  · intro hh
    obtain ⟨hr, i, hi, j, hj, rfl⟩ := ha
    refine ⟨i, hi, j, hj, rfl, ?_⟩
    rcases hr with rfl | rfl | rfl
    · exact Or.inl ⟨Or.inl rfl, (heq hi hj).mp ((binaryAtomic_logicalEquality hn hi hj Q S c).mp hh)⟩
    · exact Or.inl ⟨Or.inr rfl, (heq hi hj).mp ((binaryAtomic_relationEquality hn hi hj hc).mp hh)⟩
    · exact Or.inr ⟨rfl, (hmem hi hj).mp ((binaryAtomic_membership hn hi hj hc).mp hh)⟩

end ZFVP
