import ZFVP.ModelTheory.ForcingSequenceEvaluationGraph
import ZFVP.ModelTheory.ForcingModelGeneric
import ZFVP.ModelTheory.GenericInternalForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def GenericTableMeets (G T q b : V) : Prop := ∃ p ∈ G, ⟨q, ⟨b, p⟩ₖ⟩ₖ ∈ T

instance genericTableMeets_definable : ℒₛₑₜ-relation₄[V] GenericTableMeets := by
  unfold GenericTableMeets
  definability

/-- A predicate internal to the generic quotient, with all semantic parameters represented by sets. -/
def InternalGenericTruthAt (X E S G T q : V) : Prop := ∀ b ∈ S, domain b = kpair.π₁ q →
  (MembershipSatisfies X (kpair.π₁ q) (kpair.π₂ q) (E ‘ b) ↔ GenericTableMeets G T q b)

instance internalGenericTruthAt_definable (X E S G T : V) : ℒₛₑₜ-predicate[V] (InternalGenericTruthAt X E S G T) := by
  unfold InternalGenericTruthAt
  definability

namespace ForcingContext

theorem genericTableMeets_checked (A : ForcingContext V) {D n φ b : V}
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ D ^ n) :
    GenericTableMeets A.genericSet (A.check (internalForcingTruthTable A.P A.R D)) (A.check ⟨n, φ⟩ₖ) (A.check b) ↔
      GenericMeets A.G (internalForcingSet A.P A.R D n φ b) := by
  constructor
  · rintro ⟨p, hp, ht⟩
    obtain ⟨q, hq, rfl⟩ := (A.mem_genericSet_iff p).mp hp
    rw [← A.check_kpair, ← A.check_kpair, A.check_mem_iff] at ht
    exact ⟨q, hq, (mem_internalForcingSet hφ).mpr
      ((internalForcingTruthTable_lookup hφ hb (A.generic.1.1 q hq)).mp ht)⟩
  · rintro ⟨p, hp, ht⟩
    refine ⟨A.check p, (A.check_mem_genericSet_iff p).mpr hp, ?_⟩
    rw [← A.check_kpair, ← A.check_kpair, A.check_mem_iff]
    exact (internalForcingTruthTable_lookup hφ hb (A.generic.1.1 p hp)).mpr ((mem_internalForcingSet hφ).mp ht)

theorem internalGenericTruthAt_checked (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) (X : A.Model) {n φ : V} (hφ : IsMembershipFormulaCode n φ) :
    InternalGenericTruthAt X (A.sequenceEvaluationGraph D hD) (A.check (finiteSequences D)) A.genericSet
      (A.check (internalForcingTruthTable A.P A.R D)) (A.check ⟨n, φ⟩ₖ) ↔
    ∀ b : V, ∀ hb : b ∈ D ^ n,
      (MembershipSatisfies X (A.check n) (A.check φ) (A.sequenceValue b (A.nameSequence_of_mem_function hD hb)) ↔
        GenericMeets A.G (internalForcingSet A.P A.R D n φ b)) := by
  have hq1 : kpair.π₁ (A.check ⟨n, φ⟩ₖ) = A.check n := by rw [A.check_kpair, kpair.π₁_kpair]
  have hq2 : kpair.π₂ (A.check ⟨n, φ⟩ₖ) = A.check φ := by rw [A.check_kpair, kpair.π₂_kpair]
  constructor
  · intro h b hb
    let := IsFunction.of_mem hb
    have hseq := (mem_finiteSequences_iff D b).mpr ⟨n, hφ.context, hb⟩
    have hd : domain (A.check b) = kpair.π₁ (A.check ⟨n, φ⟩ₖ) := by
      rw [A.check_domain, domain_eq_of_mem_function hb, hq1]
    have ht := h (A.check b) ((A.check_mem_iff _ _).mpr hseq) hd
    rwa [hq1, hq2, A.sequenceEvaluationGraph_value D hD hφ.context hb,
      A.genericTableMeets_checked hφ hb] at ht
  · intro h b hb hd
    obtain ⟨c, hc, rfl⟩ := (A.mem_check_iff (finiteSequences D) b).mp hb
    obtain ⟨m, hm, hcm⟩ := (mem_finiteSequences_iff D c).mp hc
    let := IsFunction.of_mem hcm
    rw [A.check_domain, domain_eq_of_mem_function hcm, hq1] at hd
    obtain rfl := (A.check_eq_iff m n).mp hd
    change MembershipSatisfies X (kpair.π₁ (A.check ⟨m, φ⟩ₖ)) (kpair.π₂ (A.check ⟨m, φ⟩ₖ))
      ((A.sequenceEvaluationGraph D hD) ‘ (A.check c)) ↔ _
    rw [hq1, hq2, A.sequenceEvaluationGraph_value D hD hm hcm, A.genericTableMeets_checked hφ hcm]
    exact h c hcm

end ForcingContext
end ZFVP
