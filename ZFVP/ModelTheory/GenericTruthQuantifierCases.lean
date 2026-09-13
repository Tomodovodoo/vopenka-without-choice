import ZFVP.ModelTheory.GenericTruthBaseCases
import ZFVP.ModelTheory.ForcingSequencePrepend
import ZFVP.ModelTheory.DirectedElementaryUnion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem groundGenericTruth_quantifiers (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) {n φ : V} (hn : n ∈ (ω : V))
    (hφ : IsMembershipFormulaCode (succ n) φ) (ihφ : A.GroundGenericTruth D hD (succ n) φ) :
    A.GroundGenericTruth D hD n (allCode φ) ∧ A.GroundGenericTruth D hD n (existsCode φ) := by
  have hn' : A.check n ∈ (ω : A.Model) := A.checkEmbedding.natural_iff n |>.mpr hn
  have hφ' : IsMembershipFormulaCode (succ (A.check n)) (A.check φ) := by
    rw [← A.check_succ]
    exact (A.checkEmbedding.membershipFormulaCode_iff (succ n) φ).mpr hφ
  have hstep (b : V) (hb : b ∈ D ^ n) (x : V) (hx : x ∈ D) :
      MembershipSatisfies (range (A.evaluationGraph D hD)) (succ (A.check n)) (A.check φ)
        (assignmentPrepend (A.check n) (A.sequenceValue b (A.nameSequence_of_mem_function hD hb))
          (A.ofName ⟨x, hD x hx⟩)) ↔
      GenericMeets A.G (internalForcingSet A.P A.R D (succ n) φ (assignmentPrepend n b x)) := by
    have hh := ihφ (assignmentPrepend n b x) (assignmentPrepend_mem_function hn hb hx)
    rwa [A.check_succ, A.sequenceValue_prepend hD hn hb hx] at hh
  constructor
  · intro b hb
    have ht : A.check (allCode φ) = allCode (A.check φ) := A.checkEmbedding.map_allCode φ
    rw [ht, membershipSatisfies_all hn' hφ'.valid (A.sequenceValue_mem_evaluationRange hD hb),
      genericMeets_internalForcing_all A.order A.generic hn hφ hb]
    constructor
    · intro h x hx
      exact (hstep b hb x hx).mp (h _ ((A.mem_range_evaluationGraph_iff D hD _).mpr ⟨x, hx, rfl⟩))
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := (A.mem_range_evaluationGraph_iff D hD y).mp hy
      exact (hstep b hb x hx).mpr (h x hx)
  · intro b hb
    have ht : A.check (existsCode φ) = existsCode (A.check φ) := A.checkEmbedding.map_existsCode φ
    rw [ht, membershipSatisfies_exists hn' hφ'.valid (A.sequenceValue_mem_evaluationRange hD hb),
      genericMeets_internalForcing_exists A.order A.generic hn hφ hb]
    constructor
    · rintro ⟨y, hy, hh⟩
      obtain ⟨x, hx, rfl⟩ := (A.mem_range_evaluationGraph_iff D hD y).mp hy
      exact ⟨x, hx, (hstep b hb x hx).mp hh⟩
    · rintro ⟨x, hx, hh⟩
      exact ⟨A.ofName ⟨x, hD x hx⟩, (A.mem_range_evaluationGraph_iff D hD _).mpr ⟨x, hx, rfl⟩,
        (hstep b hb x hx).mpr hh⟩

end ForcingContext
end ZFVP
