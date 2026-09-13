import ZFVP.ModelTheory.ForcingRankTruth
import ZFVP.ModelTheory.WoodinSparseEndpointTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A : ForcingContext V) {δ : V} [IsOrdinal δ]

/-- Standard-formula rank truth uses actual low-name coverage, without requiring
that the endpoint forcing belong to the rank. -/
theorem rankName_formula_truth_of_coverage
    (hcov : ∀ x ∈ hierarchy (A.check δ), ∃ τ : ForcingName A.P,
      τ.val ∈ hierarchy δ ∧ x = A.ofName τ)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → ForcingName A.P)
    (hv : ∀ i, (v i).val ∈ hierarchy δ) :
    φ.Evalb (show Fin n → SetDomain (hierarchy (A.check δ)) from fun i ↦
      ⟨A.ofName (v i), A.ofName_mem_checked_hierarchy _ (hv i)⟩) ↔
      GenericMeets A.G (classForcingFormula A.P A.R (IsLowRankForcingName A.P δ)
        (by definability) φ (standardTuple (fun i ↦ (v i).val))) := by
  let e : A.RankNameModel δ ≃ SetDomain (hierarchy (A.check δ)) := {
    toFun := fun x ↦ ⟨x.val, by
      obtain ⟨τ, hτ, he⟩ := x.property
      rw [he]
      exact A.ofName_mem_checked_hierarchy _ hτ.1⟩
    invFun := fun x ↦ ⟨x.val, by
      obtain ⟨τ, hτ, he⟩ := hcov x.val x.property
      exact ⟨τ.val, ⟨hτ, τ.property⟩, he⟩⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }
  let j := ElementaryMap.ofMembershipIso e (fun _ _ ↦ Iff.rfl)
  let w : Fin n → {τ : V // IsLowRankForcingName A.P δ τ} :=
    fun i ↦ ⟨(v i).val, hv i, (v i).property⟩
  let a := ClassForcingQuotient.assignment A.P A.R A.G A.order A.generic.1
    (IsLowRankForcingName A.P δ) (fun _ h ↦ h.2) w
  have he := j.elementary φ a Empty.elim
  have hz : j ∘ (Empty.elim : Empty → A.RankNameModel δ) = Empty.elim := by
    funext i
    exact Empty.elim i
  rw [hz] at he
  exact he.symm.trans (ClassForcingQuotient.formula_truth A.P A.R A.G A.order A.generic
    (IsLowRankForcingName A.P δ) (by definability) (fun _ h ↦ h.2) φ w)

end ForcingContext
end ZFVP
