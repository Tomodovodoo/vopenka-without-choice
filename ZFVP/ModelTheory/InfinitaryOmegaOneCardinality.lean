import ZFVP.ModelTheory.InfinitaryOmegaOneStandardTruth

namespace ZFVP.Infinitary
open LO LO.FirstOrder Cardinal
universe u
namespace WeakDirectedChain
variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}
  (C : WeakDirectedChain.{u,0,0} OmegaOne S)

/-- The constructed omega-one limit has size at most aleph-one. -/
theorem mk_limit_le_alephOne : Cardinal.mk C.Limit ≤ Cardinal.aleph 1 := by
  have hq : Cardinal.mk C.Limit ≤ Cardinal.mk C.Point := Cardinal.mk_quotient_le
  have hs : Cardinal.mk C.Point = Cardinal.sum (fun i : OmegaOne ↦ Cardinal.mk (C.model i).Domain) :=
    Cardinal.mk_sigma _
  have hc : Cardinal.sum (fun i : OmegaOne ↦ Cardinal.mk (C.model i).Domain) ≤
      Cardinal.sum (fun _ : OmegaOne ↦ Cardinal.aleph0) :=
    Cardinal.sum_le_sum _ _ (fun _ ↦ Cardinal.mk_le_aleph0)
  rw [Cardinal.sum_const', mk_omegaOne,
    Cardinal.mul_eq_left (Cardinal.aleph0_le_aleph 1) (Cardinal.aleph0_le_aleph 1)
      Cardinal.aleph0_ne_zero] at hc
  exact hq.trans (hs.le.trans hc)

/-- A positive fragment fiber forces the constructed limit to have exactly
aleph-one elements once the chain has the proved growth property. -/
theorem mk_limit_eq_alephOne_of_positive (hgrowth : C.LargeFiberSuccessorGrowth)
    {n} (φ : Formula L (n + 1)) (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S)
    {i} (b : Fin n → (C.model i).Domain)
    (hq : Formula.WeakEval (C.model i).Q (.q φ) b) :
    Cardinal.mk C.Limit = Cardinal.aleph 1 := by
  apply le_antisymm C.mk_limit_le_alephOne
  by_contra h
  have : Countable C.Limit := Cardinal.mk_le_aleph0_iff.mp
    (Cardinal.lt_aleph_one_iff.mp (lt_of_not_ge h))
  exact C.large_limitFiber_not_countable hgrowth hφ b hq (Set.to_countable _)

end WeakDirectedChain
end ZFVP.Infinitary
