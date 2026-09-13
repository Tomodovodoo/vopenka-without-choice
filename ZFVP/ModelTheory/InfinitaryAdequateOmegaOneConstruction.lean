import ZFVP.ModelTheory.InfinitaryAdequateOmegaOneRecursion
import ZFVP.ModelTheory.InfinitaryCountableModelCode

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v

namespace CountableWeakModelCode
variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}

private theorem codeGrowth (hS : S.Countable) (c : CountableWeakModelCode L)
    (hc : c.asWeakModel.Adequate S) :
    ∃ d : CountableWeakModelCode L,
      ∃ e : AdequateOmegaOneNode.Map (S := S) c.asWeakModel d.asWeakModel,
        d.asWeakModel.Adequate S ∧ e.FreezesSmallFibers ∧ AdequateOmegaOneNode.Grows e := by
  obtain ⟨d, e, hd, hf, hg⟩ := c.exists_adequate_growth_block hc hS
  refine ⟨d, e, hd, hf, ?_⟩
  intro n φ hφ b hb
  exact hg φ hφ b hb

private theorem codeLimit (N : WeakModel.{u,0} L) (hN : N.Adequate S) :
    ∃ c : CountableWeakModelCode L,
      ∃ e : AdequateOmegaOneNode.Map (S := S) N c.asWeakModel,
        c.asWeakModel.Adequate S ∧ e.FreezesSmallFibers ∧ Function.Surjective e := by
  obtain ⟨c, e, hc, he, hf⟩ := exists_adequate_code N hN
  exact ⟨c, e, hc, hf, he.2⟩

/-- The omega-one recursion chooses solely from natural-carrier model codes.
Successors are actual adequate growth blocks. Countable limits are cofinal
omega limits followed by bijective recoding into the same fixed code type. -/
noncomputable def adequateOmegaOneChain (c : CountableWeakModelCode L)
    (hc : c.asWeakModel.Adequate S) (hS : S.Countable) :
    WeakDirectedChain.{u,0,0} OmegaOne (SequenceClosure.carrier S) :=
  AdequateOmegaOneNode.chain c hc (codeGrowth hS) codeLimit

theorem adequateOmegaOneChain_initial (c : CountableWeakModelCode L)
    (hc : c.asWeakModel.Adequate S) (hS : S.Countable) :
    (c.adequateOmegaOneChain hc hS).model omegaOneZero = c.asWeakModel :=
  AdequateOmegaOneNode.chain_initial c hc (codeGrowth hS) codeLimit

theorem adequateOmegaOneChain_adequate (c : CountableWeakModelCode L)
    (hc : c.asWeakModel.Adequate S) (hS : S.Countable) (i : OmegaOne) :
    ((c.adequateOmegaOneChain hc hS).model i).Adequate S :=
  AdequateOmegaOneNode.chain_adequate c hc (codeGrowth hS) codeLimit i

theorem adequateOmegaOneChain_growth (c : CountableWeakModelCode L)
    (hc : c.asWeakModel.Adequate S) (hS : S.Countable) :
    (c.adequateOmegaOneChain hc hS).LargeFiberSuccessorGrowth :=
  AdequateOmegaOneNode.chain_growth c hc (codeGrowth hS) codeLimit

theorem adequateOmegaOneChain_successor_freezes (c : CountableWeakModelCode L)
    (hc : c.asWeakModel.Adequate S) (hS : S.Countable) :
    (c.adequateOmegaOneChain hc hS).FreezesSmallFibersAtSuccessors :=
  AdequateOmegaOneNode.chain_successor_freezes c hc (codeGrowth hS) codeLimit

theorem adequateOmegaOneChain_continuous (c : CountableWeakModelCode L)
    (hc : c.asWeakModel.Adequate S) (hS : S.Countable) :
    (c.adequateOmegaOneChain hc hS).ContinuousAtLimits :=
  AdequateOmegaOneNode.chain_continuous c hc (codeGrowth hS) codeLimit

theorem adequateOmegaOneChain_freezes (c : CountableWeakModelCode L)
    (hc : c.asWeakModel.Adequate S) (hS : S.Countable) (i j : OmegaOne) (h : i ≤ j) :
    ((c.adequateOmegaOneChain hc hS).map h).FreezesSmallFibers :=
  AdequateOmegaOneNode.chain_freezes c hc (codeGrowth hS) codeLimit i j h

end CountableWeakModelCode

namespace WeakModel
variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}

/-- Starting from an adequate countable weak model, construct the omega-one
chain itself. The initial embedding is a bijective elementary copy; no chain,
schedule, growth operation or limit operation is assumed by this interface. -/
theorem exists_adequate_omegaOne_chain (M : WeakModel.{u,v} L)
    (hM : M.Adequate S) (hS : S.Countable) :
    ∃ C : WeakDirectedChain.{u,0,0} OmegaOne (SequenceClosure.carrier S),
      ∃ e : WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) M (C.model omegaOneZero),
        C.LargeFiberSuccessorGrowth ∧ C.FreezesSmallFibersAtSuccessors ∧ C.ContinuousAtLimits ∧
          (∀ i, (C.model i).Adequate S) ∧ Function.Bijective e ∧ e.FreezesSmallFibers := by
  obtain ⟨c, e, hc, he, hf⟩ := CountableWeakModelCode.exists_adequate_code M hM
  let C := c.adequateOmegaOneChain hc hS
  have hzero : C.model omegaOneZero = c.asWeakModel := c.adequateOmegaOneChain_initial hc hS
  have he0 : ∃ e0 : WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) M (C.model omegaOneZero),
      Function.Bijective e0 ∧ e0.FreezesSmallFibers := by
    rw [hzero]
    exact ⟨e, he, hf⟩
  obtain ⟨e0, he0, hf0⟩ := he0
  exact ⟨C, e0, c.adequateOmegaOneChain_growth hc hS,
    c.adequateOmegaOneChain_successor_freezes hc hS, c.adequateOmegaOneChain_continuous hc hS,
    c.adequateOmegaOneChain_adequate hc hS, he0, hf0⟩

end WeakModel
end ZFVP.Infinitary
