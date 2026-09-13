import ZFVP.ModelTheory.SuccessorNameElementaryLift
import ZFVP.ModelTheory.SuccessorLowNameCoverage
import ZFVP.SetTheory.MembershipIso

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext
variable (A : ForcingContext V) {η : V} [IsOrdinal η]
variable (hlow : ∀ x ∈ hierarchy (A.check η), ∃ σ : ForcingName A.P,
  σ.val ∈ hierarchy η ∧ x = A.ofName σ)

def successorNameRankEquiv : A.SuccessorNameModel η ≃ SetDomain (hierarchy (succ (A.check η))) where
  toFun x := ⟨x.val, by
    obtain ⟨τ, hτ, hx⟩ := x.property
    exact (A.successor_low_name_coverage hlow _).mpr
      ⟨⟨τ, successorLowNameSet_isName hτ⟩, hτ, hx⟩⟩
  invFun x := ⟨x.val, by
    obtain ⟨τ, hτ, hx⟩ := (A.successor_low_name_coverage hlow x.val).mp x.property
    exact ⟨τ.val, hτ, hx⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem successorNameRankEquiv_mem (x y : A.SuccessorNameModel η) :
    A.successorNameRankEquiv hlow x ∈ A.successorNameRankEquiv hlow y ↔ x ∈ y := Iff.rfl

end ForcingContext

theorem finiteRankEmbedding_successorRankLift {η ζ f : V} [IsOrdinal η] [IsOrdinal ζ]
    (A B : ForcingContext V)
    (hη : ∀ β ∈ η, succ β ∈ η) (hζ : ∀ β ∈ ζ, succ β ∈ ζ)
    (hP : A.P ⊆ hierarchy η) (hQ : B.P ⊆ hierarchy ζ)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd η (ω : V)))
      (hierarchy (ordinalAdd ζ (ω : V))) f)
    (hfP : f ‘ A.P = B.P) (hfR : f ‘ A.R = B.R) (hfη : f ‘ η = ζ)
    (hG : ∀ p ∈ A.G, f ‘ p ∈ B.G)
    (hA : ∀ x ∈ hierarchy (A.check η), ∃ σ : ForcingName A.P,
      σ.val ∈ hierarchy η ∧ x = A.ofName σ)
    (hB : ∀ x ∈ hierarchy (B.check ζ), ∃ σ : ForcingName B.P,
      σ.val ∈ hierarchy ζ ∧ x = B.ofName σ) :
    ∃ j : ElementaryMap (SetDomain (hierarchy (succ (A.check η))))
      (SetDomain (hierarchy (succ (B.check ζ)))),
      ∀ τ : {x : V // x ∈ successorLowNameSet A.P η}, ∃ τ' : ForcingName B.P,
        τ'.val = f ‘ τ.val ∧
          (j (A.successorNameRankEquiv hA (A.successorNameValue η τ))).val = B.ofName τ' := by
  obtain ⟨j, hj⟩ := finiteRankEmbedding_successorNameLift A B hη hζ hP hQ he hfP hfR hfη hG
  let a := A.successorNameRankEquiv hA
  let b := B.successorNameRankEquiv hB
  let a' : ElementaryMap (SetDomain (hierarchy (succ (A.check η)))) (A.SuccessorNameModel η) :=
    ElementaryMap.ofMembershipIso a.symm (fun _ _ ↦ Iff.rfl)
  let b' : ElementaryMap (B.SuccessorNameModel ζ) (SetDomain (hierarchy (succ (B.check ζ)))) :=
    ElementaryMap.ofMembershipIso b (fun _ _ ↦ Iff.rfl)
  refine ⟨b'.comp (j.comp a'), ?_⟩
  intro τ
  obtain ⟨τ', ht, hv⟩ := hj τ
  refine ⟨τ', ht, ?_⟩
  change (j (a.symm (a (A.successorNameValue η τ)))).val = B.ofName τ'
  rwa [a.symm_apply_apply]

end ZFVP
