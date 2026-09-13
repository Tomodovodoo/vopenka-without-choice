import ZFVP.ModelTheory.ForcingRegularGenericEquality
import ZFVP.SetTheory.ForcingSaturatedName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]

theorem atomicMembership_eq_of_all_values {P R one : V} (hR : IsForcingPreorder P R)
    (ht : IsForcingTop P R one) (σ Q Q' : ForcingName P)
    (he : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
      A.ofName Q = A.ofName Q') :
    atomicMembership P R σ.val Q.val = atomicMembership P R σ.val Q'.val := by
  apply IsForcingRegular.eq_of_all_generics hR (atomicMembership_regular hR _ _) (atomicMembership_regular hR _ _)
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  change A.ofName σ ∈ A.ofName Q ↔ A.ofName σ ∈ A.ofName Q'
  rw [show A.ofName Q = A.ofName Q' from he G hG]

theorem forcingSaturatedName_eq_of_all_values {P R one : V} (hR : IsForcingPreorder P R)
    (ht : IsForcingTop P R one) (U : V) (Q Q' : ForcingName P)
    (he : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
      A.ofName Q = A.ofName Q') :
    forcingSaturatedName P R U Q.val = forcingSaturatedName P R U Q'.val := by
  apply mem_ext
  intro z
  simp only [forcingSaturatedName, mem_sep_iff]
  apply and_congr_right
  intro hz
  obtain ⟨τ, _, p, _, rfl⟩ := mem_prod_iff.mp hz
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  apply and_congr_right
  intro hτ
  rw [atomicMembership_eq_of_all_values hR ht ⟨τ, hτ⟩ Q Q' he]

end ZFVP
