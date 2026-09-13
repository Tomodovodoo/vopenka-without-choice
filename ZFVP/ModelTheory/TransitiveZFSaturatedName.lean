import ZFVP.ModelTheory.TransitiveZFAtomicForcing
import ZFVP.ModelTheory.TransitiveZFForcingOrders
import ZFVP.SetTheory.ForcingSaturatedName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingSaturatedName_val (P R N Q : SetDomain U) :
    (forcingSaturatedName P R N Q).val = forcingSaturatedName P.val R.val N.val Q.val := by
  unfold forcingSaturatedName
  rw [← prod_val U N P]
  apply sep_val U
  intro z hz
  obtain ⟨τ, _, p, _, rfl⟩ := mem_prod_iff.mp hz
  simp only [kpair_val U, kpair.π₁_kpair, kpair.π₂_kpair]
  apply and_congr (forcingName_iff U P τ)
  change p.val ∈ (atomicMembership P R τ Q).val ↔ _
  rw [atomicMembership_val U]

end TransitiveZF
end ZFVP
