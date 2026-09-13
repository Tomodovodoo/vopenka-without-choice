import ZFVP.SetTheory.ForcingOrder
import ZFVP.SetTheory.FunctionValue

/-! Dense embeddings of forcing preorders: order-preserving maps with dense range that preserve
incompatibility. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `e : P → P'` is a dense embedding: order preserving, incompatibility preserving, with dense
range. -/
def IsDenseEmbedding (P R P' R' e : V) : Prop :=
  e ∈ P' ^ P ∧ (∀ p ∈ P, ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨e ‘ q, e ‘ p⟩ₖ ∈ R') ∧
    (∀ p ∈ P, ∀ q ∈ P, ¬ ForcingCompatible P R p q → ¬ ForcingCompatible P' R' (e ‘ p) (e ‘ q)) ∧
    ∀ p' ∈ P', ∃ p ∈ P, ⟨e ‘ p, p'⟩ₖ ∈ R'

theorem IsDenseEmbedding.value_mem {P R P' R' e : V} (he : IsDenseEmbedding P R P' R' e) {p : V}
    (hp : p ∈ P) : e ‘ p ∈ P' :=
  function_value_mem he.1 hp

/-- Compatibility of images gives compatibility of the conditions. -/
theorem IsDenseEmbedding.compatible_of_value {P R P' R' e : V} (he : IsDenseEmbedding P R P' R' e)
    {p q : V} (hp : p ∈ P) (hq : q ∈ P) (h : ForcingCompatible P' R' (e ‘ p) (e ‘ q)) :
    ForcingCompatible P R p q := by
  by_contra hn
  exact he.2.2.1 p hp q hq hn h

/-- Below every condition there is one whose image lies below a given condition below the image. -/
theorem IsDenseEmbedding.exists_below {P R P' R' e : V} (hR : IsForcingPreorder P R)
    (hR' : IsForcingPreorder P' R') (he : IsDenseEmbedding P R P' R' e) {p d : V} (hp : p ∈ P)
    (hd : d ∈ P') (hdp : ⟨d, e ‘ p⟩ₖ ∈ R') : ∃ r ∈ P, ⟨r, p⟩ₖ ∈ R ∧ ⟨e ‘ r, d⟩ₖ ∈ R' := by
  obtain ⟨q, hq, hqd⟩ := he.2.2.2 d hd
  have hcomp : ForcingCompatible P' R' (e ‘ p) (e ‘ q) :=
    ⟨e ‘ q, he.value_mem hq, hR'.2.2 _ (he.value_mem hq) d hd _ (he.value_mem hp) hqd hdp,
      hR'.2.1 _ (he.value_mem hq)⟩
  obtain ⟨r, hr, hrp, hrq⟩ := he.compatible_of_value hp hq hcomp
  refine ⟨r, hr, hrp, ?_⟩
  exact hR'.2.2 _ (he.value_mem hr) _ (he.value_mem hq) d hd (he.2.1 q hq r hr hrq) hqd

end ZFVP
