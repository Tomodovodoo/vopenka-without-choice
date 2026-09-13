import ZFVP.ModelTheory.ForcingProjection
import ZFVP.SetTheory.FunctionComposition
import ZFVP.SetTheory.ForcingSeparativeOrder
import ZFVP.SetTheory.ForcingClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A projection that reflects compatibility also reflects and preserves the
separative order. -/
theorem IsForcingProjection.separative_iff {P R Q S π a b : V}
    (h : IsForcingProjection P R Q S π)
    (hc : ∀ a ∈ Q, ∀ b ∈ Q,
      ForcingCompatible Q S a b ↔ ForcingCompatible P R (π ‘ a) (π ‘ b))
    (ha : a ∈ Q) (hb : b ∈ Q) :
    ⟨a, b⟩ₖ ∈ forcingSeparativeOrder Q S ↔
      ⟨π ‘ a, π ‘ b⟩ₖ ∈ forcingSeparativeOrder P R := by
  constructor
  · intro hab
    refine (kpair_mem_forcingSeparativeOrder _ _ _ _).mpr
      ⟨function_value_mem h.maps ha, function_value_mem h.maps hb, ?_⟩
    intro p hp hpa
    obtain ⟨c, hcQ, hca, he⟩ := h.lift a ha p hp hpa
    have hh := (hc c hcQ b hb).mp
      (((kpair_mem_forcingSeparativeOrder _ _ _ _).mp hab).2.2 c hcQ hca)
    rwa [he] at hh
  · intro hab
    refine (kpair_mem_forcingSeparativeOrder _ _ _ _).mpr ⟨ha, hb, ?_⟩
    intro c hcQ hca
    exact (hc c hcQ b hb).mpr
      (((kpair_mem_forcingSeparativeOrder _ _ _ _).mp hab).2.2 _
        (function_value_mem h.maps hcQ) (h.monotone c hcQ a ha hca))

/-- Closure of the target separative order transfers along an onto projection
that reflects compatibility. This uses no selection of an indexed family of
preimages. -/
theorem IsForcingProjection.separative_closedAt {P R Q S π α : V} [IsOrdinal α]
    (h : IsForcingProjection P R Q S π)
    (hc : ∀ a ∈ Q, ∀ b ∈ Q,
      ForcingCompatible Q S a b ↔ ForcingCompatible P R (π ‘ a) (π ‘ b))
    (hsurj : ∀ p ∈ P, ∃ q ∈ Q, π ‘ q = p)
    (hclosed : IsForcingClosedAt P (forcingSeparativeOrder P R) α) :
    IsForcingClosedAt Q (forcingSeparativeOrder Q S) α := by
  intro f hf
  have hcomp := compose_function hf.1 h.maps
  have hdesc : IsForcingDescending P (forcingSeparativeOrder P R) α (compose f π) := by
    refine ⟨hcomp, ?_⟩
    intro i hi j hj
    have hjα := IsOrdinal.toIsTransitive.mem_trans hj hi
    rw [value_compose_of_mem_function hf.1 h.maps hi,
      value_compose_of_mem_function hf.1 h.maps hjα]
    exact (h.separative_iff hc (function_value_mem hf.1 hi)
      (function_value_mem hf.1 hjα)).mp (hf.2 i hi j hj)
  obtain ⟨p, hp, hb⟩ := hclosed _ hdesc
  obtain ⟨q, hq, he⟩ := hsurj p hp
  refine ⟨q, hq, ?_⟩
  intro i hi
  apply (h.separative_iff hc hq (function_value_mem hf.1 hi)).mpr
  rw [he]
  simpa only [value_compose_of_mem_function hf.1 h.maps hi] using hb i hi

end ZFVP

