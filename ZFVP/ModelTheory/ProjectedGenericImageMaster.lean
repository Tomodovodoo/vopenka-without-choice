import ZFVP.ModelTheory.ForcingProjectedGenericImage
import ZFVP.SetTheory.ForcingDirectedClosure
import ZFVP.SetTheory.ForcingSeparativeOrder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

/-- A short enumerated image of the projected generic has a ground master
condition once directed closure of the actual quotient is available. -/
theorem projectedGeneric_image_master (C A : ForcingContext V)
    {π₀ E γ δ Q S π f : V} [IsOrdinal γ] [IsOrdinal δ]
    (hπ₀ : IsForcingSplitProjection C.P C.R A.P A.R π₀ E)
    (hgeneric : forcingProjectionGeneric C.P C.R π₀ A.G = C.G)
    (hsmall : rank C.P ⊆ γ) (hγδ : γ ∈ δ)
    (henum : HasShortRankEnumerations (A.check δ) (A.check δ))
    (hS : IsForcingPreorder Q S) (hπ : π ∈ A.P ^ Q)
    (himage : ∀ p ∈ C.G, f ‘ p ∈ Q ∧ π ‘ (f ‘ p) ∈ A.G)
    (hdirected : ∀ p ∈ C.G, ∀ q ∈ C.G, ∃ r ∈ C.G,
      ⟨f ‘ r, f ‘ p⟩ₖ ∈ S ∧ ⟨f ‘ r, f ‘ q⟩ₖ ∈ S)
    (hclosed : ∀ ν ∈ A.check δ, IsForcingDirectedClosedAt (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) ν) :
    ∃ t ∈ Q, π ‘ t ∈ A.G ∧ ∀ p ∈ C.G,
      ⟨A.check t, A.check (f ‘ p)⟩ₖ ∈ forcingSeparativeOrder
        (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) := by
  let I := A.checkedMapImage f (C.projectedGenericSet A E)
  have hmem (x : A.Model) : x ∈ I ↔ ∃ p ∈ C.G, x = A.check (f ‘ p) :=
    C.mem_projectedGeneric_image_iff A hπ₀ hgeneric f x
  have hI : I ⊆ A.projectionQuotient Q π := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := (hmem x).mp hx
    exact (A.check_mem_projectionQuotient_iff hπ).mpr (himage p hp)
  have hdir : ∀ x ∈ I, ∀ y ∈ I, ∃ z ∈ I,
      ⟨z, x⟩ₖ ∈ forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) ∧
      ⟨z, y⟩ₖ ∈ forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) := by
    intro x hx y hy
    obtain ⟨p, hp, rfl⟩ := (hmem x).mp hx
    obtain ⟨q, hq, rfl⟩ := (hmem y).mp hy
    obtain ⟨r, hr, hrp, hrq⟩ := hdirected p hp q hq
    have hrI := (hmem (A.check (f ‘ r))).mpr ⟨r, hr, rfl⟩
    have hrel {u v : V} (hu : u ∈ C.G) (hv : v ∈ C.G) (huv : ⟨f ‘ u, f ‘ v⟩ₖ ∈ S) :
        ⟨A.check (f ‘ u), A.check (f ‘ v)⟩ₖ ∈ forcingSeparativeOrder
          (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) := by
      apply forcingOrder_subset_separative (A.projectionQuotient_preorder hπ hS)
      apply (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
      exact ⟨A.check_kpair (f ‘ u) (f ‘ v) ▸ (A.check_mem_iff _ _).mpr huv,
        (A.check_mem_projectionQuotient_iff hπ).mpr (himage u hu),
        (A.check_mem_projectionQuotient_iff hπ).mpr (himage v hv)⟩
    exact ⟨A.check (f ‘ r), hrI, hrel hr hp hrp, hrel hr hq hrq⟩
  obtain ⟨ν, hν, s, hs, hsr⟩ :=
    C.projectedGeneric_image_shortEnumeration A hπ₀ hgeneric hsmall hγδ henum f
  change s ∈ I ^ ν at hs
  change range s = I at hsr
  let := IsFunction.of_mem hs
  have hsurj : ∀ x ∈ I, ∃ i ∈ ν, s ‘ i = x := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_range_iff.mp (hsr.symm ▸ hx)
    exact ⟨i, (mem_of_mem_functions hs hi).1, value_eq_of_kpair_mem hi⟩
  have hf : IsForcingDirectedFamily (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) ν s := by
    refine ⟨mem_function_of_mem_function_of_subset hs hI, ?_⟩
    intro i hi j hj
    obtain ⟨z, hz, hzi, hzj⟩ := hdir _ (function_value_mem hs hi) _ (function_value_mem hs hj)
    obtain ⟨k, hk, hkv⟩ := hsurj z hz
    exact ⟨k, hk, hkv.symm ▸ hzi, hkv.symm ▸ hzj⟩
  obtain ⟨u, hu, hub⟩ := hclosed ν hν s hf
  obtain ⟨t, ht, htG, rfl⟩ := (A.mem_projectionQuotient_iff hπ u).mp hu
  refine ⟨t, ht, htG, ?_⟩
  intro p hp
  obtain ⟨i, hi, hiv⟩ := hsurj _ ((hmem _).mpr ⟨p, hp, rfl⟩)
  exact hiv ▸ hub i hi

end ForcingContext
end ZFVP
