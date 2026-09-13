import ZFVP.ModelTheory.ForcingGenericInclusion
import ZFVP.ModelTheory.ProjectionQuotientGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext
variable (A B : ForcingContext V) {π E : V}
  (hπ : IsForcingSplitProjection A.P A.R B.P B.R π E)
  (he : forcingProjectionGeneric A.P A.R π B.G = A.G)

noncomputable def projectedGenericSet (E : V) : B.Model :=
  {p ∈ B.check A.P ; (B.check E) ‘ p ∈ B.genericSet}

include hπ he

theorem check_mem_projectedGenericSet (p : V) :
    B.check p ∈ A.projectedGenericSet B E ↔ p ∈ A.G := by
  let := IsFunction.of_mem hπ.maps
  constructor
  · intro hp
    obtain ⟨hpP, hpE⟩ := mem_sep_iff.mp hp
    have hpA := (B.check_mem_iff p A.P).mp hpP
    rw [B.check_value ((domain_eq_of_mem_function hπ.maps).symm ▸ hpA),
      B.check_mem_genericSet_iff] at hpE
    exact he ▸ (hπ.generic_iff_section A.order B.generic.1 hpA).mpr hpE
  · intro hp
    have hpA := A.generic.1.1 p hp
    refine mem_sep_iff.mpr ⟨(B.check_mem_iff p A.P).mpr hpA, ?_⟩
    rw [B.check_value ((domain_eq_of_mem_function hπ.maps).symm ▸ hpA),
      B.check_mem_genericSet_iff]
    exact (hπ.generic_iff_section A.order B.generic.1 hpA).mp (he.symm ▸ hp)

noncomputable def projectionRealization : ForcingRealization A B.Model where
  ground := B.checkEmbedding
  genericSet := A.projectedGenericSet B E
  generic_subset := fun _ hp ↦ (mem_sep_iff.mp hp).1
  generic_mem := A.check_mem_projectedGenericSet B hπ he

noncomputable def projectionInclusion : MembershipEndExtension A.Model B.Model :=
  (A.projectionRealization B hπ he).embedding

theorem projectionInclusion_check (x : V) :
    A.projectionInclusion B hπ he (A.check x) = B.check x :=
  (A.projectionRealization B hπ he).value_check x

theorem projectionInclusion_genericSet :
    A.projectionInclusion B hπ he A.genericSet = A.projectedGenericSet B E :=
  (A.projectionRealization B hπ he).value_genericSet

noncomputable def projectionQuotientContext : ForcingContext A.Model where
  P := A.projectionQuotient B.P π
  R := A.projectionQuotientOrder B.P B.R π
  one := A.check (E ‘ A.one)
  G := A.projectionQuotientFilter B.G
  order := A.projectionQuotient_preorder hπ.projection.maps B.order
  top := A.projectionQuotient_top hπ.projection.maps
    ⟨function_value_mem hπ.maps A.top.1, fun q hq ↦
      (hπ.below q hq A.one A.top.1).mpr (A.top.2 _ (function_value_mem hπ.projection.maps hq))⟩
    (hπ.right_inverse A.one A.top.1)
  generic := A.projectionQuotient_generic hπ B.order B.generic he

end ForcingContext
end ZFVP
