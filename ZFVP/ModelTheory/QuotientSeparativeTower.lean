import ZFVP.ModelTheory.ProjectionQuotientTower
import ZFVP.ModelTheory.ProjectionQuotientSeparative
import ZFVP.SetTheory.EndExtensionSeparative
import ZFVP.SetTheory.ForcingClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem projectionQuotient_separative_tower (A C : ForcingContext V)
    {Q S π τ ρ E q r : V}
    (hτ : IsForcingSplitProjection A.P A.R C.P C.R τ E)
    (hA : forcingProjectionGeneric A.P A.R τ C.G = A.G)
    (hπ : π ∈ A.P ^ Q) (hρ : IsForcingProjection C.P C.R Q S ρ)
    (hS : IsForcingPreorder Q S) (he : ∀ s ∈ Q, τ ‘ (ρ ‘ s) = π ‘ s)
    (hq : C.check q ∈ C.projectionQuotient Q ρ)
    (hr : C.check r ∈ C.projectionQuotient Q ρ)
    (hqr : ⟨A.check q, A.check r⟩ₖ ∈ forcingSeparativeOrder
      (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) :
    ⟨C.check q, C.check r⟩ₖ ∈ forcingSeparativeOrder
      (C.projectionQuotient Q ρ) (C.projectionQuotientOrder Q S ρ) := by
  let B := A.projectionQuotientContext C hτ hA
  have hqB : B.check (A.check q) ∈ B.projectionQuotient (A.projectionQuotient Q π)
      (A.projectionQuotientMap Q π ρ) :=
    (A.double_projectionQuotient_check_mem_iff B hπ hτ.projection hρ.maps he C.generic.1 hA rfl rfl).mpr
      ((C.check_mem_projectionQuotient_iff hρ.maps).mp hq)
  have hrB : B.check (A.check r) ∈ B.projectionQuotient (A.projectionQuotient Q π)
      (A.projectionQuotientMap Q π ρ) :=
    (A.double_projectionQuotient_check_mem_iff B hπ hτ.projection hρ.maps he C.generic.1 hA rfl rfl).mpr
      ((C.check_mem_projectionQuotient_iff hρ.maps).mp hr)
  have hb := B.projectionQuotient_separative_of_ground
    (A.projectionQuotient_projection hπ hτ.projection.maps hρ he)
    (A.projectionQuotient_preorder hπ hS) hqB hrB hqr
  let j := (A.projectionQuotientRealization C hτ hA).embedding
  have hout := (j.forcingSeparativeOrder_iff _ _ _ _).mpr hb
  change ⟨A.projectionFactorizationEquiv C hτ hA (B.check (A.check q)),
      A.projectionFactorizationEquiv C hτ hA (B.check (A.check r))⟩ₖ ∈
    forcingSeparativeOrder (A.projectionFactorizationEquiv C hτ hA _)
      (A.projectionFactorizationEquiv C hτ hA _) at hout
  rw [A.projectionFactorizationEquiv_quotient C hτ hA hπ hρ.maps he,
    A.projectionFactorizationEquiv_quotientOrder C hτ hA hπ hρ.maps he,
    A.projectionFactorizationEquiv_ground C hτ hA q,
    A.projectionFactorizationEquiv_ground C hτ hA r] at hout
  exact hout

theorem projectionQuotient_descending_tower (A C : ForcingContext V)
    {Q S π τ ρ E : V} {α f : A.Model} [IsOrdinal α]
    (hτ : IsForcingSplitProjection A.P A.R C.P C.R τ E)
    (hA : forcingProjectionGeneric A.P A.R τ C.G = A.G)
    (hπ : π ∈ A.P ^ Q) (hρ : IsForcingProjection C.P C.R Q S ρ)
    (hS : IsForcingPreorder Q S) (he : ∀ s ∈ Q, τ ‘ (ρ ‘ s) = π ‘ s)
    (hf : IsForcingDescending (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) α f)
    (hfirst : ∀ i ∈ α, ∀ q ∈ Q, f ‘ i = A.check q → ρ ‘ q ∈ C.G) :
    IsForcingDescending (C.projectionQuotient Q ρ)
      (forcingSeparativeOrder (C.projectionQuotient Q ρ) (C.projectionQuotientOrder Q S ρ))
      (A.projectionInclusion C hτ hA α) (A.projectionInclusion C hτ hA f) := by
  let j := A.projectionInclusion C hτ hA
  have hval (i : A.Model) (hi : i ∈ α) : j (f ‘ i) ∈ C.projectionQuotient Q ρ := by
    obtain ⟨q, hq, _, hqi⟩ := (A.mem_projectionQuotient_iff hπ _).mp (function_value_mem hf.1 hi)
    rw [hqi, A.projectionInclusion_check C hτ hA]
    exact (C.check_mem_projectionQuotient_iff hρ.maps).mpr ⟨hq, hfirst i hi q hq hqi⟩
  have hfj := (j.function_iff f α (A.projectionQuotient Q π)).mpr hf.1
  let := IsFunction.of_mem hfj
  refine ⟨mem_function.intro ?_ (exists_unique_of_mem_function hfj), ?_⟩
  · intro z hz
    obtain ⟨i, hi, y, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hfj z hz)
    obtain ⟨a, ha, rfl⟩ := j.endExtension α i hi
    have hy : y = j (f ‘ a) :=
      (value_eq_of_kpair_mem hz).symm.trans (j.map_value_total f a).symm
    exact kpair_mem_iff.mpr ⟨hi, hy ▸ hval a ha⟩
  · intro i hi k hk
    obtain ⟨a, ha, rfl⟩ := j.endExtension α i hi
    obtain ⟨b, hb, rfl⟩ := j.endExtension a k hk
    have hbα := IsOrdinal.toIsTransitive.mem_trans hb ha
    obtain ⟨q, hq, _, hqa⟩ := (A.mem_projectionQuotient_iff hπ _).mp (function_value_mem hf.1 ha)
    obtain ⟨r, hr, _, hrb⟩ := (A.mem_projectionQuotient_iff hπ _).mp (function_value_mem hf.1 hbα)
    rw [← j.map_value_total, ← j.map_value_total, hqa, hrb]
    change ⟨A.projectionInclusion C hτ hA (A.check q),
      A.projectionInclusion C hτ hA (A.check r)⟩ₖ ∈ _
    rw [A.projectionInclusion_check C hτ hA q, A.projectionInclusion_check C hτ hA r]
    apply A.projectionQuotient_separative_tower C hτ hA hπ hρ hS he
    · exact (C.check_mem_projectionQuotient_iff hρ.maps).mpr ⟨hq, hfirst a ha q hq hqa⟩
    · exact (C.check_mem_projectionQuotient_iff hρ.maps).mpr ⟨hr, hfirst b hbα r hr hrb⟩
    · simpa only [hqa, hrb] using hf.2 a ha b hb

end ForcingContext
end ZFVP
