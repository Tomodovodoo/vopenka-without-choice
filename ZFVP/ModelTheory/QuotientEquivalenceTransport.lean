import ZFVP.ModelTheory.QuotientSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A B : ForcingContext V) (e : A.Model ≃ B.Model)
  (hm : ∀ x y, e x ∈ e y ↔ x ∈ y) (hc : ∀ x, e (A.check x) = B.check x)

noncomputable def transportedProjectionQuotient (K ρ : V) : A.Model :=
  e.symm (B.projectionQuotient K ρ)

noncomputable def transportedProjectionQuotientOrder (K L ρ : V) : A.Model :=
  e.symm (B.projectionQuotientOrder K L ρ)

include hm in
theorem mem_equiv_pullback (x : A.Model) (y : B.Model) :
    x ∈ e.symm y ↔ e x ∈ y := by
  simpa only [Equiv.apply_symm_apply] using (hm x (e.symm y)).symm

include hm hc in
theorem check_mem_transportedProjectionQuotient_iff {K ρ q : V}
    (hρ : ρ ∈ B.P ^ K) :
    A.check q ∈ A.transportedProjectionQuotient B e K ρ ↔ q ∈ K ∧ ρ ‘ q ∈ B.G := by
  rw [transportedProjectionQuotient, A.mem_equiv_pullback B e hm, hc]
  exact B.check_mem_projectionQuotient_iff hρ

include hm hc in
theorem mem_transportedProjectionQuotient_iff {K ρ : V}
    (hρ : ρ ∈ B.P ^ K) (x : A.Model) :
    x ∈ A.transportedProjectionQuotient B e K ρ ↔
      ∃ q ∈ K, ρ ‘ q ∈ B.G ∧ x = A.check q := by
  rw [transportedProjectionQuotient, A.mem_equiv_pullback B e hm,
    B.mem_projectionQuotient_iff hρ]
  constructor
  · rintro ⟨q, hq, hg, he⟩
    exact ⟨q, hq, hg, e.injective (he.trans (hc q).symm)⟩
  · rintro ⟨q, hq, hg, rfl⟩
    exact ⟨q, hq, hg, hc q⟩

include hm hc in
theorem transportedProjectionQuotientOrder_check_pair_iff (K L ρ p q : V) :
    ⟨A.check p, A.check q⟩ₖ ∈ A.transportedProjectionQuotientOrder B e K L ρ ↔
      ⟨p, q⟩ₖ ∈ L ∧ A.check p ∈ A.transportedProjectionQuotient B e K ρ ∧
        A.check q ∈ A.transportedProjectionQuotient B e K ρ := by
  rw [transportedProjectionQuotientOrder, A.mem_equiv_pullback B e hm,
    ← A.check_kpair, hc, B.check_kpair, B.projectionQuotientOrder_pair_iff]
  simp only [transportedProjectionQuotient, A.mem_equiv_pullback B e hm,
    hc, ← B.check_kpair, B.check_mem_iff]

noncomputable def transportedProjectionQuotientInverse (K ρ v : V) : A.Model :=
  definableGraph (A.transportedProjectionQuotient B e K ρ)
    (fun x ↦ (A.check v) ‘ x) (by definability)

theorem transportedProjectionQuotientInverse_value {K Q ρ v q : V}
    (hv : v ∈ Q ^ K) (hq : q ∈ K)
    (hg : A.check q ∈ A.transportedProjectionQuotient B e K ρ) :
    (A.transportedProjectionQuotientInverse B e K ρ v) ‘ (A.check q) = A.check (v ‘ q) := by
  let := IsFunction.of_mem hv
  rw [transportedProjectionQuotientInverse, value_definableGraph _ _ _ hg,
    A.check_value ((domain_eq_of_mem_function hv).symm ▸ hq)]

variable {Q S π K L ρ u v : V}
  (hπ : π ∈ A.P ^ Q) (hρ : ρ ∈ B.P ^ K) (hu : u ∈ K ^ Q) (hv : v ∈ Q ^ K)
  (hg : ∀ p ∈ Q, ρ ‘ (u ‘ p) ∈ B.G ↔ π ‘ p ∈ A.G)
  (hi : ∀ q ∈ K, u ‘ (v ‘ q) = q)
  (ho : ∀ p ∈ Q, ∀ q ∈ Q, ⟨u ‘ p, u ‘ q⟩ₖ ∈ L ↔ ⟨p, q⟩ₖ ∈ S)

include hm hc hπ hρ hu hg in
theorem transportedProjectionQuotientMap_maps :
    A.projectionQuotientMap Q π u ∈
      A.transportedProjectionQuotient B e K ρ ^ A.projectionQuotient Q π := by
  apply definableGraph_mem_function_of_mapsTo
  intro x hx
  obtain ⟨q, hq, hqG, rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
  let := IsFunction.of_mem hu
  rw [A.check_value ((domain_eq_of_mem_function hu).symm ▸ hq)]
  exact (A.check_mem_transportedProjectionQuotient_iff B e hm hc hρ).mpr
    ⟨function_value_mem hu hq, (hg q hq).mpr hqG⟩

include hm hc hπ hρ hv hg hi in
theorem transportedProjectionQuotientInverse_maps :
    A.transportedProjectionQuotientInverse B e K ρ v ∈
      A.projectionQuotient Q π ^ A.transportedProjectionQuotient B e K ρ := by
  apply definableGraph_mem_function_of_mapsTo
  intro x hx
  obtain ⟨q, hq, hqG, rfl⟩ := (A.mem_transportedProjectionQuotient_iff B e hm hc hρ x).mp hx
  let := IsFunction.of_mem hv
  rw [A.check_value ((domain_eq_of_mem_function hv).symm ▸ hq)]
  apply (A.check_mem_projectionQuotient_iff hπ).mpr
  exact ⟨function_value_mem hv hq, (hg _ (function_value_mem hv hq)).mp (by rwa [hi q hq])⟩

include hm hc hπ hρ hu hg ho in
theorem transportedProjectionQuotientMap_order_iff
    (x : A.Model) (hx : x ∈ A.projectionQuotient Q π)
    (y : A.Model) (hy : y ∈ A.projectionQuotient Q π) :
    ⟨(A.projectionQuotientMap Q π u) ‘ x, (A.projectionQuotientMap Q π u) ‘ y⟩ₖ ∈
      A.transportedProjectionQuotientOrder B e K L ρ ↔
        ⟨x, y⟩ₖ ∈ A.projectionQuotientOrder Q S π := by
  have hmap := A.transportedProjectionQuotientMap_maps B e hm hc hπ hρ hu hg
  have hx' := function_value_mem hmap hx
  have hy' := function_value_mem hmap hy
  obtain ⟨p, hp, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
  obtain ⟨q, hq, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ y).mp hy
  rw [A.projectionQuotientMap_value hu hp hx] at hx' ⊢
  rw [A.projectionQuotientMap_value hu hq hy] at hy' ⊢
  rw [A.transportedProjectionQuotientOrder_check_pair_iff B e hm hc,
    A.projectionQuotientOrder_pair_iff]
  simp only [hx, hy, hx', hy', and_true, ← A.check_kpair, A.check_mem_iff]
  exact ho p hp q hq





include hm hc hπ hρ hu hv hg hi in
theorem transportedProjectionQuotientMap_right_inverse
    (x : A.Model) (hx : x ∈ A.transportedProjectionQuotient B e K ρ) :
    (A.projectionQuotientMap Q π u) ‘
      ((A.transportedProjectionQuotientInverse B e K ρ v) ‘ x) = x := by
  have hinv := A.transportedProjectionQuotientInverse_maps B e hm hc hπ hρ hv hg hi
  have hx' := function_value_mem hinv hx
  obtain ⟨q, hq, _, rfl⟩ := (A.mem_transportedProjectionQuotient_iff B e hm hc hρ x).mp hx
  rw [A.transportedProjectionQuotientInverse_value B e hv hq hx] at hx' ⊢
  rw [A.projectionQuotientMap_value hu (function_value_mem hv hq) hx', hi q hq]

include hm hc hπ hρ hu hv hg hi ho in
theorem transportedProjectionQuotient_projection :
    IsForcingProjection (A.transportedProjectionQuotient B e K ρ)
      (A.transportedProjectionQuotientOrder B e K L ρ)
      (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)
      (A.projectionQuotientMap Q π u) := by
  have hmap := A.transportedProjectionQuotientMap_maps B e hm hc hπ hρ hu hg
  have hinv := A.transportedProjectionQuotientInverse_maps B e hm hc hπ hρ hv hg hi
  refine ⟨hmap, ?_, ?_⟩
  · intro x hx y hy hxy
    exact (A.transportedProjectionQuotientMap_order_iff B e hm hc hπ hρ hu hg ho x hx y hy).mpr hxy
  · intro x hx y hy hyx
    let z := (A.transportedProjectionQuotientInverse B e K ρ v) ‘ y
    have hz := function_value_mem hinv hy
    have heq := A.transportedProjectionQuotientMap_right_inverse B e hm hc hπ hρ hu hv hg hi y hy
    refine ⟨z, hz, ?_, heq⟩
    apply (A.transportedProjectionQuotientMap_order_iff B e hm hc hπ hρ hu hg ho z hz x hx).mp
    rwa [heq]

include hm hc hπ hρ hu hv hg hi ho in
theorem transportedProjectionQuotient_splitProjection :
    IsForcingSplitProjection (A.transportedProjectionQuotient B e K ρ)
      (A.transportedProjectionQuotientOrder B e K L ρ)
      (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)
      (A.projectionQuotientMap Q π u) (A.transportedProjectionQuotientInverse B e K ρ v) := by
  have hinv := A.transportedProjectionQuotientInverse_maps B e hm hc hπ hρ hv hg hi
  refine ⟨A.transportedProjectionQuotient_projection B e hm hc hπ hρ hu hv hg hi ho,
    hinv, A.transportedProjectionQuotientMap_right_inverse B e hm hc hπ hρ hu hv hg hi, ?_⟩
  intro x hx y hy
  have hh := A.transportedProjectionQuotientMap_order_iff B e hm hc hπ hρ hu hg ho
    x hx _ (function_value_mem hinv hy)
  rw [A.transportedProjectionQuotientMap_right_inverse B e hm hc hπ hρ hu hv hg hi y hy] at hh
  exact hh.symm

include hm hc hπ hρ hu hv hg hi in
theorem transportedProjectionQuotientMap_surjective :
    ∀ y ∈ A.transportedProjectionQuotient B e K ρ,
      ∃ x ∈ A.projectionQuotient Q π, (A.projectionQuotientMap Q π u) ‘ x = y := by
  intro y hy
  exact ⟨_, function_value_mem
    (A.transportedProjectionQuotientInverse_maps B e hm hc hπ hρ hv hg hi) hy,
    A.transportedProjectionQuotientMap_right_inverse B e hm hc hπ hρ hu hv hg hi y hy⟩

include hm hc hπ hρ hu hv hg hi in
theorem transportedProjectionQuotientMap_inverse_equivalent
    (hl : ∀ p ∈ Q, ⟨v ‘ (u ‘ p), p⟩ₖ ∈ S ∧ ⟨p, v ‘ (u ‘ p)⟩ₖ ∈ S)
    (x : A.Model) (hx : x ∈ A.projectionQuotient Q π) :
    ⟨(A.transportedProjectionQuotientInverse B e K ρ v) ‘ ((A.projectionQuotientMap Q π u) ‘ x), x⟩ₖ ∈
      A.projectionQuotientOrder Q S π ∧
    ⟨x, (A.transportedProjectionQuotientInverse B e K ρ v) ‘ ((A.projectionQuotientMap Q π u) ‘ x)⟩ₖ ∈
      A.projectionQuotientOrder Q S π := by
  have hmap := A.transportedProjectionQuotientMap_maps B e hm hc hπ hρ hu hg
  have hinv := A.transportedProjectionQuotientInverse_maps B e hm hc hπ hρ hv hg hi
  have hx' := function_value_mem hmap hx
  have hx'' := function_value_mem hinv hx'
  obtain ⟨p, hp, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
  rw [A.projectionQuotientMap_value hu hp hx] at hx' hx'' ⊢
  rw [A.transportedProjectionQuotientInverse_value B e hv (function_value_mem hu hp) hx'] at hx'' ⊢
  constructor
  · exact (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
      ⟨A.check_kpair _ _ ▸ (A.check_mem_iff _ _).mpr (hl p hp).1, hx'', hx⟩
  · exact (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
      ⟨A.check_kpair _ _ ▸ (A.check_mem_iff _ _).mpr (hl p hp).2, hx, hx''⟩

end ForcingContext
end ZFVP
