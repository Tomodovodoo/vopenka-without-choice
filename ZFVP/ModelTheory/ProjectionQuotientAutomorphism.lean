import ZFVP.ModelTheory.ProjectionQuotient
import ZFVP.ModelTheory.ForcingIsomorphismTransport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

noncomputable def projectionQuotientAutomorphism (A : ForcingContext V) (Q π f : V) : A.Model :=
  definableGraph (A.projectionQuotient Q π) (fun x ↦ (A.check f) ‘ x) (by definability)

theorem projectionQuotientAutomorphism_check_value (A : ForcingContext V) {Q S π f p : V}
    (hπ : π ∈ A.P ^ Q) (hf : IsForcingAutomorphism Q S f)
    (hp : p ∈ Q) (hpG : π ‘ p ∈ A.G) :
    (A.projectionQuotientAutomorphism Q π f) ‘ (A.check p) = A.check (f ‘ p) := by
  let := IsFunction.of_mem hf.1
  rw [projectionQuotientAutomorphism, value_definableGraph _ _ _ ((A.check_mem_projectionQuotient_iff hπ).mpr ⟨hp,hpG⟩)]
  exact A.check_value ((domain_eq_of_mem_function hf.1).symm ▸ hp)

theorem projectionQuotientAutomorphism_isomorphism (A : ForcingContext V) {Q S π f : V}
    (hπ : π ∈ A.P ^ Q) (hf : IsForcingAutomorphism Q S f)
    (hfix : ∀ p ∈ Q, π ‘ (f ‘ p) = π ‘ p) :
    IsForcingAutomorphism (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)
      (A.projectionQuotientAutomorphism Q π f) := by
  have hfi : IsForcingIsomorphism Q S Q S f := hf
  let := IsFunction.of_mem hf.1
  let := IsFunction.of_mem hfi.inverse_maps
  let K := A.projectionQuotient Q π
  let F := fun x : A.Model ↦ (A.check f) ‘ x
  let J := fun x : A.Model ↦ (A.check (converseGraph f)) ‘ x
  have hF : ℒₛₑₜ-function₁ F := by dsimp only [F]; definability
  have hval : ∀ p ∈ Q, F (A.check p) = A.check (f ‘ p) := fun p hp ↦
    A.check_value ((domain_eq_of_mem_function hf.1).symm ▸ hp)
  have hival : ∀ p ∈ Q, J (A.check p) = A.check ((converseGraph f) ‘ p) := fun p hp ↦
    A.check_value ((domain_eq_of_mem_function hfi.inverse_maps).symm ▸ hp)
  have hifix : ∀ p ∈ Q, π ‘ ((converseGraph f) ‘ p) = π ‘ p := by
    intro p hp
    have hh := hfix _ (function_value_mem hfi.inverse_maps hp)
    rw [hfi.value_inverse hp] at hh
    exact hh.symm
  have hmaps : ∀ x ∈ K, F x ∈ K := by
    intro x hx
    obtain ⟨p,hp,hpG,rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
    rw [hval p hp]
    exact (A.check_mem_projectionQuotient_iff hπ).mpr ⟨function_value_mem hf.1 hp, (hfix p hp).symm ▸ hpG⟩
  have himaps : ∀ x ∈ K, J x ∈ K := by
    intro x hx
    obtain ⟨p,hp,hpG,rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
    rw [hival p hp]
    exact (A.check_mem_projectionQuotient_iff hπ).mpr ⟨function_value_mem hfi.inverse_maps hp, (hifix p hp).symm ▸ hpG⟩
  have hJF : ∀ x ∈ K, J (F x) = x := by
    intro x hx
    obtain ⟨p,hp,_,rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
    rw [hval p hp, hival _ (function_value_mem hf.1 hp), hfi.inverse_value hp]
  have hFJ : ∀ x ∈ K, F (J x) = x := by
    intro x hx
    obtain ⟨p,hp,_,rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
    rw [hival p hp, hval _ (function_value_mem hfi.inverse_maps hp), hfi.value_inverse hp]
  have hg : A.projectionQuotientAutomorphism Q π f ∈ K ^ K :=
    definableGraph_mem_function_of_mapsTo K K F hF hmaps
  refine ⟨hg, ?_, ?_, ?_⟩
  · intro x y z hx hy
    obtain ⟨hx,hzx⟩ := (pair_mem_definableGraph_iff K F hF x z).mp hx
    obtain ⟨hy,hzy⟩ := (pair_mem_definableGraph_iff K F hF y z).mp hy
    have hh := congrArg J (hzx.symm.trans hzy)
    simpa only [hJF x hx, hJF y hy] using hh
  · apply subset_antisymm (range_subset_of_mem_function hg)
    intro x hx
    have hh : (A.projectionQuotientAutomorphism Q π f) ‘ (J x) = x :=
      (value_definableGraph K F hF (himaps x hx)).trans (hFJ x hx)
    exact hh ▸ value_mem_range hg (himaps x hx)
  · intro x hx y hy
    change x ∈ K at hx
    change y ∈ K at hy
    have hvx : (A.projectionQuotientAutomorphism Q π f) ‘ x = F x := value_definableGraph K F hF hx
    have hvy : (A.projectionQuotientAutomorphism Q π f) ‘ y = F y := value_definableGraph K F hF hy
    rw [hvx, hvy, A.projectionQuotientOrder_pair_iff, A.projectionQuotientOrder_pair_iff]
    change (⟨x,y⟩ₖ ∈ A.check S ∧ x ∈ K ∧ y ∈ K) ↔
      (⟨F x,F y⟩ₖ ∈ A.check S ∧ F x ∈ K ∧ F y ∈ K)
    simp only [hx,hy,hmaps x hx,hmaps y hy,and_true]
    obtain ⟨p,hp,_,rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
    obtain ⟨q,hq,_,rfl⟩ := (A.mem_projectionQuotient_iff hπ y).mp hy
    rw [hval p hp, hval q hq, ← A.check_kpair, ← A.check_kpair, A.check_mem_iff, A.check_mem_iff]
    exact hf.2.2.2 p hp q hq

end ForcingContext
end ZFVP
