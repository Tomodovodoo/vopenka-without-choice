import ZFVP.ModelTheory.InfinitaryHenkinQDensity

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage KeislerDerivation FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))} (H : FragmentExtension Γ (FragmentClosure.carrier S))

theorem weakQuantifier_fiber_union_iff {φ ψ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier S) :
    H.weakQuantifier (H.fiber φ ∪ H.fiber ψ) ↔
      H.weakQuantifier (H.fiber φ) ∨ H.weakQuantifier (H.fiber ψ) := by
  rw [← H.fiber_or hφ hψ, H.weakQuantifier_fiber (or_closed hφ hψ),
    H.q_mem_or_iff hφ hψ, H.weakQuantifier_fiber hφ, H.weakQuantifier_fiber hψ]

/-- Closed terms represent all points, so every finite subset is a fragment fiber. -/
theorem finite_set_is_fiber {A : Set H.Domain} (hA : A.Finite) :
    ∃ φ : Formula (limit L) 1, ⟨1, φ⟩ ∈ FragmentClosure.carrier S ∧ H.fiber φ = A := by
  classical
  induction A, hA using Set.Finite.induction_on with
  | empty => exact H.empty_is_fiber
  | @insert a A ha hA ih =>
    obtain ⟨φ, hφ, hfφ⟩ := H.singleton_is_fiber a
    obtain ⟨ψ, hψ, hfψ⟩ := ih
    refine ⟨φ.or ψ, or_closed hφ hψ, ?_⟩
    rw [H.fiber_or hφ hψ, hfφ, hfψ, Set.singleton_union]

/-- Binary union and two-point smallness rule out every finite subset. -/
theorem weakQuantifier_not_finite {A : Set H.Domain} (hA : A.Finite) :
    ¬H.weakQuantifier A := by
  classical
  induction A, hA using Set.Finite.induction_on with
  | empty => exact H.weakQuantifier_not_empty
  | @insert a A ha hA ih =>
    obtain ⟨φ, hφ, hfφ⟩ := H.singleton_is_fiber a
    obtain ⟨ψ, hψ, hfψ⟩ := H.finite_set_is_fiber hA
    have hs := H.weakQuantifier_fiber_union_iff hφ hψ
    rw [hfφ, hfψ, Set.singleton_union] at hs
    intro hq
    rcases hs.mp hq with hp | hp
    · exact (H.weakQuantifier_not_subset_twoPoints a a (by simp)) hp
    · exact ih hp

theorem weakQuantifier_infinite {A : Set H.Domain} (hA : H.weakQuantifier A) :
    A.Infinite := fun hf ↦ H.weakQuantifier_not_finite hf hA

theorem q_mem_fiber_infinite {φ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) (hq : .q φ ∈ H.carrier) :
    (H.fiber φ).Infinite :=
  H.weakQuantifier_infinite ((H.weakQuantifier_fiber hφ).mpr hq)

theorem q_mem_outside_finite {φ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) (hq : .q φ ∈ H.carrier)
    {A : Set H.Domain} (hA : A.Finite) : ∃ x ∈ H.fiber φ, x ∉ A := by
  classical
  by_contra hn
  apply H.q_mem_fiber_infinite hφ hq
  apply hA.subset
  intro x hx
  by_contra hxA
  exact hn ⟨x, hx, hxA⟩

theorem q_mem_closedTerm_outside_finite {φ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) (hq : .q φ ∈ H.carrier)
    {A : Set H.Domain} (hA : A.Finite) :
    ∃ t : Semiterm (limit L) Empty 0, φ.substFirst t ∈ H.carrier ∧ H.classOf t ∉ A := by
  obtain ⟨x, hx, hxA⟩ := H.q_mem_outside_finite hφ hq hA
  refine ⟨x.out, hx, ?_⟩
  have he : H.classOf x.out = x := Quotient.out_eq x
  rwa [he]

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary
