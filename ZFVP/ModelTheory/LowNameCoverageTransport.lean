import ZFVP.ModelTheory.ForcingNameActionLowRank
import ZFVP.ModelTheory.ForcingLowRankNames
import ZFVP.SetTheory.UniformRank
import ZFVP.SetTheory.MembershipIso

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

def HasLocalLowNameCoverage (A : ForcingContext V) (η Q π : V) : Prop :=
  ∀ x ∈ hierarchy (A.check η), ∃ τ ∈ hierarchy η, IsForcingName Q τ ∧
    ∃ σ : ForcingName A.P, σ.val = nameAction π τ ∧ x = A.ofName σ

theorem hasLocalLowNameCoverage_congr {A B : ForcingContext V} (h : A = B) (η Q π : V) :
    A.HasLocalLowNameCoverage η Q π ↔ B.HasLocalLowNameCoverage η Q π := by
  subst B
  rfl

theorem low_name_coverage_of_local_equiv (A B : ForcingContext V) {η Q π ρ : V}
    (hη : IsChoicelessInaccessible η) (hπ : π ∈ A.P ^ Q) (hρ : ρ ∈ B.P ^ A.P)
    (hB : B.P ⊆ hierarchy η) (e : A.Model ≃ B.Model)
    (hem : ∀ x y, e x ∈ e y ↔ x ∈ y) (hec : ∀ x : V, e (A.check x) = B.check x)
    (hen : ∀ τ : ForcingName A.P, e (A.ofName τ) =
      B.ofName ⟨nameAction ρ τ.val, nameAction_isName hρ τ.property⟩)
    (hcov : A.HasLocalLowNameCoverage η Q π) :
    ∀ x ∈ hierarchy (B.check η), ∃ τ : ForcingName B.P,
      τ.val ∈ hierarchy η ∧ x = B.ofName τ := by
  let := hη.1
  let j := ElementaryMap.ofMembershipIso e hem
  have hj : j (hierarchy (A.check η)) = hierarchy (B.check η) := by
    rw [j.map_hierarchy]
    exact congrArg hierarchy (hec η)
  intro x hx
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy : y ∈ hierarchy (A.check η) := by
    apply (hem y (hierarchy (A.check η))).mp
    change e y ∈ j (hierarchy (A.check η))
    rwa [hj]
  obtain ⟨τ, hτ, hn, σ, hσ, rfl⟩ := hcov y hy
  refine ⟨⟨nameAction ρ σ.val, nameAction_isName hρ σ.property⟩, ?_, hen σ⟩
  change nameAction ρ σ.val ∈ hierarchy η
  rw [hσ, nameAction_compose hπ hρ hn]
  exact nameAction_mem_hierarchy_of_low_target hη (compose_function hπ hρ) hB hτ hn

end ForcingContext
end ZFVP


