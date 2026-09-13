import ZFVP.ModelTheory.InfinitaryHenkinFirstOrderTruth
import ZFVP.ModelTheory.InfinitaryWeakSemantics

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage KeislerDerivation FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))} (H : FragmentExtension Γ (FragmentClosure.carrier S))

/-- The subset determined by a unary formula's closed instances. -/
def fiber (φ : Formula (limit L) 1) : Set H.Domain := {x | φ.substFirst x.out ∈ H.carrier}

theorem fiber_classOf {φ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) (t : Semiterm (limit L) Empty 0) :
    H.classOf t ∈ H.fiber φ ↔ φ.substFirst t ∈ H.carrier :=
  H.substFirst_mem_congr φ hφ (H.representative_rel t)

theorem q_mem_mono {φ ψ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier S)
    (hs : H.fiber φ ⊆ H.fiber ψ) : .q φ ∈ H.carrier → .q ψ ∈ H.carrier := by
  have hall : Formula.all (φ.imp ψ) ∈ H.carrier := by
    apply (H.all_mem_iff (imp_closed hφ hψ)).mpr
    intro t
    change (φ.imp ψ).subst (Fin.cases t Semiterm.bvar) ∈ H.carrier
    rw [Formula.subst_imp]
    apply (H.imp_mem_iff (subst_closed hφ _) (subst_closed hψ _)).mpr
    intro hp
    exact (H.fiber_classOf hψ t).mp (hs ((H.fiber_classOf hφ t).mpr hp))
  have hax : Formula.qMonotonicity φ ψ ∈ H.carrier :=
    H.of_theorem (imp_closed (all_closed (imp_closed hφ hψ))
      (imp_closed (q_closed hφ) (q_closed hψ))) (.boolean (.qMono φ ψ))
  have hi := H.mp_mem (imp_closed (q_closed hφ) (q_closed hψ)) hax hall
  exact fun hq ↦ H.mp_mem (q_closed hψ) hi hq

theorem q_mem_extensional {φ ψ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier S)
    (hs : H.fiber φ = H.fiber ψ) : .q φ ∈ H.carrier ↔ .q ψ ∈ H.carrier :=
  ⟨H.q_mem_mono hφ hψ hs.subset, H.q_mem_mono hψ hφ hs.symm.subset⟩

/-- Upward closure of the fragment's Q-large definable subsets. -/
def weakQuantifier (A : Set H.Domain) : Prop :=
  ∃ φ : Formula (limit L) 1, ⟨1, φ⟩ ∈ FragmentClosure.carrier S ∧
    .q φ ∈ H.carrier ∧ H.fiber φ ⊆ A

theorem weakQuantifier_mono {A B : Set H.Domain} (h : A ⊆ B) :
    H.weakQuantifier A → H.weakQuantifier B := by
  rintro ⟨φ, hφ, hq, hs⟩
  exact ⟨φ, hφ, hq, hs.trans h⟩

theorem weakQuantifier_fiber {φ : Formula (limit L) 1}
    (hφ : ⟨1, φ⟩ ∈ FragmentClosure.carrier S) :
    H.weakQuantifier (H.fiber φ) ↔ .q φ ∈ H.carrier := by
  constructor
  · rintro ⟨ψ, hψ, hq, hs⟩
    exact H.q_mem_mono hψ hφ hs hq
  · intro hq
    exact ⟨φ, hφ, hq, Set.Subset.rfl⟩

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary
