import ZFVP.SetTheory.ForcingFormulaNameAction
import ZFVP.SetTheory.NameActionClosure
import ZFVP.SetTheory.CheckNames

/-! Weak homogeneity: when any two conditions have compatible automorphic images (by automorphisms
fixing the top), every statement about check names that is forced by some condition is forced by
the top. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Weak homogeneity via automorphisms fixing the top condition. -/
def IsWeaklyHomogeneous (P R one : V) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ∃ π, IsForcingAutomorphism P R π ∧ π ‘ one = one ∧
    ForcingCompatible P R (π ‘ p) q

/-- In a weakly homogeneous poset, a statement about check names forced by some condition is
forced by the top. -/
theorem forced_by_top_of_homogeneous {P R one : V} (hR : IsForcingPreorder P R)
    (hone : IsForcingTop P R one) (hhom : IsWeaklyHomogeneous P R one) {n : ℕ}
    (φ : SetTheorySemisentence n) (a : Fin n → V) {p : V}
    (hp : p ∈ forcingFormula P R φ (standardTuple (fun i ↦ checkName one (a i)))) :
    one ∈ forcingFormula P R φ (standardTuple (fun i ↦ checkName one (a i))) := by
  have hreg := forcingFormula_regular hR φ (standardTuple (fun i ↦ checkName one (a i)))
  have hpP : p ∈ P := hreg.1 p hp
  apply hreg.2.2 one hone.1
  intro q hq _
  obtain ⟨π, hπ, hfix, r, hr, hrπ, hrq⟩ := hhom p hpP q hq
  have hπp : π ‘ p ∈ forcingFormula P R φ (standardTuple (fun i ↦ checkName one (a i))) := by
    have h := (forcingFormula_nameAction_iff hR hπ φ (fun i ↦ checkName one (a i))
      (fun i ↦ checkName_isName hone.1 (a i)) hpP).mpr hp
    have hfix' : (fun i ↦ nameAction π (checkName one (a i))) = fun i ↦ checkName one (a i) :=
      funext (fun i ↦ nameAction_checkName hone.1 hfix (a i))
    rwa [hfix'] at h
  exact ⟨r, hreg.2.1 _ hπp r hr hrπ, hrq⟩

end ZFVP
