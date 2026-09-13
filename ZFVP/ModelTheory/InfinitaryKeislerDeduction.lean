import ZFVP.ModelTheory.InfinitaryKeislerSoundness
import ZFVP.ModelTheory.InfinitaryBooleanDeduction
import ZFVP.ModelTheory.InfinitaryRewritingLaws

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace KeislerDerivation
variable {L : Language} [L.Eq] {Γ Δ : Set (Sentence L)}

 theorem identity {n} (φ : Formula L n) : KeislerDerivation Γ (φ.imp φ) :=
  .boolean (BooleanDerivation.identity φ)

 theorem weaken_imp {n} {φ : Formula L n} (d : KeislerDerivation Γ φ) (ψ : Formula L n) :
    KeislerDerivation Γ (ψ.imp φ) := .mp (.boolean (.k φ ψ)) d

 theorem imp_trans {n} {φ ψ χ : Formula L n}
    (d : KeislerDerivation Γ (φ.imp ψ)) (e : KeislerDerivation Γ (ψ.imp χ)) :
    KeislerDerivation Γ (φ.imp χ) :=
  .mp (.mp (.boolean (.s φ ψ χ)) (e.weaken_imp φ)) d

 theorem rename {n m} {φ : Formula L n} (d : KeislerDerivation Γ φ) (ρ : Fin n → Fin m) :
    KeislerDerivation Γ (φ.rename ρ) := by
  rw [← Formula.subst_bvar_eq_rename]
  exact .substitution _ d

/-- Replacing every hypothesis by its derivation composes full Keisler proof trees. -/
theorem cut {n} {φ : Formula L n} (d : KeislerDerivation Γ φ)
    (h : ∀ ψ ∈ Γ, KeislerDerivation Δ ψ) : KeislerDerivation Δ φ := by
  induction d with
  | hypothesis hp => exact (h _ hp).rename _
  | boolean h => exact .boolean h
  | truth => exact .truth
  | nonempty => exact .nonempty
  | expansion φ => exact .expansion φ
  | instantiation φ t => exact .instantiation φ t
  | distribution φ ψ => exact .distribution φ ψ
  | exDistribution φ ψ => exact .exDistribution φ ψ
  | vacuous φ => exact .vacuous φ
  | eqRefl t => exact .eqRefl t
  | eqSubst φ s t => exact .eqSubst φ s t
  | qSmall i j => exact .qSmall i j
  | qInterchange φ => exact .qInterchange φ
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | conjunction φ _ ih => exact .conjunction φ ih
  | generalization _ ih => exact .generalization ih
  | substitution σ _ ih => exact .substitution σ ih

 theorem mono {n} {φ : Formula L n} (d : KeislerDerivation Γ φ) (h : Γ ⊆ Δ) :
    KeislerDerivation Δ φ := by
  apply d.cut
  intro ψ hψ
  have e : KeislerDerivation Δ (ψ.rename (Fin.elim0 : Fin 0 → Fin 0)) := .hypothesis (h hψ)
  have hid : (Fin.elim0 : Fin 0 → Fin 0) = id := Subsingleton.elim _ _
  simpa [hid] using e

/-- A sentence assumption can be discharged throughout the exact calculus, including
countable branching, generalization, and capture-avoiding substitution. -/
theorem deduction {φ : Sentence L} {n} {ψ : Formula L n}
    (d : KeislerDerivation (insert φ Γ) ψ) :
    KeislerDerivation Γ ((φ.rename (Fin.elim0 : Fin 0 → Fin n)).imp ψ) := by
  induction d with
  | hypothesis h =>
      rcases Set.mem_insert_iff.mp h with rfl | h
      · exact identity _
      · exact (KeislerDerivation.hypothesis h).weaken_imp _
  | boolean h => exact (KeislerDerivation.boolean h).weaken_imp _
  | truth => exact KeislerDerivation.truth.weaken_imp _
  | nonempty => exact KeislerDerivation.nonempty.weaken_imp _
  | expansion ψ => exact (KeislerDerivation.expansion ψ).weaken_imp _
  | instantiation ψ t => exact (KeislerDerivation.instantiation ψ t).weaken_imp _
  | distribution ψ χ => exact (KeislerDerivation.distribution ψ χ).weaken_imp _
  | exDistribution ψ χ => exact (KeislerDerivation.exDistribution ψ χ).weaken_imp _
  | vacuous ψ => exact (KeislerDerivation.vacuous ψ).weaken_imp _
  | eqRefl t => exact (KeislerDerivation.eqRefl t).weaken_imp _
  | eqSubst ψ s t => exact (KeislerDerivation.eqSubst ψ s t).weaken_imp _
  | qSmall i j => exact (KeislerDerivation.qSmall i j).weaken_imp _
  | qInterchange ψ => exact (KeislerDerivation.qInterchange ψ).weaken_imp _
  | mp _ _ ih₁ ih₂ => exact .mp (.mp (.boolean (.s _ _ _)) ih₁) ih₂
  | conjunction ψ _ ih => exact .mp (.boolean (.distribution _ ψ)) (.conjunction _ ih)
  | @generalization n ψ d ih =>
      let a : Formula L n := φ.rename Fin.elim0
      have e : KeislerDerivation Γ ((Formula.all (a.rename Fin.succ)).imp (Formula.all ψ)) := by
        apply KeislerDerivation.mp (KeislerDerivation.distribution _ ψ)
        apply KeislerDerivation.generalization
        simpa [a] using ih
      exact imp_trans (KeislerDerivation.vacuous a) e
  | substitution σ d ih =>
      simpa using KeislerDerivation.substitution σ ih

end KeislerDerivation
end ZFVP.Infinitary
