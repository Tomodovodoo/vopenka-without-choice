import ZFVP.ModelTheory.InfinitaryBooleanDerivation

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace BooleanDerivation
variable {L : Language} {n : ℕ} {Γ Δ : Set (Formula L n)}

/-- Derivations can be reused in a larger hypothesis set. -/
theorem mono {φ : Formula L n} (d : BooleanDerivation Γ φ) (h : Γ ⊆ Δ) :
    BooleanDerivation Δ φ := by
  induction d with
  | hypothesis hp => exact .hypothesis (h hp)
  | k φ ψ => exact .k φ ψ
  | s φ ψ χ => exact .s φ ψ χ
  | dne φ => exact .dne φ
  | contraposition φ ψ => exact .contraposition φ ψ
  | projection φ i => exact .projection φ i
  | distribution φ ψ => exact .distribution φ ψ
  | qMono φ ψ => exact .qMono φ ψ
  | qUnion φ => exact .qUnion φ
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | conjunction φ _ ih => exact .conjunction φ ih

/-- Reflexivity of implication is derived from K and S. -/
theorem identity (φ : Formula L n) : BooleanDerivation Γ (φ.imp φ) :=
  .mp (.mp (.s φ (φ.imp φ) φ) (.k φ (φ.imp φ))) (.k φ φ)

/-- Discharge one assumption, including across a countably branching conjunction rule. -/
theorem deduction {φ ψ : Formula L n} (d : BooleanDerivation (insert φ Γ) ψ) :
    BooleanDerivation Γ (φ.imp ψ) := by
  induction d with
  | hypothesis h =>
      rcases Set.mem_insert_iff.mp h with rfl | h
      · exact identity _
      · exact .mp (.k _ φ) (.hypothesis h)
  | k ψ χ => exact .mp (.k _ φ) (.k ψ χ)
  | s ψ χ θ => exact .mp (.k _ φ) (.s ψ χ θ)
  | dne ψ => exact .mp (.k _ φ) (.dne ψ)
  | contraposition ψ χ => exact .mp (.k _ φ) (.contraposition ψ χ)
  | projection ψ i => exact .mp (.k _ φ) (.projection ψ i)
  | distribution ψ χ => exact .mp (.k _ φ) (.distribution ψ χ)
  | qMono ψ χ => exact .mp (.k _ φ) (.qMono ψ χ)
  | qUnion ψ => exact .mp (.k _ φ) (.qUnion ψ)
  | mp d₁ d₂ ih₁ ih₂ => exact .mp (.mp (.s _ _ _) ih₁) ih₂
  | conjunction ψ _ ih => exact .mp (.distribution φ ψ) (.conjunction _ ih)

/-- Substitute proofs of all hypotheses into an actual derivation tree. -/
theorem cut {φ : Formula L n} (d : BooleanDerivation Γ φ)
    (h : ∀ ψ ∈ Γ, BooleanDerivation Δ ψ) : BooleanDerivation Δ φ := by
  induction d with
  | hypothesis hp => exact h _ hp
  | k φ ψ => exact .k φ ψ
  | s φ ψ χ => exact .s φ ψ χ
  | dne φ => exact .dne φ
  | contraposition φ ψ => exact .contraposition φ ψ
  | projection φ i => exact .projection φ i
  | distribution φ ψ => exact .distribution φ ψ
  | qMono φ ψ => exact .qMono φ ψ
  | qUnion φ => exact .qUnion φ
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | conjunction φ _ ih => exact .conjunction φ ih

end BooleanDerivation
end ZFVP.Infinitary

