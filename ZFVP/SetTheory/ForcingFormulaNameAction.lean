import ZFVP.SetTheory.ClassFormulaForcingAction
import ZFVP.SetTheory.FormulaForcing
import ZFVP.SetTheory.ForcingAutomorphisms

/-! Equivariance of the ordinary forcing relation under forcing automorphisms acting on names,
and names all of whose conditions are fixed by an automorphism are themselves fixed. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingFormula_nameAction_iff {P R π : V} (hR : IsForcingPreorder P R)
    (hπ : IsForcingAutomorphism P R π) {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V)
    (hv : ∀ i, IsForcingName P (v i)) {p : V} (hp : p ∈ P) :
    π ‘ p ∈ forcingFormula P R φ (standardTuple (fun i ↦ nameAction π (v i))) ↔
      p ∈ forcingFormula P R φ (standardTuple v) := by
  have hinv := forcingAutomorphism_inverse hπ
  exact classForcingFormula_nameAction_iff hR hπ (IsForcingName P) (by definability)
    (fun _ h ↦ h) (fun x hx ↦ nameAction_isName hπ.1 hx)
    (fun y hy ↦ ⟨nameAction (converseGraph π) y, nameAction_isName hinv.1 hy, by
      rw [nameAction_compose hinv.1 hπ.1 hy, forcingAutomorphism_inverse_compose hπ,
        nameAction_identity hy]⟩)
    φ v hv hp

/-- A name whose conditions are all fixed by `π` is fixed by the action of `π`. -/
theorem nameAction_eq_self_of_fixed {P π τ : V} (hτ : IsForcingName P τ)
    (hfix : ∀ σ ∈ nameClosure τ, ∀ υ p, ⟨υ, p⟩ₖ ∈ σ → π ‘ p = p) : nameAction π τ = τ := by
  revert hfix
  apply forcingName_induction P
    (fun τ ↦ (∀ σ ∈ nameClosure τ, ∀ υ p, ⟨υ, p⟩ₖ ∈ σ → π ‘ p = p) → nameAction π τ = τ)
    (by definability) ?_ τ hτ
  intro τ hτ ih hfix
  have hsub : ∀ σ p, ⟨σ, p⟩ₖ ∈ τ → ∀ σ' ∈ nameClosure σ, ∀ υ q, ⟨υ, q⟩ₖ ∈ σ' → π ‘ q = q :=
    fun σ p hσp σ' hσ' υ q hq ↦
      hfix σ' (nameClosure_mem_mono (subname_mem_nameClosure hσp) σ' hσ') υ q hq
  ext z
  rw [mem_nameAction_iff hτ]
  constructor
  · rintro ⟨σ, p, hσp, rfl⟩
    rw [ih σ p hσp (hsub σ p hσp), hfix τ (mem_nameClosure_self τ) σ p hσp]
    exact hσp
  · intro hz
    obtain ⟨υ, p, _, rfl⟩ := hτ τ (mem_nameClosure_self τ) z hz
    refine ⟨υ, p, hz, ?_⟩
    rw [ih υ p hz (hsub υ p hz), hfix τ (mem_nameClosure_self τ) υ p hz]

end ZFVP
