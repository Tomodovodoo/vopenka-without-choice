import ZFVP.SetTheory.UsubaCollapseTargets
import ZFVP.SetTheory.LowenheimSkolemDictionary
import ZFVP.SetTheory.UniformLeastOrdinalChoice

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def usubaTargetPropertyFormula : SetTheorySemisentence 2 :=
  f“ξ lam. !lsCardinalFormula lam ∧ !internalCofinalityFormula lam ∈ lam ∧
    ξ ∈ !internalCofinalityFormula lam ∧ ∃ ν,
      !weaklyLSCardinalFormula ν ∧ ξ ⊆ ν ∧ ν ⊆ !internalCofinalityFormula lam”

def usubaLeastTargetFormula : SetTheorySemisentence 2 :=
  leastOrdinalOrZeroFormula usubaTargetPropertyFormula

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsUsubaTarget (ξ lam : V) : Prop :=
  IsLSCardinal lam ∧ internalCofinality lam ∈ lam ∧ ξ ∈ internalCofinality lam ∧
    ∃ ν : V, IsWeaklyLSCardinal ν ∧ ξ ⊆ ν ∧ ν ⊆ internalCofinality lam

instance usubaTargetPropertyFormula_defined :
    ℒₛₑₜ-relation[V] IsUsubaTarget via usubaTargetPropertyFormula :=
  ⟨fun v ↦ by simp [usubaTargetPropertyFormula, IsUsubaTarget]⟩

instance isUsubaTarget_definable : ℒₛₑₜ-relation[V] IsUsubaTarget :=
  usubaTargetPropertyFormula_defined.to_definable

noncomputable def usubaLeastTarget (ξ : V) : V :=
  leastOrdinalOrZero IsUsubaTarget (by definability) ξ

instance usubaLeastTarget_definable : ℒₛₑₜ-function₁[V] usubaLeastTarget := by
  unfold usubaLeastTarget
  infer_instance

instance usubaLeastTargetFormula_defined :
    ℒₛₑₜ-function₁[V] usubaLeastTarget via usubaLeastTargetFormula := by
  refine ⟨fun v ↦ ?_⟩
  change usubaLeastTargetFormula.Evalb v ↔ v 0 = usubaLeastTarget (v 1)
  have hv : ![v 0, v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [← hv]
  exact eval_leastOrdinalOrZeroFormula usubaTargetPropertyFormula IsUsubaTarget
    (by definability) (fun x y ↦ usubaTargetPropertyFormula_defined.iff ![x, y]) _ _

instance usubaLeastTarget_ordinal (ξ : V) : IsOrdinal (usubaLeastTarget ξ) :=
  leastOrdinalOrZero_ordinal _ _ _

theorem usubaLeastTarget_spec
    (hLS : ∀ β : V, IsOrdinal β → ∃ κ : V, β ∈ κ ∧ IsLSCardinal κ)
    (ξ : V) [IsOrdinal ξ] : IsUsubaTarget ξ (usubaLeastTarget ξ) := by
  obtain ⟨hξ, hν, hlam, _, hcf, hνcf, hcflam⟩ := usubaCollapseTarget_spec hLS ξ
  have := hν.1.1
  have := hcf.1.1
  have htarget : IsUsubaTarget ξ (usubaCollapseTarget ξ) :=
    ⟨hlam, hcflam, IsOrdinal.toIsTransitive.mem_trans hξ hνcf,
      usubaAuxiliaryLS ξ, hν, IsOrdinal.toIsTransitive.transitive _ hξ,
      IsOrdinal.toIsTransitive.transitive _ hνcf⟩
  exact (leastOrdinalOrZero_spec IsUsubaTarget (by definability) ξ
    ⟨usubaCollapseTarget ξ, hlam.1.1, htarget⟩).2.1

end ZFVP

