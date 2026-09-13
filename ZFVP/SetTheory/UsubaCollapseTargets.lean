import ZFVP.SetTheory.UsubaLSLimitCofinality
import ZFVP.SetTheory.UsubaLSUniform
import ZFVP.SetTheory.SingularWeaklyLSSuccessor
import ZFVP.SetTheory.StrongLSWeakLS
import ZFVP.SetTheory.FiniteCofinality

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def usubaAuxiliaryLS (ξ : V) : V := usubaLSLimit ξ ω

instance usubaAuxiliaryLS_definable : ℒₛₑₜ-function₁[V] usubaAuxiliaryLS := by
  unfold usubaAuxiliaryLS
  apply Language.DefinableFunction₂.comp (F := usubaLSLimit) <;> definability

noncomputable def usubaCollapseTarget (ξ : V) : V :=
  usubaLSLimit (hartogsNumber (usubaAuxiliaryLS ξ)) (hartogsNumber (usubaAuxiliaryLS ξ))

instance usubaCollapseTarget_definable : ℒₛₑₜ-function₁[V] usubaCollapseTarget := by
  unfold usubaCollapseTarget
  apply Language.DefinableFunction₂.comp (F := usubaLSLimit) <;> definability

theorem usubaAuxiliaryLS_spec
    (hLS : ∀ β : V, IsOrdinal β → ∃ κ : V, β ∈ κ ∧ IsLSCardinal κ)
    (ξ : V) [IsOrdinal ξ] :
    ξ ∈ usubaAuxiliaryLS ξ ∧ IsLSCardinal (usubaAuxiliaryLS ξ) ∧
      internalCofinality (usubaAuxiliaryLS ξ) = ω ∧
      internalCofinality (usubaAuxiliaryLS ξ) ∈ usubaAuxiliaryLS ξ := by
  have hlim : ∀ j ∈ (ω : V), succ j ∈ (ω : V) :=
    fun j hj ↦ regularCardinal_succ_closed omega_regular hj
  have hs := usubaLSLimit_isLS hLS (ξ := ξ) (α := (ω : V))
    (show IsNonempty (ω : V) from ⟨∅, by simp⟩) hlim
  have hcf : internalCofinality (usubaAuxiliaryLS ξ) = ω :=
    (usubaLSLimit_cofinality hLS hlim).trans omega_regular.2.2
  exact ⟨hs.1, hs.2, hcf, hcf.symm ▸ hs.2.2.1⟩

/-- The two canonical targets used immediately before Usuba Corollary 4.8.
The target has a regular cofinality strictly above a weakly LS cardinal,
and both lie above the requested bound. -/
theorem usubaCollapseTarget_spec
    (hLS : ∀ β : V, IsOrdinal β → ∃ κ : V, β ∈ κ ∧ IsLSCardinal κ)
    (ξ : V) [IsOrdinal ξ] :
    ξ ∈ usubaAuxiliaryLS ξ ∧ IsWeaklyLSCardinal (usubaAuxiliaryLS ξ) ∧
      IsLSCardinal (usubaCollapseTarget ξ) ∧
      internalCofinality (usubaCollapseTarget ξ) = hartogsNumber (usubaAuxiliaryLS ξ) ∧
      IsRegularCardinal (internalCofinality (usubaCollapseTarget ξ)) ∧
      usubaAuxiliaryLS ξ ∈ internalCofinality (usubaCollapseTarget ξ) ∧
      internalCofinality (usubaCollapseTarget ξ) ∈ usubaCollapseTarget ξ := by
  obtain ⟨hξ, hν, _, hsing⟩ := usubaAuxiliaryLS_spec hLS ξ
  have := hν.1.1
  have hweak := hν.weaklyLSCardinal
  have hreg := hweak.singular_successor_regular hsing
  have := hreg.1.1
  have hlim : ∀ j ∈ hartogsNumber (usubaAuxiliaryLS ξ),
      succ j ∈ hartogsNumber (usubaAuxiliaryLS ξ) :=
    fun j hj ↦ regularCardinal_succ_closed hreg hj
  have hs := usubaLSLimit_isLS hLS
    (ξ := hartogsNumber (usubaAuxiliaryLS ξ))
    (show IsNonempty (hartogsNumber (usubaAuxiliaryLS ξ)) from
      ⟨∅, hreg.2.1 ∅ (by simp)⟩) hlim
  have hcf : internalCofinality (usubaCollapseTarget ξ) =
      hartogsNumber (usubaAuxiliaryLS ξ) :=
    (usubaLSLimit_cofinality hLS hlim).trans hreg.2.2
  refine ⟨hξ, hweak, hs.2, hcf, hcf.symm ▸ hreg, ?_, hcf.symm ▸ hs.1⟩
  rw [hcf]
  exact ordinal_cardLE_iff_mem_hartogsNumber.mp (CardLE.refl _)

end ZFVP
