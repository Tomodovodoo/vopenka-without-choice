import ZFVP.ModelTheory.WoodinSparseLocalPrefixRank
import ZFVP.ModelTheory.ForcingCodeUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def lowRankNameSetValueFormula : SetTheorySemisentence 3 :=
  f“D P η. ∀ τ, τ ∈ D ↔ τ ∈ !hierarchyFormula η ∧ !forcingNameFormula P τ”

def localSparsePrefixForcingFormula (stage : SetTheorySemisentence 2) : SetTheorySemisentence 4 :=
  f“n φ b p. ∃ i, ∃ η, !IsOrdinal.dfn i ∧ !IsOrdinal.dfn η ∧ (!isEmpty) ∈ η ∧
    ∃ C, !stage C i ∧ ∃ P, ∃ R, ∃ D,
      P = !value.dfn (!forcingCodePFormula C) i ∧
      R = !value.dfn (!forcingCodeRFormula C) i ∧
      !lowRankNameSetValueFormula D P η ∧ !boundedFunctionFormula b n D ∧ p ∈ P ∧
      !sigmaOneInternalForcingFormula P R D n φ b p”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance lowRankNameSetValueFormula_defined :
    ℒₛₑₜ-function₂[V] lowRankNameSet via lowRankNameSetValueFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [lowRankNameSetValueFormula, mem_lowRankNameSet]⟩

private theorem forall3_eq_local {W : Type*} (a b c : W) (F : W → W → W → Prop) :
    (∀ x y z, x = a → y = b → z = c → F x y z) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h x y z hx hy hz ↦ by subst x y z; exact h⟩
private theorem forall7_eq_local {W : Type*} (a b c d e f g : W)
    (F : W → W → W → W → W → W → W → Prop) :
    (∀ s t u v w x y, s = a → t = b → u = c → v = d → w = e → x = f → y = g → F s t u v w x y) ↔
      F a b c d e f g :=
  ⟨fun h ↦ h a b c d e f g rfl rfl rfl rfl rfl rfl rfl,
    fun h s t u v w x y hs ht hu hv hw hx hy ↦ by subst s t u v w x y; exact h⟩
theorem eval_localSparsePrefixForcingFormula (stage : SetTheorySemisentence 2)
    [ℒₛₑₜ-function₁[V] woodinSparseStageCode via stage] {n φ b p : V}
    (hφ : IsMembershipFormulaCode n φ) :
    (localSparsePrefixForcingFormula stage).Evalb ![n, φ, b, p] ↔
      WoodinSparseLocalPrefixForces n φ b p := by
  simp [localSparsePrefixForcingFormula, WoodinSparseLocalPrefixForces, Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ, forall3_eq_local, forall7_eq_local]

  apply exists_congr
  intro i
  apply and_congr_right
  intro hi
  apply exists_congr
  intro η
  apply and_congr_right
  intro hη
  apply and_congr_right
  intro h0
  apply and_congr_right
  intro hb
  apply and_congr_right
  intro hp
  exact eval_sigmaOneInternalForcingFormula hφ hb hp

end ZFVP

