import ZFVP.SetTheory.CnAbsoluteness
import ZFVP.SetTheory.DeltaOneCheckNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem Cn.sigmaOne_witness {δ : V} (hδ : Cn 1 δ) {n : ℕ}
    {φ : SetTheorySemisentence (n + 1)} (hφ : IsSigmaFormula 1 φ)
    (v : Fin n → V) (hv : ∀ i, v i ∈ hierarchy δ)
    (hex : ∃ x : V, φ.Evalb (x :> v)) : ∃ x ∈ hierarchy δ, φ.Evalb (x :> v) := by
  let b : Fin n → SetDomain (hierarchy δ) := fun i ↦ ⟨v i, hv i⟩
  have hi : (∃¹ φ).Evalb b := (hδ.sigma_correct (.exs hφ) b).mpr hex
  obtain ⟨x, hx⟩ := hi
  refine ⟨x.val, x.property, ?_⟩
  have he := (hδ.sigma_correct hφ (x :> b)).mp hx
  have hb : (fun i ↦ ((x :> b) i).val) = (x.val :> v) := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  rwa [hb] at he

theorem Cn.checkName_closed {δ one x : V} (hδ : Cn 1 δ)
    (hone : one ∈ hierarchy δ) (hx : x ∈ hierarchy δ) : checkName one x ∈ hierarchy δ := by
  let φ : SetTheorySemisentence 3 := (sigmaOneCheckNameFormula true).subst ![.bvar 1, .bvar 2, .bvar 0]
  have hφ : IsSigmaFormula 1 φ := (sigmaOneCheckNameFormula_sigmaOne true).subst _
  have hev (y : V) : φ.Evalb (y :> ![one, x]) ↔ y = checkName one x := by
    simp [φ, Semiformula.eval_substs, eval_sigmaOneCheckNameFormula, TruthAnswer,
      Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  obtain ⟨y, hy, he⟩ := hδ.sigmaOne_witness hφ ![one, x]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hone, hx])
    ⟨checkName one x, (hev _).mpr rfl⟩
  exact (hev y).mp he ▸ hy

end ZFVP
