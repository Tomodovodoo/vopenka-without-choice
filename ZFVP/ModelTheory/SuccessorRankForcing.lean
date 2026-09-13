import ZFVP.ModelTheory.SuccessorRankEmbedding
import ZFVP.SetTheory.DeltaOneForcingNames
import ZFVP.SetTheory.DeltaOneBoundedForcing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successorRankEmbedding_forcingName_iff {δ ε e P τ : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (he : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hP : P ∈ hierarchy δ) (hτ : τ ∈ hierarchy δ) :
    IsForcingName P τ ↔ IsForcingName (e ‘ P) (e ‘ τ) := by
  have h := successorRankEmbedding_pi_iff hδ hε he piOneForcingNameFormula_piOne ![P, τ]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hP, hτ])
  simpa using h

set_option maxHeartbeats 800000 in
theorem successorRankEmbedding_boundedForcing_iff {δ ε e P R p : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (he : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ) (hp : p ∈ hierarchy δ)
    (hord : IsForcingPreorder P R) (hord' : IsForcingPreorder (e ‘ P) (e ‘ R))
    {n : ℕ} {φ : SetTheorySemisentence n} (hφ : IsBoundedSetFormula φ)
    (v : Fin n → V) (hv : ∀ i, v i ∈ hierarchy δ) (hn : ∀ i, IsForcingName P (v i)) :
    p ∈ forcingFormula P R φ (standardTuple v) ↔
      e ‘ p ∈ forcingFormula (e ‘ P) (e ‘ R) φ (standardTuple (fun i ↦ e ‘ (v i))) := by
  obtain ⟨t, rfl⟩ := boundedFormulaTree_exists hφ
  have hh := successorRankEmbedding_pi_iff hδ hε he t.forcingPi_piOne (P :> R :> p :> v)
    (by intro i; exact Fin.cases hP (fun j ↦ Fin.cases hR (fun k ↦ Fin.cases hp hv k) j) i)
  have hv' : (fun i ↦ e ‘ ((P :> R :> p :> v) i)) =
      (e ‘ P :> e ‘ R :> e ‘ p :> (fun i ↦ e ‘ (v i))) := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun _ ↦ rfl) k) j) i
  rw [hv'] at hh
  exact (t.forcingPi_ordinary_meaning hord v hn p).symm.trans
    (hh.trans (t.forcingPi_ordinary_meaning hord' _
      (fun i ↦ (successorRankEmbedding_forcingName_iff hδ hε he hP (hv i)).mp (hn i)) _))

end ZFVP
