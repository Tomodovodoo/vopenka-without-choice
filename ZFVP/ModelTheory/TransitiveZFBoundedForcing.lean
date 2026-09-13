import ZFVP.ModelTheory.TransitiveZFForcingOrders
import ZFVP.ModelTheory.TransitiveZFNames
import ZFVP.SetTheory.DeltaOneBoundedForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem bounded_forcing_iff (P R p : SetDomain U) (hR : IsForcingPreorder P R)
    {n : ℕ} {φ : SetTheorySemisentence n} (hφ : IsBoundedSetFormula φ)
    (v : Fin n → SetDomain U) (hv : ∀ i, IsForcingName P (v i)) :
    p ∈ forcingFormula P R φ (standardTuple v) ↔
      p.val ∈ forcingFormula P.val R.val φ (standardTuple (fun i ↦ (v i).val)) := by
  obtain ⟨t, rfl⟩ := boundedFormulaTree_exists hφ
  have hR' := (forcingPreorder_iff U P R).mp hR
  have hv' : ∀ i, IsForcingName P.val (v i).val := fun i ↦ (forcingName_iff U P (v i)).mp (hv i)
  have hm : (fun i ↦ ((P :> R :> p :> v) i).val) =
      P.val :> R.val :> p.val :> (fun i ↦ (v i).val) := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun _ ↦ rfl) k) j) i
  constructor
  · intro hp
    have ht := (t.forcingCertificate_ordinary_meaning hR v hv true p).mpr hp
    have hu := sigma_one_upward U (t.forcingCertificate_sigmaOne true) (P :> R :> p :> v) ht
    rw [hm] at hu
    exact (t.forcingCertificate_ordinary_meaning hR' (fun i ↦ (v i).val) hv' true p.val).mp hu
  · intro hp
    have ht := (t.forcingPi_ordinary_meaning hR' (fun i ↦ (v i).val) hv' p.val).mpr hp
    rw [← hm] at ht
    exact (t.forcingPi_ordinary_meaning hR v hv p).mp
      (pi_one_downward U t.forcingPi_piOne (P :> R :> p :> v) ht)

theorem bounded_forcing_val (P R : SetDomain U) (hR : IsForcingPreorder P R)
    {n : ℕ} {φ : SetTheorySemisentence n} (hφ : IsBoundedSetFormula φ)
    (v : Fin n → SetDomain U) (hv : ∀ i, IsForcingName P (v i)) :
    (forcingFormula P R φ (standardTuple v)).val =
      forcingFormula P.val R.val φ (standardTuple (fun i ↦ (v i).val)) := by
  apply mem_ext
  intro p
  constructor
  · intro hp
    let p' : SetDomain U := ⟨p, (inferInstance : IsTransitive U).mem_trans hp
      (forcingFormula P R φ (standardTuple v)).property⟩
    exact (bounded_forcing_iff U P R p' hR hφ v hv).mp hp
  · intro hp
    have hpP := (forcingFormula_regular ((forcingPreorder_iff U P R).mp hR) φ (standardTuple (fun i ↦ (v i).val))).1 p hp
    let p' : SetDomain U := ⟨p, (inferInstance : IsTransitive U).mem_trans hpP P.property⟩
    exact (bounded_forcing_iff U P R p' hR hφ v hv).mpr hp

end TransitiveZF
end ZFVP
