import ZFVP.ModelTheory.ForcingRealization
import ZFVP.SetTheory.DeltaOneCheckNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingRealization
variable {A : ForcingContext V} (L : ForcingRealization A W)

theorem nameValue_eq_iff (σ τ : V) :
    nameValue L.genericSet (L.ground σ) = nameValue L.genericSet (L.ground τ) ↔
      GenericMeets A.G (atomicEquality A.P A.R σ τ) := by
  let N := transitiveClosure ({σ, τ} : V)
  have hN : IsSubnameClosed N := transitive_subnameClosed (transitiveClosure_transitive _)
  have hσ : σ ∈ N := subset_transitiveClosure _ _ (by simp)
  have hτ : τ ∈ N := subset_transitiveClosure _ _ (by simp)
  have he := local_atomicEquality_iff (L.ground.map_forcingPreorder A.order)
    (L.ground.map_subnameClosed hN) L.filter (L.membership_witnesses N) (L.equality_decisions N)
    ((L.ground.mem_iff σ N).mpr hσ) ((L.ground.mem_iff τ N).mpr hτ)
  rw [← L.ground.map_atomicEquality] at he
  exact he.trans (L.meets_iff _)

theorem nameValue_mem_iff (σ τ : V) :
    nameValue L.genericSet (L.ground σ) ∈ nameValue L.genericSet (L.ground τ) ↔
      GenericMeets A.G (atomicMembership A.P A.R σ τ) := by
  let N := transitiveClosure ({σ, τ} : V)
  have hN : IsSubnameClosed N := transitive_subnameClosed (transitiveClosure_transitive _)
  have hσ : σ ∈ N := subset_transitiveClosure _ _ (by simp)
  have hτ : τ ∈ N := subset_transitiveClosure _ _ (by simp)
  have he := local_atomicMembership_iff (L.ground.map_forcingPreorder A.order)
    (L.ground.map_subnameClosed hN) L.filter (L.membership_witnesses N) (L.equality_decisions N)
    ((L.ground.mem_iff σ N).mpr hσ) ((L.ground.mem_iff τ N).mpr hτ)
  rw [← L.ground.map_atomicMembership] at he
  exact he.trans (L.meets_iff _)

noncomputable def value : A.Model → W :=
  Quotient.lift (fun τ : ForcingName A.P ↦ nameValue L.genericSet (L.ground τ.val))
    (fun σ τ he ↦ (L.nameValue_eq_iff σ.val τ.val).mpr he)

theorem value_ofName (τ : ForcingName A.P) :
    L.value (A.ofName τ) = nameValue L.genericSet (L.ground τ.val) := rfl

theorem value_injective : Function.Injective L.value := by
  intro x y he
  obtain ⟨σ, rfl⟩ := A.ofName_surjective x
  obtain ⟨τ, rfl⟩ := A.ofName_surjective y
  exact (forcingQuotientMk_eq_iff A.P A.R A.G A.order A.generic.1 σ τ).mpr
    ((L.nameValue_eq_iff σ.val τ.val).mp he)

theorem value_mem_iff (x y : A.Model) : L.value x ∈ L.value y ↔ x ∈ y := by
  obtain ⟨σ, rfl⟩ := A.ofName_surjective x
  obtain ⟨τ, rfl⟩ := A.ofName_surjective y
  exact L.nameValue_mem_iff σ.val τ.val

theorem value_endExtension (x : A.Model) {y : W} (hy : y ∈ L.value x) :
    ∃ z ∈ x, y = L.value z := by
  obtain ⟨τ, rfl⟩ := A.ofName_surjective x
  obtain ⟨ν, s, hs, hνs, he⟩ := (mem_nameValue_iff _ _ _).mp hy
  obtain ⟨σ, p, hσp, hν, hsp⟩ := (L.ground.pair_mem_image_iff τ.val ν s).mp hνs
  let ρ : ForcingName A.P := ⟨σ, forcingName_subname τ.property hσp⟩
  have heval : y = L.value (A.ofName ρ) := by
    rw [L.value_ofName]
    exact he.trans (congrArg (nameValue L.genericSet) hν)
  refine ⟨A.ofName ρ, ?_, heval⟩
  apply (L.value_mem_iff _ _).mp
  rw [← heval]
  exact hy

noncomputable def embedding : MembershipEndExtension A.Model W where
  toFun := L.value
  injective := L.value_injective
  mem_iff := L.value_mem_iff
  endExtension := fun x _y hy ↦ L.value_endExtension x hy

theorem value_check (x : V) : L.value (A.check x) = L.ground x := by
  have he := (eval_sigmaOneCheckNameFormula true A.one x (checkName A.one x)).mpr rfl
  have hu := L.ground.sigma_one_upward (sigmaOneCheckNameFormula_sigmaOne true)
    ![A.one, x, checkName A.one x] he
  have hv : (fun i : Fin 3 ↦ L.ground (![A.one, x, checkName A.one x] i)) =
      ![L.ground A.one, L.ground x, L.ground (checkName A.one x)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun z ↦ Fin.elim0 z) k) j) i
  rw [hv] at hu
  have hcheck : L.ground (checkName A.one x) = checkName (L.ground A.one) (L.ground x) :=
    (eval_sigmaOneCheckNameFormula true _ _ _).mp hu
  change nameValue L.genericSet (L.ground (checkName A.one x)) = L.ground x
  rw [hcheck]
  exact nameValue_checkName ((L.generic_mem A.one).mpr (externalForcingFilter_top A.generic.1 A.top)) _

end ForcingRealization
end ZFVP
