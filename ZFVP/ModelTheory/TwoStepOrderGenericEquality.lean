import ZFVP.ModelTheory.SaturatedNameGenericEquality
import ZFVP.ModelTheory.TransitiveZFTwoStepForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]

theorem forcingFormula_eq_of_all_name_values {P R one : V} (hR : IsForcingPreorder P R)
    (ht : IsForcingTop P R one) {n : ℕ} (φ : SetTheorySemisentence n)
    (v w : Fin n → ForcingName P)
    (he : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
      ∀ i, A.ofName (v i) = A.ofName (w i)) :
    forcingFormula P R φ (standardTuple (fun i ↦ (v i).val)) =
      forcingFormula P R φ (standardTuple (fun i ↦ (w i).val)) := by
  apply IsForcingRegular.eq_of_all_generics hR (forcingFormula_regular hR _ _) (forcingFormula_regular hR _ _)
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  have hv : (fun i ↦ A.ofName (v i)) = (fun i ↦ A.ofName (w i)) := funext (he G hG)
  exact (A.formula_truth φ v).symm.trans
    ((congrArg (fun z ↦ φ.Evalb z) hv).to_iff.trans (A.formula_truth φ w))

theorem twoStepOrder_eq_of_all_order_values {P R one : V} (hR : IsForcingPreorder P R)
    (ht : IsForcingTop P R one) (Q S S' t : ForcingName P)
    (he : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
      A.ofName S = A.ofName S') :
    twoStepOrder P R Q.val S.val t.val = twoStepOrder P R Q.val S'.val t.val := by
  apply mem_ext
  intro z
  simp only [twoStepOrder, mem_sep_iff]
  apply and_congr_right
  intro hz
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_prod_iff.mp hz
  obtain ⟨p, _, τ, hτ, rfl, _⟩ := (mem_twoStepConditions P R Q.val t.val u).mp hu
  obtain ⟨q, _, σ, hσ, rfl, _⟩ := (mem_twoStepConditions P R Q.val t.val v).mp hv
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  apply and_congr_right
  intro _
  let x : ForcingName P := ⟨τ, forcingName_of_twoStepNames Q.property t.property hτ⟩
  let y : ForcingName P := ⟨σ, forcingName_of_twoStepNames Q.property t.property hσ⟩
  have hf := forcingFormula_eq_of_all_name_values hR ht boundedPairMemberFormula ![S, x, y] ![S', x, y]
    (fun G hG i ↦ Fin.cases (he G hG) (fun j ↦ Fin.cases rfl
      (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i)
  have hnames (Z : ForcingName P) :
      (fun i : Fin 3 ↦ ((![Z, x, y] : Fin 3 → ForcingName P) i).val) = ![Z.val, τ, σ] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
  rw [hnames, hnames] at hf
  rw [hf]

end ZFVP
