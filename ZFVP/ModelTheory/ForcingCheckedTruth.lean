import ZFVP.ModelTheory.ForcingDependentChoiceTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forces_checkedUnary_of_all_generics [Countable V] {P R one a p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P)
    (φ : SetTheorySemisentence 1)
    (h : ∀ G : Set V, ∀ hG : IsExternalForcingGeneric P R G, p ∈ G →
      φ.Evalb (fun _ : Fin 1 ↦ (ForcingContext.mk P R one G hR htop hG).check a)) :
    p ∈ forcingFormula P R φ (standardTuple ![checkName one a]) := by
  let c : ForcingName P := ⟨checkName one a, checkName_isName htop.1 a⟩
  apply forcingFormula_of_all_generics hR htop hp φ ![c]
  intro G hG hpG
  have he : (fun i ↦ (ForcingContext.mk P R one G hR htop hG).ofName (![c] i)) =
      (fun _ : Fin 1 ↦ (ForcingContext.mk P R one G hR htop hG).check a) := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [he]
  exact h G hG hpG

instance ForcingContext.modelCountable [Countable V] (A : ForcingContext V) : Countable A.Model := by
  unfold ForcingContext.Model ForcingQuotient
  infer_instance

theorem all_forces_iff_all_generics [Countable V] {P R one : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → ForcingName P) :
    (∀ p ∈ P, p ∈ forcingFormula P R φ (standardTuple (fun i ↦ (v i).val))) ↔
      ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
        φ.Evalb (fun i ↦ (ForcingContext.mk P R one G hR htop hG).ofName (v i)) := by
  constructor
  · intro h G hG
    let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
    obtain ⟨p, hp⟩ := hG.1.2.1
    exact (A.formula_truth φ v).mpr ⟨p, hp, h p (hG.1.1 p hp)⟩
  · intro h p hp
    exact forcingFormula_of_all_generics hR htop hp φ v (fun G hG _ ↦ h G hG)

theorem ForcingContext.checked_unary_truth (A : ForcingContext V)
    (φ : SetTheorySemisentence 1) (a : V) :
    φ.Evalb (fun _ ↦ A.check a) ↔
      ∃ p ∈ A.G, p ∈ forcingFormula A.P A.R φ (standardTuple ![checkName A.one a]) := by
  let c : ForcingName A.P := ⟨checkName A.one a, checkName_isName A.top.1 a⟩
  have he := A.formula_truth φ ![c]
  have hv : (fun i ↦ A.ofName (![c] i)) = (fun _ : Fin 1 ↦ A.check a) := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [hv] at he
  exact he

theorem all_forces_checked_iff_all_generics [Countable V] {P R one a : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (φ : SetTheorySemisentence 1) :
    (∀ p ∈ P, p ∈ forcingFormula P R φ (standardTuple ![checkName one a])) ↔
      ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
        φ.Evalb (fun _ ↦ (ForcingContext.mk P R one G hR htop hG).check a) := by
  constructor
  · intro h G hG
    let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
    obtain ⟨p, hp⟩ := hG.1.2.1
    exact (A.checked_unary_truth φ a).mpr ⟨p, hp, h p (hG.1.1 p hp)⟩
  · intro h p hp
    exact forces_checkedUnary_of_all_generics hR htop hp φ (fun G hG _ ↦ h G hG)

end ZFVP
