import ZFVP.ModelTheory.ElementaryStageSatisfaction
import ZFVP.ModelTheory.FiniteParameterElementarity
import ZFVP.Syntax.EndExtensionFoundationEncoding

/-! A full pullback satisfaction class gives an actual elementary map into its rank stage. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_encodeMembershipFormula (j : MembershipEndExtension V W) {n : ℕ}
    (φ : SetTheorySemisentence n) :
    j (encodeMembershipFormula φ) = encodeMembershipFormula φ := by
  unfold encodeMembershipFormula
  rw [j.map_encodeSemiformula]
  congr 1
  · funext k f
    exact f.elim
  · funext k r
    cases r <;> exact j.map_numeral _
  · funext x
    exact x.elim

def stageMap (j : MembershipEndExtension V W) (δ : W)
    (hsub : ∀ x : V, j x ∈ hierarchy δ) : V → SetDomain (hierarchy δ) :=
  fun x ↦ ⟨j x, hsub x⟩

theorem stageMap_evalb (j : MembershipEndExtension V W) (δ : W)
    (hsub : ∀ x : V, j x ∈ hierarchy δ)
    (hS : IsFullSatisfactionClass V (stageSatisfaction j δ))
    {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → V) :
    φ.Evalb b ↔ φ.Evalb (stageMap j δ hsub ∘ b) := by
  have hA : IsNonempty (hierarchy δ) := ⟨j (Classical.choice ‹Nonempty V›), hsub _⟩
  have h := hS.evalb_iff φ b
  unfold stageSatisfaction at h
  rw [j.map_numeral, j.map_encodeMembershipFormula, j.map_standardTuple] at h
  exact h.symm.trans (membershipSatisfies_encode hA φ (stageMap j δ hsub ∘ b))

def elementaryStageMap (j : MembershipEndExtension V W) (δ : W)
    (hsub : ∀ x : V, j x ∈ hierarchy δ)
    (hS : IsFullSatisfactionClass V (stageSatisfaction j δ)) :
    ElementaryMap V (SetDomain (hierarchy δ)) where
  toFun := stageMap j δ hsub
  elementary φ b f := elementary_of_semisentences _ (stageMap_evalb j δ hsub hS) φ b f

end MembershipEndExtension
end ZFVP
