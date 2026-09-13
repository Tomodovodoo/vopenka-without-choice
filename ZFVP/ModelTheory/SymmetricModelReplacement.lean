import ZFVP.ModelTheory.SymmetricModelImages
import ZFVP.SetTheory.TupleNameStabilizer

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricContext

theorem replacementNames (S : SymmetricContext V) (τ : S.Name) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1 + 1)) (v : Fin n → S.Name)
    (huniq : ∀ a, a ∈ S.ofName τ → ∀ b c,
      φ.Evalb (a :> b :> fun i ↦ S.ofName (v i)) →
      φ.Evalb (a :> c :> fun i ↦ S.ofName (v i)) → b = c) :
    ∃ b : S.Model, ∀ x, x ∈ b ↔ ∃ a, a ∈ S.ofName τ ∧
      φ.Evalb (a :> x :> fun i ↦ S.ofName (v i)) := by
  apply S.definableImage τ (tupleNameStabilizer S.Γ (τ.val :> fun i ↦ (v i).val))
    (tupleNameStabilizer_mem_filter S.normal _ (fun i ↦ Fin.cases τ.property (fun j ↦ (v j).property) i))
    (fun π hπ ↦ ((mem_tupleNameStabilizer_iff _ _ _).mp hπ).2 0)
    (fun σ ν ↦ symmetricForcingFormula S.P S.R S.Γ S.F φ
      (assignmentPrepend ((n + 1 : ℕ) : V)
        (assignmentPrepend (n : V) (standardTuple (fun i ↦ (v i).val)) ν) σ))
    (by definability) ?_ (fun σ ν ↦ (symmetricForcingFormula_regular S.order S.Γ S.F φ _).2.1) _ ?_ huniq
  · intro π hπ σ ν hσ hν p hp
    obtain ⟨hπΓ, hfix⟩ := (mem_tupleNameStabilizer_iff _ _ _).mp hπ
    have he : (fun i ↦ nameAction π ((σ :> ν :> fun j ↦ (v j).val) i)) =
        (nameAction π σ :> nameAction π ν :> fun j ↦ (v j).val) := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ hfix k.succ) j) i
    have hh := symmetricForcingFormula_nameAction_iff S.order S.group S.normal hπΓ φ
      (σ :> ν :> fun j ↦ (v j).val)
      (fun i ↦ Fin.cases hσ (fun j ↦ Fin.cases hν (fun k ↦ (v k).property) j) i) hp
    rw [he] at hh
    exact hh
  · intro σ ν
    simpa only [ClassForcingQuotient.nameTuple_cons, S.ofName_cons] using
      (S.formula_truth φ (σ :> ν :> v)).symm

theorem replacement (S : SymmetricContext V) {n : ℕ} (φ : SetTheorySemisentence (n + 1 + 1))
    (v : Fin n → S.Model) (a : S.Model)
    (huniq : ∀ x, x ∈ a → ∀ y z, φ.Evalb (x :> y :> v) → φ.Evalb (x :> z :> v) → y = z) :
    ∃ b : S.Model, ∀ y, y ∈ b ↔ ∃ x, x ∈ a ∧ φ.Evalb (x :> y :> v) := by
  obtain ⟨τ, rfl⟩ := S.ofName_surjective a
  choose w hw using fun i ↦ S.ofName_surjective (v i)
  have he : (fun i ↦ S.ofName (w i)) = v := funext hw
  simpa only [he] using S.replacementNames τ φ w (by simpa only [he] using huniq)

end SymmetricContext
end ZFVP
