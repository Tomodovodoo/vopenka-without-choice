import ZFVP.ModelTheory.SymmetricModel
import ZFVP.SetTheory.SymmetricSelectedName
import ZFVP.SetTheory.TupleNameStabilizer

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricContext

noncomputable def separationName (S : SymmetricContext V) (τ : S.Name) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → S.Name) : S.Name :=
  ⟨forcingSelectedName S.P S.R τ.val
    (fun ν ↦ symmetricForcingFormula S.P S.R S.Γ S.F φ
      (assignmentPrepend (n : V) (standardTuple (fun i ↦ (v i).val)) ν)) (by definability), by
    apply hereditarilySymmetric_forcingSelectedName S.group S.normal τ.property
      (tupleNameStabilizer_mem_filter S.normal (τ.val :> fun i ↦ (v i).val)
        (fun i ↦ Fin.cases τ.property (fun j ↦ (v j).property) i))
    · intro π hπ
      exact ((mem_tupleNameStabilizer_iff _ _ _).mp hπ).2 0
    · intro π hπ ν hν p hp
      obtain ⟨hπΓ, hfix⟩ := (mem_tupleNameStabilizer_iff _ _ _).mp hπ
      have he : (fun i ↦ nameAction π ((ν :> fun j ↦ (v j).val) i)) =
          (nameAction π ν :> fun j ↦ (v j).val) := by
        funext i
        exact Fin.cases rfl (fun j ↦ hfix j.succ) i
      have hh := symmetricForcingFormula_nameAction_iff S.order S.group S.normal hπΓ φ
        (ν :> fun j ↦ (v j).val) (fun i ↦ Fin.cases hν (fun j ↦ (v j).property) i) hp
      rw [he] at hh
      exact hh⟩

theorem mem_selected_iff (S : SymmetricContext V) (τ : S.Name) (A : V → V) (hA : ℒₛₑₜ-function₁ A)
    (hsel : IsHereditarilySymmetricName S.P S.Γ S.F (forcingSelectedName S.P S.R τ.val A hA))
    (hd : ∀ ν, IsForcingDownwardClosed S.P S.R (A ν)) (x : S.Model) :
    x ∈ S.ofName ⟨forcingSelectedName S.P S.R τ.val A hA, hsel⟩ ↔
      ∃ ν : S.Name, ∃ s ∈ S.G, ⟨ν.val, s⟩ₖ ∈ τ.val ∧ x = S.ofName ν ∧ GenericMeets S.G (A ν.val) := by
  rw [S.mem_ofName_iff]
  constructor
  · rintro ⟨ν, q, hqG, hνq, he⟩
    obtain ⟨_, s, hs, hqs, hqA⟩ := (mem_forcingSelectedName_iff _ _ _ A hA _ _).mp hνq
    exact ⟨ν, s, S.generic.1.2.2.1 q hqG s (forcingOrder_right_mem S.order hqs) hqs,
      hs, he, q, hqG, hqA⟩
  · rintro ⟨ν, s, hsG, hs, he, p, hpG, hpA⟩
    obtain ⟨q, hqG, hqs, hqp⟩ := S.generic.1.2.2.2 s hsG p hpG
    exact ⟨ν, q, hqG, (mem_forcingSelectedName_iff _ _ _ A hA _ _).mpr
      ⟨S.generic.1.1 q hqG, s, hs, hqs, hd ν.val p hpA q (S.generic.1.1 q hqG) hqp⟩, he⟩

theorem mem_separationName_iff (S : SymmetricContext V) (τ : S.Name) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → S.Name) (x : S.Model) :
    x ∈ S.ofName (S.separationName τ φ v) ↔
      x ∈ S.ofName τ ∧ φ.Evalb (x :> fun i ↦ S.ofName (v i)) := by
  rw [separationName, S.mem_selected_iff τ _ _ _
    (fun ν ↦ (symmetricForcingFormula_regular S.order S.Γ S.F φ _).2.1)]
  have htruth (ν : S.Name) : GenericMeets S.G (symmetricForcingFormula S.P S.R S.Γ S.F φ
      (assignmentPrepend (n : V) (standardTuple (fun i ↦ (v i).val)) ν.val)) ↔
        φ.Evalb (S.ofName ν :> fun i ↦ S.ofName (v i)) := by
    have he : (fun i ↦ S.ofName ((ν :> v) i)) = (S.ofName ν :> fun i ↦ S.ofName (v i)) := by
      funext i
      exact Fin.cases rfl (fun _ ↦ rfl) i
    simpa only [he, ClassForcingQuotient.nameTuple_cons] using (S.formula_truth φ (ν :> v)).symm
  constructor
  · rintro ⟨ν, s, hsG, hs, rfl, hA⟩
    exact ⟨(S.mem_ofName_iff τ _).mpr ⟨ν, s, hsG, hs, rfl⟩, (htruth ν).mp hA⟩
  · rintro ⟨hx, hφ⟩
    obtain ⟨ν, s, hsG, hs, he⟩ := (S.mem_ofName_iff τ x).mp hx
    exact ⟨ν, s, hsG, hs, he, (htruth ν).mpr (he ▸ hφ)⟩

theorem separation (S : SymmetricContext V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → S.Model) (a : S.Model) : ∃ b : S.Model, ∀ x, x ∈ b ↔ x ∈ a ∧ φ.Evalb (x :> v) := by
  obtain ⟨τ, rfl⟩ := S.ofName_surjective a
  choose w hw using fun i ↦ S.ofName_surjective (v i)
  have he : (fun i ↦ S.ofName (w i)) = v := funext hw
  refine ⟨S.ofName (S.separationName τ φ w), ?_⟩
  simpa only [he] using S.mem_separationName_iff τ φ w

end SymmetricContext
end ZFVP
