import ZFVP.SetTheory.HereditarySymmetry

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def tupleNameStabilizer (Γ : V) : {n : ℕ} → (Fin n → V) → V
  | 0, _ => Γ
  | _ + 1, v => nameStabilizer Γ (v 0) ∩ tupleNameStabilizer Γ (fun i ↦ v i.succ)

theorem mem_tupleNameStabilizer_iff (Γ π : V) {n : ℕ} (v : Fin n → V) :
    π ∈ tupleNameStabilizer Γ v ↔ π ∈ Γ ∧ ∀ i, nameAction π (v i) = v i := by
  induction n with
  | zero => simp [tupleNameStabilizer]
  | succ n ih =>
    rw [tupleNameStabilizer, mem_inter_iff, ih]
    constructor
    · rintro ⟨h0, hΓ, ht⟩
      exact ⟨hΓ, fun i ↦ Fin.cases (mem_sep_iff.mp h0).2 (fun j ↦ ht j) i⟩
    · rintro ⟨hΓ, hh⟩
      exact ⟨mem_sep_iff.mpr ⟨hΓ, hh 0⟩, hΓ, fun i ↦ hh i.succ⟩

theorem tupleNameStabilizer_mem_filter {P Γ F : V} (hF : IsNormalSubgroupFilter P Γ F)
    {n : ℕ} (v : Fin n → V) (hv : ∀ i, IsHereditarilySymmetricName P Γ F (v i)) :
    tupleNameStabilizer Γ v ∈ F := by
  induction n with
  | zero => exact hF.2.1
  | succ n ih =>
    exact hF.2.2.2.1 _ (hereditarilySymmetric_symmetric (hv 0)).2 _
      (ih (fun i ↦ v i.succ) (fun i ↦ hv i.succ))

end ZFVP
