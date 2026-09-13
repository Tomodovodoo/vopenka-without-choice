import ZFVP.ModelTheory.ClassForcingTowerNameEvaluation
import ZFVP.SetTheory.Collection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

theorem classImageWitnessBound (I S : V) (A : V → V → V → Prop)
    (hA : ℒₛₑₜ-relation₃ A) :
    ∃ B : V, ∀ σ ∈ I, ∀ p ∈ S,
      (∃ ν, T.IsName ν ∧ A σ ν p) → ∃ ν ∈ B, T.IsName ν ∧ A σ ν p := by
  let J : V := {z ∈ I ×ˢ S ; ∃ ν, T.IsName ν ∧ A (kpair.π₁ z) ν (kpair.π₂ z)}
  obtain ⟨B, hB⟩ := collection J
    (fun z ν ↦ T.IsName ν ∧ A (kpair.π₁ z) ν (kpair.π₂ z)) (by definability)
    (fun z hz ↦ (mem_sep_iff.mp hz).2)
  refine ⟨B, ?_⟩
  intro σ hσ p hp hex
  have hz : ⟨σ, p⟩ₖ ∈ J := by
    simpa only [J, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair] using ⟨⟨hσ, hp⟩, hex⟩
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hB ⟨σ, p⟩ₖ hz

noncomputable def classImageName (I F B : V) (A : V → V → V → Prop)
    (hA : ℒₛₑₜ-relation₃ A) : V :=
  {z ∈ B ×ˢ (⋃ˢ range F) ; T.IsName (kpair.π₁ z) ∧ T.Condition (kpair.π₂ z) ∧
    ∃ σ ∈ I, kpair.π₂ z ∈ F ‘ σ ∧ A σ (kpair.π₁ z) (kpair.π₂ z)}

theorem mem_classImageName (I F B : V) (A : V → V → V → Prop)
    (hA : ℒₛₑₜ-relation₃ A) (ν p : V) :
    ⟨ν, p⟩ₖ ∈ T.classImageName I F B A hA ↔
      ν ∈ B ∧ p ∈ ⋃ˢ range F ∧ T.IsName ν ∧ T.Condition p ∧
        ∃ σ ∈ I, p ∈ F ‘ σ ∧ A σ ν p := by
  simp only [classImageName, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

theorem classImageName_isName (I F B : V) (A : V → V → V → Prop)
    (hA : ℒₛₑₜ-relation₃ A) : T.IsName (T.classImageName I F B A hA) := by
  apply (T.isName_iff_local _).mpr
  intro z hz
  obtain ⟨ν, _, p, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨_, _, hν, hp, _⟩ := (T.mem_classImageName I F B A hA ν p).mp hz
  exact ⟨ν, p, hp, rfl, hν⟩

end DefinableForcingTower
end ZFVP
