import ZFVP.ModelTheory.SymmetricModelSeparation

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricContext

theorem boundedRepresentative (S : SymmetricContext V) (τ : S.Name) (x : S.Model)
    (hx : ∀ z, z ∈ x → z ∈ S.ofName τ) :
    ∃ ρ : S.Name, ρ.val ⊆ domain τ.val ×ˢ S.P ∧ S.ofName ρ = x := by
  obtain ⟨σ, rfl⟩ := S.ofName_surjective x
  let φ : SetTheorySemisentence 2 := .rel .mem ![.bvar 0, .bvar 1]
  refine ⟨S.separationName τ φ ![σ], ?_, ?_⟩
  · dsimp only [separationName]
    exact forcingSelectedName_subset S.P S.R τ.val _ _
  apply S.extensionality
  intro z
  rw [S.mem_separationName_iff]
  have he : φ.Evalb (z :> fun i ↦ S.ofName (![σ] i)) ↔ z ∈ S.ofName σ := by
    simp [φ, Semiformula.Evalb, Structure.rel]
  rw [he]
  exact ⟨And.right, fun hz ↦ ⟨hx z hz, hz⟩⟩

end SymmetricContext
end ZFVP
