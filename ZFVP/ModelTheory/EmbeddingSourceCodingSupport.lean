import ZFVP.ModelTheory.EmbeddingBoundedOperations
import ZFVP.SetTheory.BoundedSequenceSupport

/-! Transitive sources of elementary embeddings inherit bounded operation
closure from their targets. Omega membership is supplied separately. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCodedMembershipEmbedding
variable {A B f : V} [IsTransitive A]

theorem bounded_witness (h : IsCodedMembershipEmbedding A B f) [IsTransitive B]
    {n : ℕ} {φ : SetTheorySemisentence (n + 1)}
    (hφ : IsBoundedSetFormula φ) (v : Fin n → V) (hv : ∀ i, v i ∈ A)
    (hex : ∃ y ∈ B, φ.Evalb (Matrix.vecCons y (fun i ↦ f ‘ (v i)))) :
    ∃ y ∈ A, φ.Evalb (Matrix.vecCons y v) := by
  let b : Fin n → SetDomain A := fun i ↦ ⟨v i, hv i⟩
  have hs : (φ.exs).Evalb (h.toFunction ∘ b) := by
    obtain ⟨y, hy, hpy⟩ := hex
    change ∃ y : SetDomain B, φ.Evalb (Matrix.vecCons y _)
    refine ⟨⟨y, hy⟩, ?_⟩
    apply (bounded_formula_absolute B hφ _).mpr
    convert hpy using 1
    congr 1
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  have hsA := (h.eval_semisentence φ.exs b).mpr hs
  change ∃ y : SetDomain A, φ.Evalb (Matrix.vecCons y b) at hsA
  obtain ⟨y, hy⟩ := hsA
  refine ⟨y.val, y.property, ?_⟩
  have ht := (bounded_formula_absolute A hφ _).mp hy
  convert ht using 1
  congr 1
  funext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

theorem source_isCodingSupport (h : IsCodedMembershipEmbedding A B f)
    [IsCodingSupport B] (hω : (ω : V) ∈ A) : IsCodingSupport A where
  toIsTransitive := inferInstance
  omega_mem := hω
  kpair_closed := by
    intro x hx y hy
    obtain ⟨z, hz, he⟩ := h.bounded_witness boundedKpairFormula_bounded
      ![x, y] (by simp [hx, hy])
      ⟨⟨f ‘ x, f ‘ y⟩ₖ, IsCodingSupport.kpair_closed _
        (function_value_mem h.function hx) _ (function_value_mem h.function hy), by simp⟩
    have heq : z = ⟨x, y⟩ₖ := by simpa using he
    exact heq ▸ hz
  doubleton_closed := by
    intro x hx y hy
    obtain ⟨z, hz, he⟩ := h.bounded_witness boundedDoubletonFormula_bounded
      ![x, y] (by simp [hx, hy])
      ⟨doubleton (f ‘ x) (f ‘ y), IsCodingSupport.doubleton_closed _
        (function_value_mem h.function hx) _ (function_value_mem h.function hy), by simp⟩
    have heq : z = doubleton x y := by simpa using he
    exact heq ▸ hz
  succ_closed := by
    intro x hx
    obtain ⟨z, hz, he⟩ := h.bounded_witness boundedSuccFormula_bounded
      ![x] (by simpa using hx)
      ⟨succ (f ‘ x), IsCodingSupport.succ_closed _ (function_value_mem h.function hx), by simp⟩
    have heq : z = succ x := by simpa using he
    exact heq ▸ hz

theorem source_isSequenceSupport (h : IsCodedMembershipEmbedding A B f)
    [IsSequenceSupport B] (hω : (ω : V) ∈ A) : IsSequenceSupport A where
  toIsCodingSupport := h.source_isCodingSupport hω
  union_closed := by
    intro x hx y hy
    obtain ⟨z, hz, he⟩ := h.bounded_witness boundedUnionFormula_bounded
      ![x, y] (by simp [hx, hy])
      ⟨f ‘ x ∪ f ‘ y, IsSequenceSupport.union_closed _
        (function_value_mem h.function hx) _ (function_value_mem h.function hy), by simp⟩
    have heq : z = x ∪ y := by simpa using he
    exact heq ▸ hz

end IsCodedMembershipEmbedding
end ZFVP
