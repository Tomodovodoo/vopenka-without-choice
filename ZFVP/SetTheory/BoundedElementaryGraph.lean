import ZFVP.ModelTheory.EmbeddingBoundedOperations
import ZFVP.SetTheory.FunctionMap

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure IsBoundedElementaryGraph (j : V) : Prop where
  function : IsFunction j
  transitive : IsTransitive (domain j)
  elementary : ∀ {n : ℕ} {φ : SetTheorySemisentence n}, IsBoundedSetFormula φ →
    ∀ v : Fin n → V, (∀ i, v i ∈ domain j) →
      (φ.Evalb v ↔ φ.Evalb (fun i ↦ j ‘ (v i)))

namespace IsBoundedElementaryGraph

variable {j : V} (h : IsBoundedElementaryGraph j)

include h

theorem defined_iff {n : ℕ} {φ : SetTheorySemisentence n} (hφ : IsBoundedSetFormula φ)
    (R : (Fin n → V) → Prop) [Defined R φ] (v : Fin n → V) (hv : ∀ i, v i ∈ domain j) :
    R v ↔ R (fun i ↦ j ‘ (v i)) :=
  (Defined.eval_iff v).symm.trans ((h.elementary hφ v hv).trans (Defined.eval_iff _))

theorem mem_iff {x y : V} (hx : x ∈ domain j) (hy : y ∈ domain j) :
    x ∈ y ↔ j ‘ x ∈ j ‘ y := by
  have he := h.elementary (IsBoundedSetFormula.rel Language.Set.Rel.mem ![.bvar 0, .bvar 1])
    ![x, y] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hx, hy])
  simpa [Semiformula.Evalb, Structure.rel] using he

theorem function_iff {s X α : V} (hs : s ∈ domain j) (hX : X ∈ domain j) (hα : α ∈ domain j) :
    s ∈ X ^ α ↔ j ‘ s ∈ (j ‘ X) ^ (j ‘ α) :=
  h.defined_iff boundedFunctionFormula_bounded (fun v ↦ v 0 ∈ v 2 ^ v 1)
    ![s, α, X] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hs, hα, hX])

theorem pair_mem_iff {R s x : V} (hR : R ∈ domain j) (hs : s ∈ domain j) (hx : x ∈ domain j) :
    ⟨s, x⟩ₖ ∈ R ↔ ⟨j ‘ s, j ‘ x⟩ₖ ∈ j ‘ R :=
  h.defined_iff boundedPairMemberFormula_bounded (fun v ↦ ⟨v 1, v 2⟩ₖ ∈ v 0)
    ![R, s, x] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hR, hs, hx])

theorem value_apply {s X α i : V} (hs : s ∈ domain j) (hX : X ∈ domain j)
    (hα : α ∈ domain j) (hf : s ∈ X ^ α) (hi : i ∈ α) :
    j ‘ (s ‘ i) = (j ‘ s) ‘ (j ‘ i) := by
  let := h.function
  let := IsFunction.of_mem hf
  have him : j ‘ s ∈ (j ‘ X) ^ (j ‘ α) := (h.function_iff hs hX hα).mp hf
  let := IsFunction.of_mem him
  have hid := h.transitive.mem_trans hi hα
  have hvid := h.transitive.mem_trans (function_value_mem hf hi) hX
  exact (value_eq_of_kpair_mem ((h.pair_mem_iff hs hid hvid).mp
    (kpair_value_mem ((domain_eq_of_mem_function hf).symm ▸ hi)))).symm

theorem functionMap_eq_value {s X α : V} (hs : s ∈ domain j) (hX : X ∈ domain j)
    (hα : α ∈ domain j) (hf : s ∈ X ^ α) (hfixα : j ‘ α = α)
    (hfix : ∀ i ∈ α, j ‘ i = i) :
    functionMap (fun x ↦ j ‘ x) (by definability) s = j ‘ s := by
  let := IsFunction.of_mem hf
  have hjf := (h.function_iff hs hX hα).mp hf
  rw [hfixα] at hjf
  let := IsFunction.of_mem hjf
  apply functions_eq_of_domain_values
  · rw [functionMap_domain, domain_eq_of_mem_function hf, domain_eq_of_mem_function hjf]
  · intro i hi
    rw [functionMap_domain, domain_eq_of_mem_function hf] at hi
    rw [functionMap_value _ _ ((domain_eq_of_mem_function hf).symm ▸ hi),
      h.value_apply hs hX hα hf hi, hfix i hi]

end IsBoundedElementaryGraph
end ZFVP
