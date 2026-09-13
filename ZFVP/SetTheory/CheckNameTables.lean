import ZFVP.SetTheory.CheckNames
import ZFVP.SetTheory.BoundedNameAction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCheckNameTable (one C T f : V) : Prop :=
  f ∈ T ^ C ∧ ∀ u ∈ C, ∀ z, z ∈ f ‘ u ↔ ∃ s ∈ u, z = ⟨f ‘ s, one⟩ₖ

theorem IsCheckNameTable.correct {one C T f : V} [hC : IsTransitive C] (h : IsCheckNameTable one C T f) :
    ∀ u ∈ C, f ‘ u = checkName one u := by
  apply projectedRank_induction C (fun x : V ↦ x) (by definability)
    (fun u ↦ f ‘ u = checkName one u) (by definability)
  intro u hu ih
  apply mem_ext
  intro z
  rw [h.2 u hu z, mem_checkName_iff]
  apply exists_congr
  intro s
  apply and_congr_right
  intro hs
  rw [ih s (hC.mem_trans hs hu) (rank_mem hs)]

theorem checkNameTable_exists (one C : V) [hC : IsTransitive C] : ∃ T f, IsCheckNameTable one C T f := by
  let hf : ℒₛₑₜ-function₁[V] (checkName one) := by definability
  refine ⟨repl (checkName one) hf C, definableGraph C (checkName one) hf,
    definableGraph_mem_function C (checkName one) hf, ?_⟩
  intro u hu z
  rw [value_definableGraph _ _ _ hu, mem_checkName_iff]
  apply exists_congr
  intro s
  apply and_congr_right
  intro hs
  rw [value_definableGraph _ _ _ (hC.mem_trans hs hu)]

end ZFVP
