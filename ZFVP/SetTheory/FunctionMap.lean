import ZFVP.SetTheory.FunctionUnion
import ZFVP.SetTheory.FiniteSequences

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def functionMap (F : V → V) (hF : ℒₛₑₜ-function₁ F) (s : V) : V :=
  definableGraph (domain s) (fun i ↦ F (s ‘ i)) (by definability)

instance functionMap_definable (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    ℒₛₑₜ-function₁[V] (functionMap F hF) := by
  have h : ℒₛₑₜ-relation[V] (fun t s ↦ ∀ z, z ∈ t ↔
      ∃ i ∈ domain s, z = ⟨i, F (s ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = functionMap F hF (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [functionMap, mem_definableGraph_iff]

instance functionMap_isFunction (F : V → V) (hF : ℒₛₑₜ-function₁ F) (s : V) :
    IsFunction (functionMap F hF s) := by unfold functionMap; infer_instance

theorem functionMap_domain (F : V → V) (hF : ℒₛₑₜ-function₁ F) (s : V) :
    domain (functionMap F hF s) = domain s := domain_definableGraph _ _ _

theorem functionMap_value (F : V → V) (hF : ℒₛₑₜ-function₁ F) {s i : V}
    (hi : i ∈ domain s) : (functionMap F hF s) ‘ i = F (s ‘ i) :=
  value_definableGraph _ _ _ hi

theorem functionMap_mem_function (F : V → V) (hF : ℒₛₑₜ-function₁ F) {s A B C : V}
    (hs : s ∈ B ^ A) (hmap : ∀ x ∈ B, F x ∈ C) : functionMap F hF s ∈ C ^ A := by
  rw [← domain_eq_of_mem_function hs]
  exact definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦
    hmap _ (function_value_mem hs ((domain_eq_of_mem_function hs) ▸ hi)))

theorem functionMap_restrict (F : V → V) (hF : ℒₛₑₜ-function₁ F) {s A : V}
    [IsFunction s] (hA : A ⊆ domain s) :
    functionMap F hF (s ↾ A) = (functionMap F hF s) ↾ A := by
  have hsr := function_restrict_mem (IsFunction.mem_function s) hA
  have hd : domain (s ↾ A) = A := domain_eq_of_mem_function hsr
  have hAm : A ⊆ domain (functionMap F hF s) := by rwa [functionMap_domain]
  have hmr := function_restrict_mem (IsFunction.mem_function (functionMap F hF s)) hAm
  have := IsFunction.of_mem hmr
  apply functions_eq_of_domain_values
  · rw [functionMap_domain, hd, domain_eq_of_mem_function hmr]
  · intro i hi
    rw [functionMap_domain, hd] at hi
    rw [functionMap_value F hF (hd.symm ▸ hi), value_restrict (hA i hi) hi,
      value_restrict (hAm i hi) hi, functionMap_value F hF (hA i hi)]

end ZFVP
