import ZFVP.ModelTheory.StructureCode

/-! Every coded language has structures on every nonempty internal domain.
The construction uses one supplied element, not a choice function on symbols. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def constantGraph (A a : V) : V :=
  definableGraph A (fun _ ↦ a) (by definability)

def constantGraphFormula : SetTheorySemisentence 3 :=
  f“f A a. ∀ p, p ∈ f ↔ ∃ x ∈ A, p = !kpair.dfn x a”

instance constantGraphFormula_defined :
    ℒₛₑₜ-function₂[V] constantGraph via constantGraphFormula := ⟨fun v ↦ by
  change constantGraphFormula.Evalb v ↔ v 0 = constantGraph (v 1) (v 2)
  rw [mem_ext_iff]
  simp [constantGraphFormula, constantGraph, mem_definableGraph_iff]⟩

instance constantGraph_definable : ℒₛₑₜ-function₂[V] constantGraph :=
  constantGraphFormula_defined.to_definable

instance constantGraph_isFunction (A a : V) : IsFunction (constantGraph A a) :=
  definableGraph_isFunction A (fun _ ↦ a) _

theorem domain_constantGraph (A a : V) : domain (constantGraph A a) = A :=
  domain_definableGraph A (fun _ ↦ a) _

theorem value_constantGraph (A a : V) {x : V} (hx : x ∈ A) :
    (constantGraph A a) ‘ x = a := value_definableGraph A (fun _ ↦ a) _ hx

theorem constantGraph_mem_function (A B a : V) (ha : a ∈ B) :
    constantGraph A a ∈ B ^ A :=
  definableGraph_mem_function_of_mapsTo A B (fun _ ↦ a) _ (fun _ _ ↦ ha)

theorem structureCode_exists_on_domain (L A : V) (hL : IsLanguageCode L)
    (hA : IsNonempty A) : ∃ M : V, IsStructureCode L M ∧ structureDomain M = A := by
  obtain ⟨a, ha⟩ := hA.nonempty
  let F : V → V := fun f ↦ constantGraph (A ^ ((functionArities L) ‘ f)) a
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let FI := definableGraph (functionSymbols L) F hF
  let RI := constantGraph (relationSymbols L) ∅
  refine ⟨structureCode A FI RI, ?_, structureDomain_code A FI RI⟩
  simp only [IsStructureCode, structureDomain_code, structureFunctions_code, structureRelations_code]
  refine ⟨hL, True.intro, ⟨a, ha⟩, inferInstance, domain_definableGraph _ _ _,
    inferInstance, domain_constantGraph _ _, ?_, ?_⟩
  · intro f hf
    change (definableGraph (functionSymbols L) F hF) ‘ f ∈ A ^ (A ^ ((functionArities L) ‘ f))
    rw [value_definableGraph _ _ _ hf]
    exact constantGraph_mem_function _ A a ha
  · intro r hr
    change (constantGraph (relationSymbols L) ∅) ‘ r ⊆ A ^ ((relationArities L) ‘ r)
    rw [value_constantGraph _ _ hr]
    exact empty_subset _

end ZFVP
