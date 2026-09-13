import ZFVP.ModelTheory.SemanticStandardCodedZFModel
import ZFVP.ModelTheory.SchmerlUniverseGraphs

/-! An external elementary map between represented structures has an actual
internal graph preserving every internal formula code in Universe. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

namespace BinaryRelationRepresentation

variable {M N : Type*} [SetStructure M] [SetStructure N]
    (R : BinaryRelationRepresentation (V := Universe.{u}) M)
    (S : BinaryRelationRepresentation (V := Universe.{u}) N)

noncomputable def mapGraph (f : M → N) : Universe.{u} :=
  Schmerl.universeGraph R.carrier (fun x ↦
    (S.equiv (f (R.equiv.symm (⟨x.val, x.property⟩ : BinaryRelationDomain R.carrier R.relation)))).val)

theorem mapGraph_function (f : M → N) : R.mapGraph S f ∈ S.carrier ^ R.carrier :=
  Schmerl.universeGraph_mem_function _ (fun _ ↦ (S.equiv _).property)

theorem mapGraph_value (f : M → N) (x : M) :
    (R.mapGraph S f) ‘ (R.equiv x).val = (S.equiv (f x)).val := by
  have he := Schmerl.value_universeGraph R.carrier (fun y ↦
    (S.equiv (f (R.equiv.symm (⟨y.val, y.property⟩ : BinaryRelationDomain R.carrier R.relation)))).val)
      ⟨(R.equiv x).val, (R.equiv x).property⟩
  change (R.mapGraph S f) ‘ (R.equiv x).val =
    (S.equiv (f (R.equiv.symm (R.equiv x)))).val at he
  simpa only [Equiv.symm_apply_apply] using he

theorem mapGraph_compose_tuple (f : M → N) {k : ℕ} (b : Fin k → M) :
    compose (standardTuple (fun i ↦ (R.equiv (b i)).val)) (R.mapGraph S f) =
      standardTuple (fun i ↦ (S.equiv (f (b i))).val) := by
  let := IsFunction.of_mem (R.mapGraph_function S f)
  rw [compose_standardTuple _ _ (fun i ↦ by
    rw [domain_eq_of_mem_function (R.mapGraph_function S f)]
    exact (R.equiv (b i)).property)]
  congr 1
  funext i
  exact R.mapGraph_value S f (b i)

theorem mapGraph_codedElementary (j : ElementaryMap M N) :
    IsCodedElementaryEmbedding membershipLanguageCode R.code S.code (R.mapGraph S j) := by
  refine ⟨R.code_valid, S.code_valid, ?_, ?_⟩
  · simpa only [code, binaryRelationStructureCode_domain] using R.mapGraph_function S j
  · intro n hn φ hφ b hb
    obtain ⟨k, rfl⟩ := Schmerl.universe_standardOmega n hn
    obtain ⟨ψ, hψ⟩ := universe_semanticStandardMembershipSyntax.formulas k φ
      ((mem_formulaSet_iff _ _ _ _).mp hφ)
    obtain ⟨v, rfl⟩ := R.exists_standard_assignment hb
    rw [R.mapGraph_compose_tuple S j v]
    have hf : j ∘ (Empty.elim : Empty → M) = Empty.elim := funext (fun x ↦ Empty.elim x)
    have hj : ψ.Evalb v ↔ ψ.Evalb (j ∘ v) := by
      simpa only [Semiformula.Evalb, hf] using j.elementary ψ v Empty.elim
    exact (R.satisfies_represented_iff hψ v).trans
      (hj.trans (S.satisfies_represented_iff hψ (j ∘ v)).symm)

end BinaryRelationRepresentation

end ZFVP
