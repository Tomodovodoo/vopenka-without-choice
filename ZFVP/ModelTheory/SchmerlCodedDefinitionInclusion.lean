import ZFVP.ModelTheory.SchmerlCodedInclusionLaws
import ZFVP.ModelTheory.SchmerlDirectedPosetFormulas
import ZFVP.ModelTheory.FiniteParameterElementarity

/-! Raw definitions retain their meaning under literal coded elementary
inclusions. Their internally finite parameter tuples enter a common stage. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem unaryDefinitionParameters_mono {M N d : V}
    (hMN : structureDomain M ⊆ structureDomain N) (hd : d ∈ unaryDefinitionParameters M) :
    d ∈ unaryDefinitionParameters N := by
  obtain ⟨n, hn, φ, hφ, b, hb, rfl⟩ := unaryDefinitionParameters_cases hd
  exact pair_mem_unaryDefinitionParameters.mpr ⟨hn, hφ, mem_function_of_mem_function_of_subset hb hMN⟩

theorem binaryDefinitionParameters_mono {M N d : V}
    (hMN : structureDomain M ⊆ structureDomain N) (hd : d ∈ binaryDefinitionParameters M) :
    d ∈ binaryDefinitionParameters N := by
  obtain ⟨n, hn, φ, hφ, b, hb, rfl⟩ := binaryDefinitionParameters_cases hd
  exact pair_mem_binaryDefinitionParameters.mpr ⟨hn, hφ, mem_function_of_mem_function_of_subset hb hMN⟩

theorem transportDefinition_identity_unary {M d : V} (hd : d ∈ unaryDefinitionParameters M) :
    transportDefinition d (SetTheory.identity (structureDomain M)) = d := by
  obtain ⟨n, _, φ, _, b, hb, rfl⟩ := unaryDefinitionParameters_cases hd
  simp only [transportDefinition, definitionParameterCount_pair, definitionFormula_pair,
    definitionTuple_pair, graph_compose_identity hb]

theorem transportDefinition_identity_binary {M d : V} (hd : d ∈ binaryDefinitionParameters M) :
    transportDefinition d (SetTheory.identity (structureDomain M)) = d := by
  obtain ⟨n, _, φ, _, b, hb, rfl⟩ := binaryDefinitionParameters_cases hd
  simp only [transportDefinition, definitionParameterCount_pair, definitionFormula_pair,
    definitionTuple_pair, graph_compose_identity hb]

theorem IsCodedElementaryInclusion.unaryDefinition_iff {M N d x : V}
    (h : IsCodedElementaryInclusion M N) (hd : d ∈ unaryDefinitionParameters M)
    (hx : x ∈ structureDomain M) : x ∈ unaryDefinitionSet M d ↔ x ∈ unaryDefinitionSet N d := by
  simpa only [identity_value hx, transportDefinition_identity_unary hd] using
    elementary_unaryDefinition_iff h hd hx

theorem IsCodedElementaryInclusion.binaryDefinition_iff {M N d x y : V}
    (h : IsCodedElementaryInclusion M N) (hd : d ∈ binaryDefinitionParameters M)
    (hx : x ∈ structureDomain M) (hy : y ∈ structureDomain M) :
    ⟨x, y⟩ₖ ∈ binaryDefinitionRelation M d ↔ ⟨x, y⟩ₖ ∈ binaryDefinitionRelation N d := by
  simpa only [identity_value hx, identity_value hy, transportDefinition_identity_binary hd] using
    elementary_binaryDefinition_iff h hd hx hy

theorem IsInternalRelationalChain.definitions_eventual_stage {θ C N u r : V}
    (hC : IsInternalRelationalChain membershipLanguageCode θ C)
    (hN : structureDomain N = codedChainCarrier θ C)
    (hu : u ∈ unaryDefinitionParameters N) (hr : r ∈ binaryDefinitionParameters N) :
    ∃ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      u ∈ unaryDefinitionParameters (C ‘ j) ∧ r ∈ binaryDefinitionParameters (C ‘ j) := by
  obtain ⟨n, hn, φ, hφ, b, hb, rfl⟩ := unaryDefinitionParameters_cases hu
  obtain ⟨m, hm, ψ, hψ, c, hc, rfl⟩ := binaryDefinitionParameters_cases hr
  obtain ⟨i, hi, hbi⟩ := hC.assignment_stage hn (hN ▸ hb)
  obtain ⟨j, hj, hcj⟩ := hC.assignment_stage hm (hN ▸ hc)
  obtain ⟨k, hk, hik, hjk⟩ := hC.common hi hj
  refine ⟨k, hk, ?_⟩
  intro l hl hkl
  refine ⟨pair_mem_unaryDefinitionParameters.mpr ⟨hn, hφ, ?_⟩,
    pair_mem_binaryDefinitionParameters.mpr ⟨hm, hψ, ?_⟩⟩
  · exact mem_function_of_mem_function_of_subset hbi (hC.increasing i hi l hl (subset_trans hik hkl))
  · exact mem_function_of_mem_function_of_subset hcj (hC.increasing j hj l hl (subset_trans hjk hkl))

def binaryCarrierInclusion {D E B S : V} (hDB : D ⊆ B) :
    BinaryRelationDomain D E → BinaryRelationDomain B S := fun x ↦ ⟨x.val, hDB x.val x.property⟩

theorem binaryInclusion_eval {D E B S : V}
    (he : IsCodedElementaryInclusion (binaryRelationStructureCode D E) (binaryRelationStructureCode B S))
    (hDB : D ⊆ B) {ξ : Type*} {n : ℕ} (φ : SetTheorySemiformula ξ n)
    (b : Fin n → BinaryRelationDomain D E) (a : ξ → BinaryRelationDomain D E) :
    φ.Eval b a ↔ φ.Eval (binaryCarrierInclusion (S := S) hDB ∘ b) (binaryCarrierInclusion (S := S) hDB ∘ a) := by
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using he.source.domain_nonempty
  have hB : IsNonempty B := by simpa only [binaryRelationStructureCode_domain] using he.target.domain_nonempty
  let : Nonempty (BinaryRelationDomain D E) := by
    obtain ⟨x, hx⟩ := hD
    exact ⟨⟨x, hx⟩⟩
  apply elementary_of_semisentences (binaryCarrierInclusion (S := S) hDB) ?_ φ b a
  intro k ψ v
  have hb : standardTuple (fun i ↦ (v i).val) ∈ structureDomain (binaryRelationStructureCode D E) ^ (k : V) := by
    simpa only [binaryRelationStructureCode_domain] using standardTuple_mem_function (fun i ↦ (v i).val) (fun i ↦ (v i).property)
  have hs := he.satisfies_iff (by simp) (encodeMembershipFormula_mem ψ) hb
  rw [graph_compose_identity hb] at hs
  exact (satisfies_encodeBinaryRelationFormula hD ψ v).symm.trans
    (hs.trans (satisfies_encodeBinaryRelationFormula hB ψ (binaryCarrierInclusion hDB ∘ v)))

theorem exists_unaryDefinition_uniformFormula (hω : HasStandardOmega V) {D E d : V}
    (hd : d ∈ unaryDefinitionParameters (binaryRelationStructureCode D E)) :
    ∃ δ : SetTheorySemiformula (BinaryRelationDomain D E) 1,
      ∀ B S, ∀ _hB : IsNonempty B, ∀ hDB : D ⊆ B, ∀ x : BinaryRelationDomain B S,
        δ.Eval ![x] (binaryCarrierInclusion hDB) ↔ x.val ∈ unaryDefinitionSet (binaryRelationStructureCode B S) d := by
  obtain ⟨n, hn, φ, hφ, b, hb, rfl⟩ := unaryDefinitionParameters_cases hd
  obtain ⟨n, rfl⟩ := hω n hn
  have hcode : IsMembershipFormulaCode ((n + 1 : ℕ) : V) φ := by
    simpa only [IsMembershipFormulaCode, num_succ_def] using (mem_formulaSet_iff _ _ _ _).mp hφ
  obtain ⟨ψ, hψ⟩ := binary_formula_representable_of_standardOmega hω hcode
  obtain ⟨a, rfl⟩ := exists_binaryStandardTuple (R := E)
    (by simpa only [binaryRelationStructureCode_domain] using hb)
  refine ⟨Rew.embSubsts (#0 :> fun t ↦ &(a t)) ▹ ψ, ?_⟩
  intro B S hB hDB x
  rw [Semiformula.eval_embSubsts]
  have hv : Semiterm.val (L := ℒₛₑₜ) ![x] (binaryCarrierInclusion hDB) ∘
      (#0 :> fun t ↦ &(a t)) = x :> (binaryCarrierInclusion hDB ∘ a) := by
    funext t
    refine Fin.cases ?_ (fun i ↦ ?_) t <;> simp
  rw [hv, mem_unaryDefinitionSet, binaryRelationStructureCode_domain, and_iff_right x.property]
  have ht : standardTuple (fun i ↦ ((x :> (binaryCarrierInclusion hDB ∘ a)) i).val) =
      assignmentPrepend (n : V) (standardTuple (fun i ↦ (a i).val)) x.val := by
    simp only [standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ, binaryCarrierInclusion, Function.comp_apply]
  have hh := (hψ B S hB (x :> (binaryCarrierInclusion hDB ∘ a))).symm
  rw [ht] at hh
  simpa only [codedSatisfies, definitionParameterCount_pair, definitionFormula_pair,
    definitionTuple_pair, num_succ_def] using hh

theorem exists_binaryDefinition_uniformFormula (hω : HasStandardOmega V) {D E d : V}
    (hd : d ∈ binaryDefinitionParameters (binaryRelationStructureCode D E)) :
    ∃ ρ : SetTheorySemiformula (BinaryRelationDomain D E) 2,
      ∀ B S, ∀ _hB : IsNonempty B, ∀ hDB : D ⊆ B, ∀ x y : BinaryRelationDomain B S,
        ρ.Eval ![x, y] (binaryCarrierInclusion hDB) ↔
          ⟨x.val, y.val⟩ₖ ∈ binaryDefinitionRelation (binaryRelationStructureCode B S) d := by
  obtain ⟨n, hn, φ, hφ, b, hb, rfl⟩ := binaryDefinitionParameters_cases hd
  obtain ⟨n, rfl⟩ := hω n hn
  have hcode : IsMembershipFormulaCode ((n + 2 : ℕ) : V) φ := by
    simpa only [IsMembershipFormulaCode, num_succ_def] using (mem_formulaSet_iff _ _ _ _).mp hφ
  obtain ⟨ψ, hψ⟩ := binary_formula_representable_of_standardOmega hω hcode
  obtain ⟨a, rfl⟩ := exists_binaryStandardTuple (R := E)
    (by simpa only [binaryRelationStructureCode_domain] using hb)
  refine ⟨Rew.embSubsts (#0 :> #1 :> fun t ↦ &(a t)) ▹ ψ, ?_⟩
  intro B S hB hDB x y
  rw [Semiformula.eval_embSubsts]
  have hv : Semiterm.val (L := ℒₛₑₜ) ![x, y] (binaryCarrierInclusion hDB) ∘
      (#0 :> #1 :> fun t ↦ &(a t)) = x :> y :> (binaryCarrierInclusion hDB ∘ a) := by
    funext t
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun j ↦ ?_) i) t <;> simp
  rw [hv, pair_mem_binaryDefinitionRelation, binaryRelationStructureCode_domain, and_iff_right ⟨x.property, y.property⟩]
  have ht : standardTuple (fun i ↦ ((x :> y :> (binaryCarrierInclusion hDB ∘ a)) i).val) =
      assignmentPrepend (succ (n : V)) (assignmentPrepend (n : V) (standardTuple (fun i ↦ (a i).val)) y.val) x.val := by
    simp only [standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ, binaryCarrierInclusion, Function.comp_apply, num_succ_def]
  have hh := (hψ B S hB (x :> y :> (binaryCarrierInclusion hDB ∘ a))).symm
  rw [ht] at hh
  simpa only [codedSatisfies, definitionParameterCount_pair, definitionFormula_pair,
    definitionTuple_pair, num_succ_def] using hh

end ZFVP.Schmerl
