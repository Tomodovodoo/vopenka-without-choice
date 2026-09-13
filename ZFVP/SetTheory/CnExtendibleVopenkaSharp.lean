import ZFVP.SetTheory.CnExtendibleVopenka
import ZFVP.SetTheory.ChoicelessCorrectness
import ZFVP.SetTheory.ChoicelessInaccessibleRank
import ZFVP.ModelTheory.GenericRankEmbeddingZFRestriction

/-! The C(n)-extendibility-to-Vopenka implication at every positive level.

Choose the source rank to be a second C(n)-extendible cardinal. It is sufficiently
correct and models ZF by the existing inaccessibility theorem. The target rank
also models ZF by elementarity. Absolute arbitrary-language coding in those
transitive ZF models replaces the coarse numerical dictionary bounds.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem eval_vopenkaReflectionFormula_components {M : Type*} [SetStructure M]
    (φ : SetTheorySemisentence 2) (κ B a L : M) :
    (vopenkaReflectionFormula φ).Evalb ![κ, B, a, L] ↔
      ∃ A : M, piOneHierarchyFormula.Evalb ![A, κ] ∧
        ∃ X : M, X ∈ A ∧ φ.Evalb ![X, a] ∧
          ∃ f : M, codedElementaryEmbeddingFormula.Evalb ![L, X, B, f] := by
  simp [vopenkaReflectionFormula]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Unbounded C(k+1)-extendibles imply every Pi(k+2) Vopenka instance.
There is no lower bound on `k` beyond it being a natural number. -/
theorem cnExtendible_unbounded_implies_pi_vopenka_sharp {k : ℕ}
    (hE : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsCnExtendible (k + 1) κ)
    (φ : SetTheorySemisentence 2) (hφ : IsPiFormula (k + 2) φ) : VopenkaInstance (V := V) φ := by
  intro L a hproper hclass
  let b := ⟨L, ⟨a, syntaxUniverse L ∅⟩ₖ⟩ₖ
  obtain ⟨κ, hbκ, hκ⟩ := hE (rank b) inferInstance
  let := hκ.1.1
  let := hierarchy_transitive κ
  have hb : b ∈ hierarchy κ := (mem_hierarchy_iff_rank_mem _ _).mpr hbκ
  obtain ⟨hLκ, hap⟩ := kpair_components_mem_transitive hb
  obtain ⟨haκ, hsyntaxκ⟩ := kpair_components_mem_transitive hap
  obtain ⟨B, hBclass, hκB⟩ := hproper.rank_unbounded κ
  have hB := hclass B hBclass
  obtain ⟨μ, hBμ, hμE⟩ := hE (rank B) inferInstance
  have hμ : Cn (k + 2) μ := hμE.cn.of_le (by omega)
  have hμrank := hμE.inaccessible.rankCriterion
  let := hμ.ordinal
  let := rankDomain_nonempty hμrank.2.1
  let := hμrank.models_zf
  have hκμ := IsOrdinal.toIsTransitive.mem_trans hκB hBμ
  have hμ1 : Cn (k + 1) μ := hμ.of_le (by omega)
  obtain ⟨θ, e, hμθ, hθ, he, hc, hμeκ⟩ := hκ.2 μ hμ1 hκμ
  let := hθ.ordinal
  let := hierarchy_transitive μ
  let := hierarchy_transitive θ
  let : Nonempty (SetDomain (hierarchy θ)) := by
    obtain ⟨x, hx⟩ := he.target_nonempty.nonempty
    exact ⟨⟨x, hx⟩⟩
  have hθZF : (SetDomain (hierarchy θ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
    refine ⟨fun ψ hψ ↦ ?_⟩
    have hs : ψ.Evalb (![] : Fin 0 → SetDomain (hierarchy μ)) :=
      Theory.models (SetDomain (hierarchy μ)) 𝗭𝗙 hψ
    have ht := (he.eval_semisentence ψ ![]).mp hs
    have hv : he.toFunction ∘ (![] : Fin 0 → SetDomain (hierarchy μ)) =
        (![] : Fin 0 → SetDomain (hierarchy θ)) := by funext i; exact Fin.elim0 i
    rw [hv] at ht
    exact ht
  let := hθZF
  let := IsFunction.of_mem he.function
  have hVκ : hierarchy κ ∈ hierarchy μ := hierarchy_mem hκμ
  have haμ : a ∈ hierarchy μ := (hierarchy_transitive μ).mem_trans haκ hVκ
  have hLμ : L ∈ hierarchy μ := (hierarchy_transitive μ).mem_trans hLκ hVκ
  have hBμV : B ∈ hierarchy μ := (mem_hierarchy_iff_rank_mem _ _).mpr hBμ
  have hκμV : κ ∈ hierarchy μ := ordinal_subset_hierarchy μ κ hκμ
  have hfix := rankEmbedding_fixed_below_criticalPoint hμ1 hθ he hc
  have hafix : e ‘ a = a := hfix a haκ
  have hLfix : e ‘ L = L := hfix L hLκ
  have hgeneric := rankEmbedding_generic_restrict_zf hμ1 hθ he hc hLκ
    ((hierarchy_transitive κ).transitive _ hsyntaxκ) hB hBμV
  have hVμθ : hierarchy μ ∈ hierarchy θ := hierarchy_mem hμθ
  have hBθ : B ∈ hierarchy θ := (hierarchy_transitive θ).mem_trans hBμV hVμθ
  have haθ : a ∈ hierarchy θ := (hierarchy_transitive θ).mem_trans haμ hVμθ
  have hLθ : L ∈ hierarchy θ := (hierarchy_transitive θ).mem_trans hLμ hVμθ
  have heκ : IsOrdinal (e ‘ κ) := he.value_ordinal hc.ordinal hc.mem_domain
  have heκθ : e ‘ κ ∈ hierarchy θ := function_value_mem he.function hκμV
  have heBθ : e ‘ B ∈ hierarchy θ := function_value_mem he.function hBμV
  have hBeκ : B ∈ hierarchy (e ‘ κ) :=
    (mem_hierarchy_iff_rank_mem _ _).mpr (IsOrdinal.toIsTransitive.mem_trans hBμ hμeκ)
  have hDθ : structureDomain B ∈ hierarchy θ :=
    (hierarchy_transitive θ).mem_trans (hB.domain_mem_transitive hBμV) hVμθ
  have hD'θ : structureDomain (e ‘ B) ∈ hierarchy θ := hgeneric.target.domain_mem_transitive heBθ
  have hf0 : e ↾ (structureDomain B) ∈ hierarchy θ := by
    have hsub := (mem_function_iff.mp hgeneric.function).1
    exact (hierarchy_transitive θ).mem_trans (mem_power_iff.mpr hsub)
      (power_mem_hierarchy_limit hθ.successor_closed
        (prod_mem_hierarchy_limit hθ.successor_closed hDθ hD'θ))
  let : Defined (fun v : Fin 2 → V ↦ φ.Evalb v) φ := ⟨fun _ ↦ Iff.rfl⟩
  have hθΘ : (vopenkaReflectionFormula φ).Evalb
      (![⟨e ‘ κ, heκθ⟩, ⟨e ‘ B, heBθ⟩, ⟨a, haθ⟩, ⟨L, hLθ⟩] : Fin 4 → SetDomain (hierarchy θ)) := by
    apply (eval_vopenkaReflectionFormula_components φ _ _ _ _).mpr
    refine ⟨⟨hierarchy (e ‘ κ), hθ.hierarchy_closed heκ heκθ⟩, ?_, ⟨B, hBθ⟩, hBeκ, ?_,
      ⟨e ↾ (structureDomain B), hf0⟩, ?_⟩
    · exact (hθ.hierarchy_formula_correct _ _).mpr ⟨heκ, rfl⟩
    · have hd := hθ.defined_pi_succ_downward hφ (fun v ↦ φ.Evalb v) ![⟨B, hBθ⟩, ⟨a, haθ⟩]
      have hv : (fun i ↦ ((![⟨B, hBθ⟩, ⟨a, haθ⟩] : Fin 2 → SetDomain (hierarchy θ)) i).val) = ![B, a] := by
        funext i
        exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
      rw [hv] at hd
      exact hd hBclass
    · exact (Defined.eval_iff (R := fun v : Fin 4 → SetDomain (hierarchy θ) ↦
        IsCodedElementaryEmbedding (v 0) (v 1) (v 2) (v 3)) _).mpr
        ((TransitiveZF.codedElementaryEmbedding_iff (hierarchy θ) _ _ _ _).mp hgeneric)
  have hμΘ : (vopenkaReflectionFormula φ).Evalb
      (![⟨κ, hκμV⟩, ⟨B, hBμV⟩, ⟨a, haμ⟩, ⟨L, hLμ⟩] : Fin 4 → SetDomain (hierarchy μ)) := by
    rw [he.eval_semisentence]
    convert hθΘ using 2
    funext i
    refine Fin.cases rfl (fun j ↦ Fin.cases rfl (fun l ↦ Fin.cases ?_ (fun t ↦ Fin.cases ?_ (fun s ↦ Fin.elim0 s) t) l) j) i
    · exact Subtype.ext hafix
    · exact Subtype.ext hLfix
  obtain ⟨A, hA, X, hXA, hφX, f, hf⟩ :=
    (eval_vopenkaReflectionFormula_components φ _ _ _ _).mp hμΘ
  have hA' := (hμ.hierarchy_formula_correct A ⟨κ, hκμV⟩).mp hA
  have hXκ : X.val ∈ hierarchy κ := by
    have : X.val ∈ A.val := hXA
    rwa [hA'.2] at this
  have hφX' : φ.Evalb ![X.val, a] := by
    have hd := hμ.defined_correct hφ (fun v ↦ φ.Evalb v) ![X, ⟨a, haμ⟩]
    have hv : (fun i ↦ ((![X, ⟨a, haμ⟩] : Fin 2 → SetDomain (hierarchy μ)) i).val) = ![X.val, a] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
    rw [hv] at hd
    exact hd.mp hφX
  have hemb : IsCodedElementaryEmbedding L X.val B f.val :=
    (TransitiveZF.codedElementaryEmbedding_iff (hierarchy μ) _ _ _ _).mpr
      ((Defined.eval_iff (R := fun v : Fin 4 → SetDomain (hierarchy μ) ↦
        IsCodedElementaryEmbedding (v 0) (v 1) (v 2) (v 3)) _).mp hf)
  refine ⟨X.val, B, f.val, ?_, hφX', hBclass, hemb⟩
  intro hXB
  rw [hXB] at hXκ
  have hr := (mem_hierarchy_iff_rank_mem B κ).mp hXκ
  exact mem_irrefl κ (IsOrdinal.toIsTransitive.mem_trans hκB hr)

end ZFVP
