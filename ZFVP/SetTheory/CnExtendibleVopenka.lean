import ZFVP.SetTheory.VopenkaScheme
import ZFVP.SetTheory.CnExtendible
import ZFVP.SetTheory.CnLevyTransport
import ZFVP.ModelTheory.GenericRankEmbeddingRestriction

/-! Bagaria, C(n)-cardinals, Theorem 4.11 in the E_n form used by the paper:
unboundedly many C(n)-extendible cardinals give every Pi(n+1) instance of the
parameterized arbitrary-language Vopenka scheme. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Some `X` in the rank stage of the first variable satisfies the class formula with the third
variable and embeds elementarily, in the language of the fourth variable, into the second. -/
def vopenkaReflectionFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 4 :=
  “κ B a L. ∃ A X f, !piOneHierarchyFormula A κ ∧ X ∈ A ∧ !φ X a ∧
    !codedElementaryEmbeddingFormula L X B f”

/-- The fixed complexity of the coded elementary-embedding dictionary. -/
def codedElementaryEmbeddingBound : ℕ := levySyntacticBound codedElementaryEmbeddingFormula

theorem codedElementaryEmbeddingFormula_complexity (p : LevyPolarity) :
    IsLevyFormula p codedElementaryEmbeddingBound codedElementaryEmbeddingFormula :=
  isLevyFormula_syntacticBound _ p

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem cnExtendible_unbounded_implies_pi_vopenka {k : ℕ}
    (hk : coreSyntaxDictionaryBound ≤ k + 1) (hk' : codedElementaryEmbeddingBound ≤ k + 1)
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
  obtain ⟨μ, hBμ, hμ⟩ := cn_unbounded (k + 2) (rank B)
  let := hμ.ordinal
  have hκμ := IsOrdinal.toIsTransitive.mem_trans hκB hBμ
  have hμ1 : Cn (k + 1) μ := hμ.of_le (by omega)
  obtain ⟨θ, e, hμθ, hθ, he, hc, hμeκ⟩ := hκ.2 μ hμ1 hκμ
  let := hθ.ordinal
  let := hierarchy_transitive μ
  let := hierarchy_transitive θ
  let := IsFunction.of_mem he.function
  have hVκ : hierarchy κ ∈ hierarchy μ := hierarchy_mem hκμ
  have haμ : a ∈ hierarchy μ := (hierarchy_transitive μ).mem_trans haκ hVκ
  have hLμ : L ∈ hierarchy μ := (hierarchy_transitive μ).mem_trans hLκ hVκ
  have hBμV : B ∈ hierarchy μ := (mem_hierarchy_iff_rank_mem _ _).mpr hBμ
  have hκμV : κ ∈ hierarchy μ := ordinal_subset_hierarchy μ κ hκμ
  have hfix := rankEmbedding_fixed_below_criticalPoint hμ1 hθ he hc
  have hafix : e ‘ a = a := hfix a haκ
  have hLfix : e ‘ L = L := hfix L hLκ
  have hgeneric := rankEmbedding_generic_restrict hμ1 hθ he hc hk hLκ
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
  have hembφ : IsLevyFormula .pi (k + 1) codedElementaryEmbeddingFormula :=
    (codedElementaryEmbeddingFormula_complexity .pi).mono hk'
  -- the reflection statement holds in the target stage
  have hθΘ : (vopenkaReflectionFormula φ).Evalb
      (![⟨e ‘ κ, heκθ⟩, ⟨e ‘ B, heBθ⟩, ⟨a, haθ⟩, ⟨L, hLθ⟩] : Fin 4 → SetDomain (hierarchy θ)) := by
    simp only [vopenkaReflectionFormula]
    simp
    refine ⟨⟨hierarchy (e ‘ κ), hθ.hierarchy_closed heκ heκθ⟩, ?_, ⟨B, hBθ⟩, hBeκ, ?_,
      ⟨e ↾ (structureDomain B), hf0⟩, ?_⟩
    · exact (hθ.hierarchy_formula_correct _ _).mpr ⟨heκ, rfl⟩
    · have hd := hθ.defined_pi_succ_downward hφ (fun v ↦ φ.Evalb v) ![⟨B, hBθ⟩, ⟨a, haθ⟩]
      have hv : (fun i ↦ ((![⟨B, hBθ⟩, ⟨a, haθ⟩] : Fin 2 → SetDomain (hierarchy θ)) i).val) = ![B, a] := by
        funext i
        exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
      rw [hv] at hd
      exact hd hBclass
    · have hd := hθ.defined_correct hembφ
        (fun v ↦ IsCodedElementaryEmbedding (v 0) (v 1) (v 2) (v 3))
        ![⟨L, hLθ⟩, ⟨B, hBθ⟩, ⟨e ‘ B, heBθ⟩, ⟨e ↾ (structureDomain B), hf0⟩]
      exact hd.mpr hgeneric
  -- pull it back along the embedding
  have hμΘ : (vopenkaReflectionFormula φ).Evalb
      (![⟨κ, hκμV⟩, ⟨B, hBμV⟩, ⟨a, haμ⟩, ⟨L, hLμ⟩] : Fin 4 → SetDomain (hierarchy μ)) := by
    rw [he.eval_semisentence]
    convert hθΘ using 2
    funext i
    refine Fin.cases rfl (fun j ↦ Fin.cases rfl (fun l ↦ Fin.cases ?_ (fun t ↦ Fin.cases ?_ (fun s ↦ Fin.elim0 s) t) l) j) i
    · exact Subtype.ext hafix
    · exact Subtype.ext hLfix
  simp only [vopenkaReflectionFormula] at hμΘ
  simp at hμΘ
  obtain ⟨A, hA, X, hXA, hφX, f, hf⟩ := hμΘ
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
    (hμ.defined_correct (hembφ.mono (by omega))
      (fun v ↦ IsCodedElementaryEmbedding (v 0) (v 1) (v 2) (v 3))
      ![⟨L, hLμ⟩, X, ⟨B, hBμV⟩, f]).mp hf
  refine ⟨X.val, B, f.val, ?_, hφX', hBclass, hemb⟩
  intro hXB
  rw [hXB] at hXκ
  have hr := (mem_hierarchy_iff_rank_mem B κ).mp hXκ
  exact mem_irrefl κ (IsOrdinal.toIsTransitive.mem_trans hκB hr)

/-- Every instance of the arbitrary-language scheme has a syntactic Levy bound, so any
finite list of instances follows from unboundedly many E_n cardinals for one large n.
This replaces the paper's finite-language reduction (lem:finite-language-reduction). -/
theorem cnExtendible_unbounded_implies_vopenka_list {k : ℕ}
    (hk : coreSyntaxDictionaryBound ≤ k + 1) (hk' : codedElementaryEmbeddingBound ≤ k + 1)
    (hE : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsCnExtendible (k + 1) κ)
    (φs : List (SetTheorySemisentence 2)) (hφs : ∀ φ ∈ φs, levySyntacticBound φ ≤ k + 2) :
    ∀ φ ∈ φs, VopenkaInstance (V := V) φ := fun φ hφ ↦
  cnExtendible_unbounded_implies_pi_vopenka hk hk' hE φ
    ((isLevyFormula_syntacticBound φ .pi).mono (hφs φ hφ))

end ZFVP
