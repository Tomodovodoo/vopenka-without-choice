import ZFVP.SetTheory.VopenkaScheme
import ZFVP.SetTheory.CnExtendible
import ZFVP.ModelTheory.GenericRankEmbeddingRestriction

/-! Unbounded C(n)-extendibility proves every parameterized arbitrary-language Vopenka instance. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem unboundedExtendibility_implies_vopenka
    (hUE : ∀ n : ℕ, ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsCnExtendible (n + 1) κ)
    (φ : SetTheorySemisentence 2) : VopenkaInstance (V := V) φ := by
  intro L a hproper hclass
  let b := ⟨L, ⟨a, syntaxUniverse L ∅⟩ₖ⟩ₖ
  let n := max coreSyntaxDictionaryBound (levySyntacticBound φ)
  obtain ⟨κ, hbκ, hκ⟩ := hUE n (rank b) inferInstance
  let := hκ.1.1
  let := hierarchy_transitive κ
  have hb : b ∈ hierarchy κ := (mem_hierarchy_iff_rank_mem _ _).mpr hbκ
  obtain ⟨hLκ, hap⟩ := kpair_components_mem_transitive hb
  obtain ⟨haκ, hsyntaxκ⟩ := kpair_components_mem_transitive hap
  obtain ⟨M, hMclass, hκM⟩ := hproper.rank_unbounded κ
  have hM := hclass M hMclass
  obtain ⟨μ, hMμ, hμ⟩ := cn_unbounded (n + 1) (rank M)
  let := hμ.ordinal
  have hκμ := IsOrdinal.toIsTransitive.mem_trans hκM hMμ
  obtain ⟨θ, f, _, hθ, hf, hc, hμfκ⟩ := hκ.2 μ hμ hκμ
  let := hθ.ordinal
  let := hierarchy_transitive μ
  let := hierarchy_transitive θ
  have hVκ : hierarchy κ ∈ hierarchy μ := hierarchy_mem hκμ
  have haμ := (hierarchy_transitive μ).mem_trans haκ hVκ
  have hMμV : M ∈ hierarchy μ := (mem_hierarchy_iff_rank_mem _ _).mpr hMμ
  have hafix := rankEmbedding_fixed_below_criticalPoint hμ hθ hf hc a haκ
  have hφ : IsPiFormula (n + 1) φ := (isLevyFormula_syntacticBound φ .pi).mono (by dsimp [n]; omega)
  let : Defined (fun v : Fin 2 → V ↦ φ.Evalb v) φ := ⟨fun _ ↦ Iff.rfl⟩
  have he := rankEmbedding_defined_iff hμ hθ hf hφ (fun v ↦ φ.Evalb v) ![M, a] (by simp [hMμV, haμ])
  have hv : (fun i ↦ f ‘ (![M, a] i)) = ![f ‘ M, a] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases hafix (fun t ↦ Fin.elim0 t) j) i
  rw [hv] at he
  have htarget := he.mp hMclass
  have hgeneric := rankEmbedding_generic_restrict hμ hθ hf hc (by dsimp [n]; omega)
    hLκ ((hierarchy_transitive κ).transitive _ hsyntaxκ) hM hMμV
  have hne : M ≠ f ‘ M := by
    intro hsame
    have hrfix : f ‘ (rank M) = rank M := by
      rw [rankEmbedding_value_rank hμ hθ hf hMμV, ← hsame]
    have hm := (hf.value_mem_iff hc.mem_domain (hμ.rank_closed hMμV)).mpr hκM
    rw [hrfix] at hm
    have hback : rank M ∈ f ‘ κ := by
      let := hf.value_ordinal hc.ordinal hc.mem_domain
      exact IsOrdinal.toIsTransitive.mem_trans hMμ hμfκ
    exact mem_irrefl (rank M) (IsOrdinal.toIsTransitive.mem_trans hback hm)
  exact ⟨M, f ‘ M, f ↾ (structureDomain M), hne, hMclass, htarget, hgeneric⟩

end ZFVP
