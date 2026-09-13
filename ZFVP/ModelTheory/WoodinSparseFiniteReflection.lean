import ZFVP.SetTheory.FiniteDictionaryReflection
import ZFVP.ModelTheory.WoodinSparseSourceFiniteRank

/-! Finite reflection captures the actual sparse forcing tables and cutoff table.

The graph formula is explicit input: the existing definability instances allow
parameters and do not supply the parameter-free dictionary required here.
The reflection theorem proves full-code capture from that graph formula. A
uniform effective restoration level also requires the endpoint finite-window
complexity bound.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseCompleteStageCode (θ : V) : V :=
  ⟨woodinSparseSourceStageCode θ, woodinSparseSourceStageCardinals θ⟩ₖ

instance woodinSparseCompleteStageCode_definable :
    ℒₛₑₜ-function₁[V] woodinSparseCompleteStageCode := by
  unfold woodinSparseCompleteStageCode
  definability

def woodinSparseReflectionDictionary (r : ℕ) (code : SetTheorySemisentence 2) :
    List (SetTheorySemisentence 6) :=
  [“η δ θ ρ α x. !(cnFormula r) θ”,
   “η δ θ ρ α x. !woodinSupercompactFormula θ”,
   “η δ θ ρ α x. !code x θ”]

theorem eval_woodinSparseReflectionDictionary (r : ℕ) (code : SetTheorySemisentence 2)
    (hcode : ∀ x θ : V, code.Evalb ![x, θ] ↔ x = woodinSparseCompleteStageCode θ)
    (η δ θ ρ α x : V) :
    (∀ e ∈ woodinSparseReflectionDictionary r code,
      e.Evalb ![η, δ, θ, ρ, α, x]) ↔
      Cn r θ ∧ IsWoodinSupercompact θ ∧ x = woodinSparseCompleteStageCode θ := by
  simp only [Semiformula.Evalb] at hcode
  simp [woodinSparseReflectionDictionary, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, hcode]

theorem woodinSparseCompleteStageCode_finiteRank {θ : V}
    (hθ : IsWoodinSupercompact θ) (hAC : ¬InternalChoice V) :
    woodinSparseCompleteStageCode θ ∈ hierarchy (ordinalAdd θ (ω : V)) :=
  woodinSparseSourceStageCode_pair_finiteRank_at_endpoint hθ hAC

/-- The dictionary reflection lemma applied to the complete actual sparse code. -/
theorem finite_reflection_woodinSparseCompleteStageCode {c k r : ℕ}
    (code : SetTheorySemisentence 2)
    (hcode : ∀ x θ : V, code.Evalb ![x, θ] ↔ x = woodinSparseCompleteStageCode θ)
    (hc : 2 ≤ c) (hD : listBound (woodinSparseReflectionDictionary r code) ≤ c)
    (hck : c ≤ k) {η δ θ ρ α : V}
    (hδ : IsCnExtendible (k + 1) δ) (hρ : Cn c ρ)
    (hηδ : η ∈ δ) (hδθ : δ ∈ θ) (hθρ : ordinalAdd θ (ω : V) ∈ ρ)
    (hαθ : α ∈ θ) (hθcn : Cn r θ) (hθ : IsWoodinSupercompact θ)
    (hAC : ¬InternalChoice V) :
    Reflects c (woodinSparseReflectionDictionary r code)
      ![η, δ, θ, ρ, α, woodinSparseCompleteStageCode θ] := by
  let := hρ.ordinal
  have hx : woodinSparseCompleteStageCode θ ∈ hierarchy ρ :=
    (hierarchy_transitive ρ).mem_trans
      (woodinSparseCompleteStageCode_finiteRank hθ hAC) (hierarchy_mem hθρ)
  exact finite_reflection _ hc hD hck hδ hρ hηδ hδθ hθρ hαθ hx
    ((eval_woodinSparseReflectionDictionary r code hcode η δ θ ρ α _).mpr ⟨hθcn, hθ, rfl⟩)

/-- Decode the reflected conjunction in the ambient universe. In particular,
the reflected source object is the actual complete source code. -/
theorem exists_woodinSparse_reflected_embedding {c r : ℕ}
    (code : SetTheorySemisentence 2)
    (hcode : ∀ x θ : V, code.Evalb ![x, θ] ↔ x = woodinSparseCompleteStageCode θ)
    {η δ θ ρ α : V}
    (href : Reflects c (woodinSparseReflectionDictionary r code)
      ![η, δ, θ, ρ, α, woodinSparseCompleteStageCode θ]) :
    ∃ e θ' ρ' α' f : V,
      η ∈ e ∧ e ∈ θ' ∧ ordinalAdd θ' (ω : V) ∈ ρ' ∧ ρ' ∈ δ ∧ α' ∈ θ' ∧
      Cn c ρ' ∧ Cn r θ' ∧ IsWoodinSupercompact θ' ∧
      IsCodedMembershipEmbedding (hierarchy ρ') (hierarchy ρ) f ∧
      IsCriticalPoint (hierarchy ρ') f e ∧
      f ‘ e = δ ∧ f ‘ θ' = θ ∧ f ‘ α' = α ∧
      f ‘ (woodinSparseCompleteStageCode θ') = woodinSparseCompleteStageCode θ := by
  rcases href with ⟨e, θ', ρ', α', x', A, B, f, hm⟩
  change η ∈ e ∧ e ∈ θ' ∧ (∃ γ ∈ ρ', IsPlusOmega γ θ') ∧ ρ' ∈ δ ∧ δ ∈ θ ∧
    (∃ γ ∈ ρ, IsPlusOmega γ θ) ∧ α' ∈ θ' ∧
    (IsOrdinal ρ' ∧ A = hierarchy ρ') ∧ x' ∈ A ∧
    (IsOrdinal ρ ∧ B = hierarchy ρ) ∧ IsCodedMembershipEmbedding A B f ∧
    CriticalPointGraphSpec A f e ∧ ⟨e, δ⟩ₖ ∈ f ∧ ⟨θ', θ⟩ₖ ∈ f ∧
    ⟨α', α⟩ₖ ∈ f ∧ ⟨x', woodinSparseCompleteStageCode θ⟩ₖ ∈ f ∧
    Cn c ρ' ∧ ∀ d ∈ woodinSparseReflectionDictionary r code,
      d.Evalb ![η, e, θ', ρ', α', x'] at hm
  rcases hm with ⟨hηe, heθ', hbuf, hρ'δ, _, _, hα'θ',
    hA, _, hB, hf, hcrit, he, hθ', hα', hx', hρ', hD⟩
  rcases hbuf with ⟨β, hβ, hθ'ord, rfl⟩
  rcases hA with ⟨hρ'ord, rfl⟩
  rcases hB with ⟨hρord, rfl⟩
  obtain ⟨hcn, hsc, rfl⟩ :=
    (eval_woodinSparseReflectionDictionary r code hcode η e θ' ρ' α' x').mp hD
  let := hρ'ord
  let := hierarchy_transitive ρ'
  let := IsFunction.of_mem hf.function
  exact ⟨e, θ', ρ', α', f, hηe, heθ', hβ, hρ'δ, hα'θ', hρ', hcn, hsc, hf,
    (criticalPoint_iff_graphSpec hf.function).mpr hcrit,
    value_eq_of_kpair_mem he, value_eq_of_kpair_mem hθ',
    value_eq_of_kpair_mem hα', value_eq_of_kpair_mem hx'⟩

/-- Restriction retains the critical point, ordinal capture and complete code.
Its source and target are exactly the ground ranks used by the marked-rank lift. -/
theorem exists_woodinSparse_restricted_reflection {c r : ℕ}
    (code : SetTheorySemisentence 2)
    (hcode : ∀ x θ : V, code.Evalb ![x, θ] ↔ x = woodinSparseCompleteStageCode θ)
    (hc : 1 ≤ c) {η δ θ ρ α : V} (hρ : Cn c ρ) (hAC : ¬InternalChoice V)
    (href : Reflects c (woodinSparseReflectionDictionary r code)
      ![η, δ, θ, ρ, α, woodinSparseCompleteStageCode θ]) :
    ∃ e θ' α' J : V,
      η ∈ e ∧ e ∈ θ' ∧ θ' ∈ δ ∧ α' ∈ θ' ∧ Cn r θ' ∧ IsWoodinSupercompact θ' ∧
      IsCodedMembershipEmbedding (hierarchy (ordinalAdd θ' (ω : V)))
        (hierarchy (ordinalAdd θ (ω : V))) J ∧
      IsCriticalPoint (hierarchy (ordinalAdd θ' (ω : V))) J e ∧
      J ‘ e = δ ∧ J ‘ θ' = θ ∧ J ‘ α' = α ∧
      woodinSparseCompleteStageCode θ' ∈ hierarchy (ordinalAdd θ' (ω : V)) ∧
      J ‘ (woodinSparseCompleteStageCode θ') = woodinSparseCompleteStageCode θ := by
  obtain ⟨e, θ', ρ', α', f, hηe, heθ', hbuf, hρ'δ, hα'θ', hρ', hcn, hsc, hf,
    hcrit, he, hθ', hα', hcodef⟩ := exists_woodinSparse_reflected_embedding code hcode href
  let := hρ.ordinal
  let := hρ'.ordinal
  let := hsc.inaccessible.1
  let := hierarchy_transitive ρ'
  let := hierarchy_transitive ρ
  let := hierarchy_transitive (ordinalAdd θ' (ω : V))
  let := IsFunction.of_mem hf.function
  have hθ'buf : θ' ∈ ordinalAdd θ' (ω : V) := ordinalAdd_omega_gt θ'
  have hθ'ρ' : θ' ∈ ρ' := IsOrdinal.toIsTransitive.mem_trans hθ'buf hbuf
  have heρ' : e ∈ ρ' := IsOrdinal.toIsTransitive.mem_trans heθ' hθ'ρ'
  have heA : e ∈ hierarchy (ordinalAdd θ' (ω : V)) :=
    ordinal_subset_hierarchy _ _ (IsOrdinal.toIsTransitive.mem_trans heθ' hθ'buf)
  have hθ'A : θ' ∈ hierarchy (ordinalAdd θ' (ω : V)) := ordinal_subset_hierarchy _ _ hθ'buf
  have hα'A : α' ∈ hierarchy (ordinalAdd θ' (ω : V)) :=
    ordinal_subset_hierarchy _ _ (IsOrdinal.toIsTransitive.mem_trans hα'θ' hθ'buf)
  have hA : hierarchy (ordinalAdd θ' (ω : V)) ∈ hierarchy ρ' := hierarchy_mem hbuf
  have hsub : hierarchy (ordinalAdd θ' (ω : V)) ⊆ hierarchy ρ' :=
    (hierarchy_transitive ρ').transitive _ hA
  have hbufV : ordinalAdd θ' (ω : V) ∈ hierarchy ρ' := ordinal_subset_hierarchy _ _ hbuf
  have hθ'V : θ' ∈ hierarchy ρ' := ordinal_subset_hierarchy _ _ hθ'ρ'
  have hplus : IsPlusOmega (f ‘ (ordinalAdd θ' (ω : V))) (f ‘ θ') := by
    have h := hf.bounded_defined_iff plusOmegaFormula_bounded
      (fun v ↦ IsPlusOmega (v 0) (v 1)) ![ordinalAdd θ' (ω : V), θ']
      (by simp [Fin.forall_fin_succ, hbufV, hθ'V])
    apply h.mp
    change IsPlusOmega (ordinalAdd θ' (ω : V)) θ'
    exact ⟨inferInstance, rfl⟩
  have hbufImage : f ‘ (ordinalAdd θ' (ω : V)) = ordinalAdd θ (ω : V) := by
    rw [hθ'] at hplus
    exact hplus.2
  have hρ1 : Cn (0 + 1) ρ := hρ.of_le hc
  have hρ'1 : Cn (0 + 1) ρ' := hρ'.of_le hc
  have hδord : IsOrdinal δ := he ▸ hf.value_ordinal hcrit.ordinal hcrit.mem_domain
  let := hδord
  have hJ := rankEmbedding_restrict hρ'1 hρ1 hf hA ⟨e, heA⟩
  rw [(rankEmbedding_value_hierarchy hρ'1 hρ1 hf inferInstance hbufV).2, hbufImage] at hJ
  have hval : ∀ x ∈ hierarchy (ordinalAdd θ' (ω : V)),
      (f ↾ (hierarchy (ordinalAdd θ' (ω : V)))) ‘ x = f ‘ x := by
    intro x hx
    exact value_restrict (by rw [domain_eq_of_mem_function hf.function]; exact hsub _ hx) hx
  have hsourceCode := woodinSparseCompleteStageCode_finiteRank hsc hAC
  refine ⟨e, θ', α', f ↾ (hierarchy (ordinalAdd θ' (ω : V))), hηe, heθ',
    IsOrdinal.toIsTransitive.mem_trans hθ'ρ' hρ'δ, hα'θ', hcn, hsc, hJ,
    hcrit.restrict hf.function hsub heA, ?_, ?_, ?_, hsourceCode, ?_⟩
  · exact (hval _ heA).trans he
  · exact (hval _ hθ'A).trans hθ'
  · exact (hval _ hα'A).trans hα'
  · exact (hval _ hsourceCode).trans hcodef

end ZFVP
