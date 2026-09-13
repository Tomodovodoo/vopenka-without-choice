import ZFVP.ModelTheory.RubinFiniteTypes

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u v

/-- No new member is added to an old set which the source regards as finite. -/
def PreservesInternallyFiniteSets {M : Type u} {N : Type v} [SetStructure M] [SetStructure N]
    [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (j : ElementaryMap M N) : Prop :=
  ∀ a : M, IsInternallyFinite a → ∀ b : N, b ∈ j a → ∃ m ∈ a, j m = b

/-- The Rubin successor simultaneously omits separating types and the types
for new members of every old internally finite set. -/
theorem exists_finite_preserving_rubin_successor (M : Type u) [SetStructure M]
    [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M]
    (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2)
    (U W : ℕ → M → Prop) (hins : ∀ n, Inseparable M (U n) (W n))
    (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) :
    ∃ X : InseparableUpperBoundExtension M δ ρ U W,
      PreservesInternallyFiniteSets X.embedding := by
  classical
  let _ : Encodable M := Encodable.ofCountable M
  let I := (ℕ × ((q : ℕ) × Semisentence (LSetC (M ⊕ ℕ)) (q + 1))) ⊕
    {a : M // IsInternallyFinite a}
  let ar : I → ℕ := fun i ↦ match i with
    | .inl i => i.2.1
    | .inr _ => 1
  let types : (i : I) → PartialType (LSetC (M ⊕ ℕ)) (ar i) := fun i ↦ match i with
    | .inl i => separatingType (U i.1) (W i.1) i.2.2
    | .inr a => finiteNewMemberType a.val
  have : Nonempty I := ⟨Sum.inl (0, ⟨0, ⊤⟩)⟩
  obtain ⟨e, he⟩ := exists_surjective_nat I
  have hlocal : ∀ i : I, LocallyOmits (rubinTheory δ ρ) (types i) := by
    intro i
    cases i with
    | inl i => exact separatingTypesLocallyOmitted M δ ρ U W hins hdir i.1 i.2.1 i.2.2
    | inr a => exact finiteNewMemberType_locallyOmitted δ ρ hdir a.property
  obtain ⟨Om⟩ := omittingTypesTheoremEq (LSetC (M ⊕ ℕ)) (rubinTheory δ ρ)
    eqAxiom_subset_rubinTheory (consistent_rubinTheory hdir)
    (fun k ↦ ar (e k)) (fun k ↦ types (e k)) (fun k ↦ hlocal (e k))
  obtain ⟨NM⟩ := exists_normalModel (rubinTheory δ ρ) eqAxiom_subset_rubinTheory
    (fun k ↦ types (e k)) Om.Dom Om.models Om.omits
  obtain ⟨j, hj⟩ := elementaryMap_of_models_rubinTheory NM.assign NM.models
  have hjc : (fun m ↦ j m) = NM.assign ∘ Sum.inl := funext hj
  have hom : ∀ i : I, OmitsWith NM.Dom NM.assign (types i) := by
    intro i
    obtain ⟨k, hk⟩ := he i
    have h := NM.omits k
    rwa [hk] at h
  let X : InseparableUpperBoundExtension M δ ρ U W :=
    { Model := NM.Dom
      embedding := j
      inseparable := by
        intro n
        have h := inseparable_of_omits NM.assign (U n) (W n)
          (fun q ψ ↦ hom (Sum.inl (n, ⟨q, ψ⟩)))
        simpa only [hj] using h
      upperBound := by
        intro n
        obtain ⟨hmem, hbound⟩ := upperBound_of_models_rubinTheory NM.assign NM.models n
        refine ⟨NM.assign (Sum.inr n), ?_, fun m hm ↦ ?_⟩
        · rw [hjc]; exact hmem
        · rw [hjc, hj m]; exact hbound m hm }
  refine ⟨X, ?_⟩
  intro a ha b hb
  have homa : OmitsWith NM.Dom NM.assign (finiteNewMemberType a) := hom (Sum.inr ⟨a, ha⟩)
  obtain ⟨σ, hσ, hnσ⟩ := homa ![b]
  rcases hσ with rfl | ⟨m, hm, rfl⟩
  · exfalso
    apply hnσ
    apply (eval_substConst NM.assign _ _ ![b]).mpr
    change b ∈ NM.assign (Sum.inl a)
    simpa only [X, hj] using hb
  · refine ⟨m, hm, ?_⟩
    have heq : NM.assign (Sum.inl m) = b := by
      simpa [eval_substConst, eval_finiteEqualityTemplate] using hnσ
    change j m = b
    rw [hj]
    exact heq

end ZFVP
