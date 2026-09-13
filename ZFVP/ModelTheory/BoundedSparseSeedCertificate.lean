import ZFVP.ModelTheory.BoundedCoordinatePool
import ZFVP.ModelTheory.WoodinSparseSeedRecovery
import ZFVP.SetTheory.BoundedNameValueTable

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedEvaluatedPoolFormula : SetTheorySemisentence 3 :=
  “C W F. (∀ q ∈ C, ∃ τ ∈ W, !boundedValueFormula q F τ) ∧
    ∀ τ ∈ W, ∃ q ∈ C, !boundedValueFormula q F τ”

def boundedCollapseRowsFormula : SetTheorySemisentence 3 :=
  “m C T. !isSubsetOf m T ∧ ∀ r ∈ T, (r ∈ m ↔
    ∃ q ∈ C, ∃ ξ ∈ T, ∃ d ∈ T, ∃ v ∈ T,
      !boundedKpairFormula d r ξ ∧ !boundedPairMemberFormula q d v)”

theorem boundedEvaluatedPoolFormula_bounded : IsBoundedSetFormula boundedEvaluatedPoolFormula := by
  repeat' first
    | exact boundedValueFormula_bounded.subst _
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and

theorem boundedCollapseRowsFormula_bounded : IsBoundedSetFormula boundedCollapseRowsFormula := by
  repeat' first
    | exact isSubsetOf_bounded.subst _
    | exact boundedKpairFormula_bounded.subst _
    | exact (boundedKpairFormula_bounded.subst _).neg
    | exact boundedPairMemberFormula_bounded.subst _
    | exact (boundedPairMemberFormula_bounded.subst _).neg
    | exact IsBoundedSetFormula.rel _ _
    | exact (IsBoundedSetFormula.rel _ _).neg
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or

def boundedSparseSeedCertificateFormula : SetTheorySemisentence 7 :=
  “S T o F W C m. !boundedNameValueTableFormula o T F ∧
    !boundedCoordinatePoolFormula W S o ∧ !isSubsetOf W T ∧
    !boundedEvaluatedPoolFormula C W F ∧ !isSubsetOf C T ∧
    !boundedCollapseRowsFormula m C T”

theorem boundedSparseSeedCertificateFormula_bounded :
    IsBoundedSetFormula boundedSparseSeedCertificateFormula := by
  repeat' first
    | exact boundedNameValueTableFormula_bounded.subst _
    | exact boundedCoordinatePoolFormula_bounded.subst _
    | exact boundedEvaluatedPoolFormula_bounded.subst _
    | exact boundedCollapseRowsFormula_bounded.subst _
    | exact isSubsetOf_bounded.subst _
    | apply IsBoundedSetFormula.and

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedEvaluatedPoolFormula {C W F : V} :
    boundedEvaluatedPoolFormula.Evalb ![C, W, F] ↔
      ∀ q, q ∈ C ↔ ∃ τ ∈ W, q = F ‘ τ := by
  simp [boundedEvaluatedPoolFormula]
  constructor
  · rintro ⟨hl, hr⟩ q
    constructor
    · exact hl q
    · rintro ⟨τ, hτ, rfl⟩
      exact hr τ hτ
  · intro h
    exact ⟨fun q ↦ (h q).mp, fun τ hτ ↦ (h _).mpr ⟨τ, hτ, rfl⟩⟩

theorem collapseRowIndices_subset_transitive {C T : V} [IsTransitive T]
    (hC : C ⊆ T) : collapseRowIndices C ⊆ T := by
  intro r hr
  obtain ⟨q, hq, ξ, hξ⟩ := mem_collapseRowIndices_iff.mp hr
  obtain ⟨v, hv⟩ := mem_domain_iff.mp hξ
  have hd := (subname_pair_components_mem_transitive (hC q hq) hv).1
  exact (kpair_components_mem_transitive hd).1

theorem eval_boundedCollapseRowsFormula {m C T : V} [IsTransitive T]
    (hC : C ⊆ T) :
    boundedCollapseRowsFormula.Evalb ![m, C, T] ↔ m = collapseRowIndices C := by
  have he : boundedCollapseRowsFormula.Evalb ![m, C, T] ↔
      m ⊆ T ∧ ∀ r ∈ T, (r ∈ m ↔ ∃ q ∈ C, ∃ ξ ∈ T, ∃ d ∈ T, ∃ v ∈ T,
        d = ⟨r, ξ⟩ₖ ∧ ⟨d, v⟩ₖ ∈ q) := by simp [boundedCollapseRowsFormula]
  have hr (r : V) : (∃ q ∈ C, ∃ ξ ∈ T, ∃ d ∈ T, ∃ v ∈ T,
      d = ⟨r, ξ⟩ₖ ∧ ⟨d, v⟩ₖ ∈ q) ↔ r ∈ collapseRowIndices C := by
    rw [mem_collapseRowIndices_iff]
    constructor
    · rintro ⟨q, hq, ξ, _, d, _, v, _, rfl, hv⟩
      exact ⟨q, hq, ξ, mem_domain_of_kpair_mem hv⟩
    · rintro ⟨q, hq, ξ, hξ⟩
      obtain ⟨v, hv⟩ := mem_domain_iff.mp hξ
      have hdv := subname_pair_components_mem_transitive (hC q hq) hv
      exact ⟨q, hq, ξ, (kpair_components_mem_transitive hdv.1).2,
        ⟨r, ξ⟩ₖ, hdv.1, v, hdv.2, rfl, hv⟩
  rw [he]
  simp only [hr]
  constructor
  · rintro ⟨hm, he⟩
    apply mem_ext
    intro r
    constructor
    · intro h
      exact (he r (hm r h)).mp h
    · intro h
      exact (he r (collapseRowIndices_subset_transitive hC r h)).mpr h
  · rintro rfl
    exact ⟨collapseRowIndices_subset_transitive hC, fun _ _ ↦ Iff.rfl⟩

theorem boundedSparseSeedCertificate_unique {S T F W C m : V} [IsTransitive T]
    (h : boundedSparseSeedCertificateFormula.Evalb ![S, T, succ (∅ : V), F, W, C, m]) :
    m = sparseRecoveredSeed S := by
  have hs : boundedNameValueTableFormula.Evalb ![succ (∅ : V), T, F] ∧
      W = sparseCoordinatePool S (succ (∅ : V)) ∧ W ⊆ T ∧
      (∀ q, q ∈ C ↔ ∃ τ ∈ W, q = F ‘ τ) ∧ C ⊆ T ∧
      boundedCollapseRowsFormula.Evalb ![m, C, T] := by
    simpa [boundedSparseSeedCertificateFormula, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
      eval_boundedCoordinatePoolFormula, eval_boundedEvaluatedPoolFormula] using h
  obtain ⟨hF, rfl, hW, hC, hCT, hm⟩ := hs
  rw [eval_boundedCollapseRowsFormula hCT] at hm
  have hone : succ (∅ : V) = ({∅} : V) := by ext x; simp [mem_succ_iff]
  have he : C = sparseFirstCoordinateValues S := by
    apply mem_ext
    intro q
    rw [hC]
    unfold sparseFirstCoordinateValues
    rw [repl_spec (by definability)]
    constructor
    · rintro ⟨τ, hτ, hq⟩
      refine ⟨τ, hτ, hq.trans ?_⟩
      simpa only [hone] using boundedNameValueTable_unique hF τ (hW τ hτ)
    · rintro ⟨τ, hτ, hq⟩
      refine ⟨τ, hτ, hq.trans ?_⟩
      symm
      simpa only [hone] using boundedNameValueTable_unique hF τ (hW τ hτ)
  exact hm.trans (congrArg collapseRowIndices he)

theorem sparseFirstCoordinateValues_subset_transitive {S T : V}
    (hW : sparseCoordinatePool S (succ (∅ : V)) ⊆ T)
    (hT : ∀ τ ∈ T, nameValue ({∅} : V) τ ∈ T) :
    sparseFirstCoordinateValues S ⊆ T := by
  intro q hq
  obtain ⟨τ, hτ, rfl⟩ := (repl_spec (by definability)).mp hq
  exact hT τ (hW τ hτ)

theorem boundedSparseSeedCertificate_canonical {S T : V} [IsTransitive T]
    (hW : sparseCoordinatePool S (succ (∅ : V)) ⊆ T)
    (hT : ∀ τ ∈ T, nameValue ({∅} : V) τ ∈ T) :
    boundedSparseSeedCertificateFormula.Evalb ![S, T, succ (∅ : V),
      canonicalNameValueTable ({∅} : V) T, sparseCoordinatePool S (succ (∅ : V)),
      sparseFirstCoordinateValues S, sparseRecoveredSeed S] := by
  have hone : succ (∅ : V) = ({∅} : V) := by ext x; simp [mem_succ_iff]
  have hC := sparseFirstCoordinateValues_subset_transitive hW hT
  have hF : boundedNameValueTableFormula.Evalb
      ![succ (∅ : V), T, canonicalNameValueTable ({∅} : V) T] := by
    rw [hone]
    exact canonicalNameValueTable_spec hT
  have hv : boundedEvaluatedPoolFormula.Evalb ![sparseFirstCoordinateValues S,
      sparseCoordinatePool S (succ (∅ : V)), canonicalNameValueTable ({∅} : V) T] := by
    apply eval_boundedEvaluatedPoolFormula.mpr
    intro q
    unfold sparseFirstCoordinateValues
    rw [repl_spec (by definability)]
    constructor
    · rintro ⟨τ, hτ, hq⟩
      exact ⟨τ, hτ, hq.trans (canonicalNameValueTable_value (hW τ hτ)).symm⟩
    · rintro ⟨τ, hτ, hq⟩
      exact ⟨τ, hτ, hq.trans (canonicalNameValueTable_value (hW τ hτ))⟩
  have hm : boundedCollapseRowsFormula.Evalb
      ![sparseRecoveredSeed S, sparseFirstCoordinateValues S, T] :=
    (eval_boundedCollapseRowsFormula hC).mpr rfl
  simpa [boundedSparseSeedCertificateFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
    eval_boundedCoordinatePoolFormula] using And.intro hF
      (And.intro (show sparseCoordinatePool S (succ (∅ : V)) =
        sparseCoordinatePool S (succ (∅ : V)) from rfl)
        (And.intro hW (And.intro hv (And.intro hC hm))))

end ZFVP




