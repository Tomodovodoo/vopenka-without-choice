import ZFVP.ModelTheory.LimitRankEmbedding
import ZFVP.SetTheory.PiOneHierarchy
import ZFVP.ModelTheory.TransitiveZFAbsoluteness

/-! The rank formulas are absolute in every limit rank segment. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedRankCertificateBody : SetTheorySemisentence 5 :=
  “T R f α x. !IsTransitive.dfn T ∧ x ∈ T ∧
    !boundedRankTableFormula T R f ∧ !boundedPairMemberFormula f x α”

theorem boundedRankCertificateBody_bounded : IsBoundedSetFormula boundedRankCertificateBody :=
  .and (isTransitiveFormula_bounded.subst _) (.and (.rel _ _)
    (.and (boundedRankTableFormula_bounded.subst _) (boundedPairMemberFormula_bounded.subst _)))

theorem eval_sigmaOneRankFormula_witnesses {M : Type*} [SetStructure M] (α x : M) :
    sigmaOneRankFormula.Evalb ![α, x] ↔
      ∃ T R f : M, boundedRankCertificateBody.Evalb ![T, R, f, α, x] := by
  simp [sigmaOneRankFormula, boundedRankCertificateBody, exists_and_left]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankCertificate_exists_in_limit {κ x : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hx : x ∈ hierarchy κ) :
    ∃ T ∈ hierarchy κ, ∃ R ∈ hierarchy κ, ∃ g ∈ hierarchy κ,
      boundedRankCertificateBody.Evalb ![T, R, g, rank x, x] := by
  let T := hierarchy (succ (rank x))
  let : IsTransitive T := hierarchy_transitive _
  have hr := (mem_hierarchy_iff_rank_mem x κ).mp hx
  have hT : T ∈ hierarchy κ := hierarchy_mem (hκ _ hr)
  have hxT : x ∈ T := by
    rw [mem_hierarchy_iff_rank_mem]
    simp
  have hRT : rank T ∈ hierarchy κ := by
    rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]
    exact (mem_hierarchy_iff_rank_mem _ _).mp hT
  obtain ⟨g, hgκ, hg⟩ := rankTable_exists_in_limit hκ hT
  let := IsFunction.of_mem hg.1
  have hp : ⟨x, rank x⟩ₖ ∈ g := kpair_mem_iff_value.mpr
    ⟨by simpa only [domain_eq_of_mem_function hg.1] using hxT, rankTable_correct hg x hxT⟩
  refine ⟨T, hT, rank T, hRT, g, hgκ, ?_⟩
  simp [boundedRankCertificateBody, hxT, hp, (eval_boundedRankTableFormula _ _).mpr hg]
  infer_instance

theorem sigmaOneRankFormula_absolute_limit {κ : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (α x : SetDomain (hierarchy κ)) :
    sigmaOneRankFormula.Evalb ![α, x] ↔ α.val = rank x.val := by
  let := hierarchy_transitive κ
  constructor
  · intro h
    have he := sigma_one_upward (hierarchy κ) sigmaOneRankFormula_sigmaOne ![α, x] h
    have hv : (fun i ↦ (![α, x] i).val) = ![α.val, x.val] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
    rw [hv] at he
    exact (eval_sigmaOneRankFormula α.val x.val).mp he
  · intro hα
    obtain ⟨T, hT, R, hR, g, hg, hb⟩ := rankCertificate_exists_in_limit hκ x.property
    have hb' : boundedRankCertificateBody.Evalb ![T, R, g, α.val, x.val] := by simpa only [hα] using hb
    let t : SetDomain (hierarchy κ) := ⟨T, hT⟩
    let r : SetDomain (hierarchy κ) := ⟨R, hR⟩
    let f : SetDomain (hierarchy κ) := ⟨g, hg⟩
    have he := bounded_formula_absolute (hierarchy κ) boundedRankCertificateBody_bounded ![t, r, f, α, x]
    have hv : (fun i ↦ (![t, r, f, α, x] i).val) = ![T, R, g, α.val, x.val] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
        (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun z ↦ Fin.elim0 z) m) l) k) j) i
    rw [hv] at he
    have hl := he.mpr hb'
    exact (eval_sigmaOneRankFormula_witnesses α x).mpr ⟨t, r, f, hl⟩

theorem piOneRankFormula_absolute_limit {κ : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (α x : SetDomain (hierarchy κ)) :
    piOneRankFormula.Evalb ![α, x] ↔ α.val = rank x.val := by
  have hr : rank x.val ∈ hierarchy κ := by
    rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]
    exact (mem_hierarchy_iff_rank_mem _ _).mp x.property
  simp [piOneRankFormula, sigmaOneNonRankFormula, sigmaOneRankFormula_absolute_limit hκ, ← imp_iff_not_or]
  constructor
  · intro h
    exact (congrArg Subtype.val (h ⟨rank x.val, hr⟩ rfl)).symm
  · intro h β hβ
    exact Subtype.ext (hβ.trans h.symm)

theorem sigmaOneRankLtFormula_absolute_limit {κ : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (x α : SetDomain (hierarchy κ)) :
    sigmaOneRankLtFormula.Evalb ![x, α] ↔ rank x.val ∈ α.val := by
  have hr : rank x.val ∈ hierarchy κ := by
    rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]
    exact (mem_hierarchy_iff_rank_mem _ _).mp x.property
  simp [sigmaOneRankLtFormula, sigmaOneRankFormula_absolute_limit hκ]
  constructor
  · rintro ⟨β, hβ, he⟩
    exact he ▸ hβ
  · intro hx
    exact ⟨⟨rank x.val, hr⟩, hx, rfl⟩

theorem piOneRankLtFormula_absolute_limit {κ : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (x α : SetDomain (hierarchy κ)) :
    piOneRankLtFormula.Evalb ![x, α] ↔ rank x.val ∈ α.val := by
  have hr : rank x.val ∈ hierarchy κ := by
    rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]
    exact (mem_hierarchy_iff_rank_mem _ _).mp x.property
  simp [piOneRankLtFormula, piOneRankFormula_absolute_limit hκ]
  constructor
  · rintro ⟨β, hβ, he⟩
    exact he ▸ hβ
  · intro hx
    exact ⟨⟨rank x.val, hr⟩, hx, rfl⟩

theorem piOneHierarchyFormula_absolute_limit {κ : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (A α : SetDomain (hierarchy κ)) :
    piOneHierarchyFormula.Evalb ![A, α] ↔ IsOrdinal α.val ∧ A.val = hierarchy α.val := by
  let := hierarchy_transitive κ
  simp [piOneHierarchyFormula, TransitiveZF.ordinal_iff,
    sigmaOneRankLtFormula_absolute_limit hκ, piOneRankLtFormula_absolute_limit hκ]
  intro hα
  let := hα
  constructor
  · intro he
    apply mem_ext
    intro x
    rw [mem_hierarchy_iff_rank_mem]
    constructor
    · intro hx
      exact (he ⟨x, (hierarchy_transitive κ).mem_trans hx A.property⟩).1 hx
    · intro hx
      have hxκ : x ∈ hierarchy κ := by
        rw [mem_hierarchy_iff_rank_mem]
        exact IsOrdinal.toIsTransitive.mem_trans hx
          (by simpa only [mem_hierarchy_iff_rank_mem, rank_of_ordinal] using α.property)
      exact (he ⟨x, hxκ⟩).2 hx
  · intro hA x
    change (x.val ∈ A.val → rank x.val ∈ α.val) ∧ (rank x.val ∈ α.val → x.val ∈ A.val)
    rw [hA, mem_hierarchy_iff_rank_mem]
    exact ⟨id, id⟩

end ZFVP
