import ZFVP.SetTheory.BinaryExpansionContinuity
import ZFVP.SetTheory.CantorCompactness
import ZFVP.SetTheory.RealIntervalBasics

/-! Binary images of internal tree bodies are closed on the actual real line. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def binaryImage (K : V) : V := repl binaryReal binaryReal_definable K

theorem mem_binaryImage_iff (K x : V) : x ∈ binaryImage K ↔ ∃ c ∈ K, binaryReal c = x := by
  simp [binaryImage, repl_spec, eq_comm]

instance binaryImage_definable : ℒₛₑₜ-function₁[V] binaryImage := by
  have h : ℒₛₑₜ-relation (fun I K : V ↦ ∀ x, x ∈ I ↔ ∃ c ∈ K, binaryReal c = x) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_binaryImage_iff]

theorem binaryImage_subset_reals {K : V} (hK : K ⊆ cantorSpace V) :
    binaryImage K ⊆ dedekindReals V := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_binaryImage_iff _ _).mp hx
  exact binaryReal_mem (hK c hc)

noncomputable def binaryExcludedPrefixes (x : V) : V :=
  {s ∈ binarySequences V ; ∃ a ∈ internalRationals V, ∃ b ∈ internalRationals V,
    x ∈ realInterval a b ∧ ∀ c ∈ cantorSpace V, s ⊆ c → binaryReal c ∉ realInterval a b}

theorem mem_binaryExcludedPrefixes_iff (x s : V) : s ∈ binaryExcludedPrefixes x ↔
    s ∈ binarySequences V ∧ ∃ a ∈ internalRationals V, ∃ b ∈ internalRationals V,
      x ∈ realInterval a b ∧ ∀ c ∈ cantorSpace V, s ⊆ c → binaryReal c ∉ realInterval a b := by
  simp [binaryExcludedPrefixes]

instance binaryExcludedPrefixes_definable : ℒₛₑₜ-function₁[V] binaryExcludedPrefixes := by
  have h : ℒₛₑₜ-relation (fun S x : V ↦ ∀ s, s ∈ S ↔ s ∈ binarySequences V ∧
      ∃ a ∈ internalRationals V, ∃ b ∈ internalRationals V,
        x ∈ realInterval a b ∧ ∀ c ∈ cantorSpace V, s ⊆ c → binaryReal c ∉ realInterval a b) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_binaryExcludedPrefixes_iff]

theorem binaryExcludedPrefixes_cover {T x : V} (hx : IsDedekindCut x)
    (hxI : x ∉ binaryImage (treeBody T)) : treeBody T ⊆ openFrom (binaryExcludedPrefixes x) := by
  intro c hc
  have hcC := treeBody_subset_cantorSpace T c hc
  have hne : x ≠ binaryReal c := by
    intro he
    exact hxI ((mem_binaryImage_iff _ _).mpr ⟨c, hc, he.symm⟩)
  obtain ⟨a, ha, b, hb, u, hu, v, hv, hxi, hci, hdis⟩ :=
    realIntervals_separate hx (binaryReal_isCut hcC) hne
  obtain ⟨n, hn, hlo, hup⟩ := binaryPrefixEnds_inside hcC hu hv hci
  have hs := restrict_mem_binarySequences hcC hn
  refine (mem_openFrom_iff _ _).mpr ⟨hcC, c ↾ n, ?_,
    (subset_iff_restrict_eq hcC hs).mp (restrict_subset _ _)⟩
  exact (mem_binaryExcludedPrefixes_iff _ _).mpr ⟨hs, a, ha, b, hb, hxi,
    fun d hd hsd ↦ hdis _ (binaryReal_interval_of_prefix hcC hd hn hu hv hlo hup hsd)⟩

theorem binaryExcludedPrefixes_finite_neighborhood {x F : V} (hx : IsDedekindCut x)
    (hF : IsInternallyFinite F) (hFx : F ⊆ binaryExcludedPrefixes x) :
    ∃ a ∈ internalRationals V, ∃ b ∈ internalRationals V, x ∈ realInterval a b ∧
      ∀ s ∈ F, ∀ c ∈ cantorSpace V, s ⊆ c → binaryReal c ∉ realInterval a b := by
  have h := internallyFinite_induction
    (fun F ↦ F ⊆ binaryExcludedPrefixes x →
      ∃ a ∈ internalRationals V, ∃ b ∈ internalRationals V, x ∈ realInterval a b ∧
        ∀ s ∈ F, ∀ c ∈ cantorSpace V, s ⊆ c → binaryReal c ∉ realInterval a b)
    (by definability) ?_ ?_ F hF
  · exact h hFx
  · intro _
    obtain ⟨a, ha, b, hb, hxi⟩ := realInterval_neighborhood hx
    exact ⟨a, ha, b, hb, hxi, fun _ hs ↦ (not_mem_empty hs).elim⟩
  · intro A s ih hAs
    obtain ⟨a, ha, b, hb, hxi, havoid⟩ := ih (fun t ht ↦ hAs t (mem_insert.mpr (Or.inr ht)))
    obtain ⟨_, u, hu, v, hv, hxj, hsavoid⟩ := (mem_binaryExcludedPrefixes_iff _ _).mp
      (hAs s (mem_insert.mpr (Or.inl rfl)))
    obtain ⟨p, hp, q, hq, hxpq, hi, hj⟩ := realInterval_refine_inter ha hb hu hv hxi hxj
    refine ⟨p, hp, q, hq, hxpq, ?_⟩
    intro t ht c hc htc hcpq
    rcases mem_insert.mp ht with rfl | ht
    · exact hsavoid c hc htc (hj _ hcpq)
    · exact havoid t ht c hc htc (hi _ hcpq)

theorem binaryTreeImage_complement_open {T : V} (hT : IsTree T) :
    IsRealOpen ((dedekindReals V) \ binaryImage (treeBody T)) := by
  apply realOpen_of_neighborhoods
  intro x hx
  obtain ⟨hxR, hxI⟩ := mem_sdiff_iff.mp hx
  have hxCut := (mem_dedekindReals_iff _).mp hxR
  have hS : binaryExcludedPrefixes x ⊆ binarySequences V :=
    fun s hs ↦ ((mem_binaryExcludedPrefixes_iff _ _).mp hs).1
  obtain ⟨F, hFS, hF, hcover⟩ := treeBody_finite_subcover hT hS (binaryExcludedPrefixes_cover hxCut hxI)
  obtain ⟨a, ha, b, hb, hxi, havoid⟩ := binaryExcludedPrefixes_finite_neighborhood hxCut hF hFS
  refine ⟨a, ha, b, hb, realInterval_order ha hb hxi, hxi, ?_⟩
  intro z hzi
  refine mem_sdiff_iff.mpr ⟨realInterval_subset_reals _ _ z hzi, ?_⟩
  intro hzI
  obtain ⟨c, hc, rfl⟩ := (mem_binaryImage_iff _ _).mp hzI
  obtain ⟨hcC, s, hs, hsc⟩ := (mem_openFrom_iff _ _).mp (hcover c hc)
  exact havoid s hs c hcC ((subset_iff_restrict_eq hcC (hS s (hFS s hs))).mpr hsc) hzi

theorem binaryTreeImage_closed {T : V} (hT : IsTree T) :
    ∃ S, S ⊆ realBasicCodes V ∧ binaryImage (treeBody T) = realClosedFrom S := by
  obtain ⟨S, hS, he⟩ := binaryTreeImage_complement_open hT
  refine ⟨S, hS, ?_⟩
  apply mem_ext
  intro x
  rw [mem_realClosedFrom_iff, ← he, mem_sdiff_iff]
  have hIR := binaryImage_subset_reals (treeBody_subset_cantorSpace T)
  constructor
  · intro hx
    exact ⟨(mem_dedekindReals_iff _).mp (hIR x hx), fun h ↦ h.2 hx⟩
  · rintro ⟨hxCut, h⟩
    by_contra hx
    exact h ⟨(mem_dedekindReals_iff _).mpr hxCut, hx⟩

end ZFVP
