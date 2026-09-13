import ZFVP.ModelTheory.SchmerlFiniteUpperBounds
import ZFVP.SetTheory.InverseFunction

/-! Actual finite demands and cofinality on finitely many distinct coordinates.
The index set and its finite demands are internal sets; only the displayed
list of coordinates has a standard finite length. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem mem_range_standardTuple_iff {p : ℕ} (v : Fin p → V) (x : V) :
    x ∈ range (standardTuple v) ↔ ∃ t, x = v t := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := mem_range_iff.mp hx
    obtain ⟨t, ht⟩ := (mem_standardTuple_iff v _).mp ha
    exact ⟨t, (kpair_iff.mp ht).2⟩
  · rintro ⟨t, rfl⟩
    exact mem_range_of_kpair_mem ((mem_standardTuple_iff v _).mpr ⟨t, rfl⟩)

private theorem internallyFinite_range_standardTuple {p : ℕ} (v : Fin p → V) :
    IsInternallyFinite (range (standardTuple v)) := by
  apply internallyFinite_range
  apply internallyFinite_function
  rw [domain_standardTuple]
  exact ⟨(p : V), by simp, CardEQ.refl _⟩

/-- Replace distinct, standard finitely many values of an actual internal
function. The result is itself an internal function on the entire index set. -/
theorem exists_internal_finiteCoordinateUpdate {I D d : V} {p : ℕ}
    (hd : d ∈ D ^ I) (indices : Fin p → V) (hi : ∀ t, indices t ∈ I)
    (hinj : Function.Injective indices) (s : Fin p → V) (hs : ∀ t, s t ∈ D) :
    ∃ c ∈ D ^ I, (∀ t, c ‘ (indices t) = s t) ∧
      ∀ i ∈ I, (∀ t, i ≠ indices t) → c ‘ i = d ‘ i := by
  classical
  let e := standardTuple indices
  have he : e ∈ I ^ (p : V) := standardTuple_mem_function indices hi
  have hei : Injective e := by
    intro x y z hx hy
    obtain ⟨t, ht⟩ := (mem_standardTuple_iff indices _).mp hx
    obtain ⟨u, hu⟩ := (mem_standardTuple_iff indices _).mp hy
    obtain ⟨rfl, htz⟩ := kpair_iff.mp ht
    obtain ⟨rfl, huz⟩ := kpair_iff.mp hu
    exact congrArg (fun t : Fin p ↦ (t.val : V)) (hinj (htz.symm.trans huz))
  have heinv := converseGraph_mem_function he hei
  have hst : standardTuple s ∈ D ^ (p : V) := standardTuple_mem_function s hs
  let b := compose (converseGraph e) (standardTuple s)
  have hb : b ∈ D ^ range e := compose_function heinv hst
  have hiv (t : Fin p) : indices t ∈ range e :=
    (mem_range_standardTuple_iff indices _).mpr ⟨t, rfl⟩
  have hbv (t : Fin p) : b ‘ (indices t) = s t := by
    rw [value_compose_of_mem_function heinv hst (hiv t)]
    have hval : e ‘ (t.val : V) = indices t := value_standardTuple indices t
    rw [← hval, converseGraph_value_value he hei (natCast_mem_of_lt t.isLt)]
    exact value_standardTuple s t
  let F : V → V := fun i ↦ if i ∈ range e then b ‘ i else d ‘ i
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation[V] (fun y i ↦
        (i ∈ range e ∧ y = b ‘ i) ∨ (i ∉ range e ∧ y = d ‘ i)) := by definability
    apply Language.Definable.of_iff h
    intro v
    change v 0 = F (v 1) ↔ _
    dsimp only [F]
    split <;> simp_all
  let c := definableGraph I F hF
  have hc : c ∈ D ^ I := definableGraph_mem_function_of_mapsTo _ _ _ _ (by
    intro i hiI
    dsimp only [F]
    split
    · exact function_value_mem hb ‹i ∈ range e›
    · exact function_value_mem hd hiI)
  refine ⟨c, hc, ?_, ?_⟩
  · intro t
    rw [value_definableGraph _ _ _ (hi t)]
    simp only [F, hiv t, ite_true, hbv t]
  · intro i hiI hnot
    rw [value_definableGraph _ _ _ hiI]
    have hne : i ∉ range e := by
      intro hh
      obtain ⟨t, ht⟩ := (mem_range_standardTuple_iff indices _).mp hh
      exact hnot t ht
    simp only [F, hne, ite_false]

/-- Meeting every actual finite collection of nonstrict lower-bound demands
is equivalent to strict product cofinality on a fixed finite coordinate list. -/
theorem finiteCoordinate_cofinal_iff (hAC : InternalChoice V) {I D P R E : V} {p : ℕ}
    (hP : P ∈ power D ^ I)
    (hpos : ∀ i ∈ I, IsForcingPoset (P ‘ i) (R ‘ i))
    (hdir : ∀ i ∈ I, IsInternalDirectedNoMax (P ‘ i) (R ‘ i))
    (indices : Fin p → V) (hi : ∀ t, indices t ∈ I) (hinj : Function.Injective indices)
    (B : (Fin p → BinaryRelationDomain D E) → Prop) :
    (∀ H, IsInternallyFinite H → H ⊆ I ×ˢ D →
      (∀ i x, ⟨i, x⟩ₖ ∈ H → x ∈ P ‘ i) →
      ∃ (c : V) (hc : c ∈ D ^ I), (∀ i ∈ I, c ‘ i ∈ P ‘ i) ∧
        (∀ i x, ⟨i, x⟩ₖ ∈ H → ⟨x, c ‘ i⟩ₖ ∈ R ‘ i) ∧
        B (fun t ↦ ⟨c ‘ (indices t), function_value_mem hc (hi t)⟩)) ↔
    (∀ r : Fin p → BinaryRelationDomain D E, (∀ t, (r t).val ∈ P ‘ (indices t)) →
      ∃ s : Fin p → BinaryRelationDomain D E, (∀ t, (s t).val ∈ P ‘ (indices t)) ∧
        (∀ t, ⟨(r t).val, (s t).val⟩ₖ ∈ R ‘ (indices t) ∧ (r t).val ≠ (s t).val) ∧ B s) := by
  classical
  have hPD (i : V) (hiI : i ∈ I) : P ‘ i ⊆ D := mem_power_iff.mp (function_value_mem hP hiI)
  constructor
  · intro h r hr
    have hnext : ∀ t, ∃ y ∈ P ‘ (indices t),
        ⟨(r t).val, y⟩ₖ ∈ R ‘ (indices t) ∧ (r t).val ≠ y :=
      fun t ↦ (hdir _ (hi t)).strict_upper (hr t)
    choose y hy hxy using hnext
    let v : Fin p → V := fun t ↦ ⟨indices t, y t⟩ₖ
    let H := range (standardTuple v)
    have hH : IsInternallyFinite H := internallyFinite_range_standardTuple v
    have hsub : H ⊆ I ×ˢ D := by
      intro z hz
      obtain ⟨t, rfl⟩ := (mem_range_standardTuple_iff v _).mp hz
      exact kpair_mem_iff.mpr ⟨hi t, hPD _ (hi t) _ (hy t)⟩
    have hvalid : ∀ i x, ⟨i, x⟩ₖ ∈ H → x ∈ P ‘ i := by
      intro i x hx
      obtain ⟨t, ht⟩ := (mem_range_standardTuple_iff v _).mp hx
      obtain ⟨rfl, rfl⟩ := kpair_iff.mp ht
      exact hy t
    obtain ⟨c, hc, hcp, hbound, hB⟩ := h H hH hsub hvalid
    refine ⟨fun t ↦ ⟨c ‘ (indices t), function_value_mem hc (hi t)⟩,
      fun t ↦ hcp _ (hi t), ?_, hB⟩
    intro t
    have hyc : ⟨y t, c ‘ (indices t)⟩ₖ ∈ R ‘ (indices t) :=
      hbound _ _ ((mem_range_standardTuple_iff v _).mpr ⟨t, rfl⟩)
    have hp := hpos _ (hi t)
    refine ⟨hp.1.2.2 _ (hr t) _ (hy t) _ (hcp _ (hi t)) (hxy t).1 hyc, ?_⟩
    intro heq
    exact (hxy t).2 (hp.2 _ (hr t) _ (hy t) (hxy t).1 (heq ▸ hyc))
  · intro h H hH hsub hvalid
    obtain ⟨d, hd, hdp, hdb⟩ := exists_finite_strict_upper_choice hAC hP hpos hdir hH hsub hvalid
    let r : Fin p → BinaryRelationDomain D E :=
      fun t ↦ ⟨d ‘ (indices t), function_value_mem hd (hi t)⟩
    obtain ⟨s, hsp, hrs, hB⟩ := h r (fun t ↦ hdp _ (hi t))
    obtain ⟨c, hc, hcs, hcd⟩ := exists_internal_finiteCoordinateUpdate hd indices hi hinj
      (fun t ↦ (s t).val) (fun t ↦ (s t).property)
    have hcp : ∀ i ∈ I, c ‘ i ∈ P ‘ i := by
      intro i hiI
      by_cases he : ∃ t, i = indices t
      · obtain ⟨t, rfl⟩ := he
        rw [hcs t]
        exact hsp t
      · rw [hcd i hiI (by simpa using he)]
        exact hdp i hiI
    refine ⟨c, hc, hcp, ?_, ?_⟩
    · intro i x hx
      have hiI := (kpair_mem_iff.mp (hsub _ hx)).1
      by_cases he : ∃ t, i = indices t
      · obtain ⟨t, rfl⟩ := he
        rw [hcs t]
        exact (hpos _ (hi t)).1.2.2 _ (hvalid _ _ hx) _ (hdp _ (hi t)) _ (hsp t)
          (hdb _ _ hx).1 (hrs t).1
      · rw [hcd i hiI (by simpa using he)]
        exact (hdb _ _ hx).1
    · have he : (fun t ↦ (⟨c ‘ (indices t), function_value_mem hc (hi t)⟩ :
          BinaryRelationDomain D E)) = s := by
        funext t
        exact Subtype.ext (hcs t)
      rwa [he]

end ZFVP.Schmerl
