import ZFVP.SetTheory.UltrapowerCollapse

/-! The canonical map of the internal ultrapower, as an internal set function.

The ultrapower of a transitive set `A` by an ultrafilter `U` on `P` lives on
`ultraTarget P U A`, the range of the collapse map of the a.e. membership relation. The canonical
map sends `x ∈ A` to the collapse of the constant function at `x`. This file builds that map as an
internal function graph and proves what does not need Los's theorem: it is a function from `A` into
the target, it is injective, and it preserves and reflects membership. Elementarity comes later. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The value of the canonical map at `x`: the collapse of the constant function at `x`. -/
noncomputable def ultraConstantValue (P U A x : V) : V :=
  (ultraCollapse P U A) ‘ (constantGraph P x)

instance ultraConstantValue_definable : ℒₛₑₜ-function₄[V] ultraConstantValue := by
  have h : ℒₛₑₜ-relation₅ (fun y P U A x : V ↦
      ∃ c, c = constantGraph P x ∧ ∃ m, m = ultraCollapse P U A ∧ y = m ‘ c) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = ultraConstantValue (v 1) (v 2) (v 3) (v 4) ↔ _
  unfold ultraConstantValue
  constructor
  · intro hy
    exact ⟨_, rfl, _, rfl, hy⟩
  · rintro ⟨c, hc, m, hm, hy⟩
    rw [hy, hc, hm]

/-- Definability in the last argument alone, which is what the graph construction needs. -/
theorem ultraConstantValue_definable_one (P U A : V) :
    ℒₛₑₜ-function₁[V] (ultraConstantValue P U A) := by
  have h : ℒₛₑₜ-relation[V] (fun y x : V ↦
      ∃ c, c = constantGraph P x ∧ ∃ m, m = ultraCollapse P U A ∧ y = m ‘ c) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = ultraConstantValue P U A (v 1) ↔ _
  unfold ultraConstantValue
  constructor
  · intro hy
    exact ⟨_, rfl, _, rfl, hy⟩
  · rintro ⟨c, hc, m, hm, hy⟩
    rw [hy, hc, hm]

/-- The canonical map of the ultrapower: `x` goes to the collapse of the constant function at
`x`. -/
noncomputable def ultraEmbedding (P U A : V) : V :=
  definableGraph A (ultraConstantValue P U A) (ultraConstantValue_definable_one P U A)

instance ultraEmbedding_definable : ℒₛₑₜ-function₃[V] ultraEmbedding := by
  have h : ℒₛₑₜ-relation₄ (fun B P U A : V ↦ ∀ q, q ∈ B ↔
      ∃ x ∈ A, q = ⟨x, ultraConstantValue P U A x⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = ultraEmbedding (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [ultraEmbedding, mem_definableGraph_iff]

instance ultraEmbedding_isFunction (P U A : V) : IsFunction (ultraEmbedding P U A) :=
  definableGraph_isFunction _ _ _

@[simp] theorem domain_ultraEmbedding (P U A : V) : domain (ultraEmbedding P U A) = A :=
  domain_definableGraph _ _ _

theorem value_ultraEmbedding {P U A x : V} (hx : x ∈ A) :
    (ultraEmbedding P U A) ‘ x = (ultraCollapse P U A) ‘ (constantGraph P x) :=
  value_definableGraph A (ultraConstantValue P U A) (ultraConstantValue_definable_one P U A) hx

/-- The canonical map is a function from `A` into the ultrapower target. -/
theorem ultraEmbedding_mem_function {P U A : V}
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P)) :
    ultraEmbedding P U A ∈ (ultraTarget P U A) ^ A := by
  apply definableGraph_mem_function_of_mapsTo
  intro x hx
  exact ultraCollapse_value_mem hwf (constantGraph_mem_ultraFunctions hx)

/-- The canonical map separates points. -/
theorem ultraEmbedding_value_eq_iff (hAC : InternalChoice V) {P U A κ : V} [IsOrdinal κ]
    [IsTransitive A] (hU : IsSetUltrafilter P U) (hcomp : IsOrdinalCompleteOn P κ U)
    (hω : (ω : V) ∈ κ) (hA : IsNonempty A) {x y : V} (hx : x ∈ A) (hy : y ∈ A) :
    (ultraEmbedding P U A) ‘ x = (ultraEmbedding P U A) ‘ y ↔ x = y := by
  rw [value_ultraEmbedding hx, value_ultraEmbedding hy,
    ultraCollapse_eq_iff hAC hU hcomp hω hA (constantGraph_mem_ultraFunctions hx)
      (constantGraph_mem_ultraFunctions hy),
    ultraEq_constantGraph_iff hU]

/-- The canonical map preserves and reflects membership. -/
theorem ultraEmbedding_value_mem_iff (hAC : InternalChoice V) {P U A κ : V} [IsOrdinal κ]
    [IsTransitive A] (hU : IsSetUltrafilter P U) (hcomp : IsOrdinalCompleteOn P κ U)
    (hω : (ω : V) ∈ κ) (hA : IsNonempty A) {x y : V} (hx : x ∈ A) (hy : y ∈ A) :
    (ultraEmbedding P U A) ‘ x ∈ (ultraEmbedding P U A) ‘ y ↔ x ∈ y := by
  rw [value_ultraEmbedding hx, value_ultraEmbedding hy,
    ultraCollapse_mem_iff hAC hU hcomp hω hA (constantGraph_mem_ultraFunctions hx)
      (constantGraph_mem_ultraFunctions hy),
    ultraMem_constantGraph_iff hU]

theorem ultraEmbedding_injective (hAC : InternalChoice V) {P U A κ : V} [IsOrdinal κ]
    [IsTransitive A] (hU : IsSetUltrafilter P U) (hcomp : IsOrdinalCompleteOn P κ U)
    (hω : (ω : V) ∈ κ) (hA : IsNonempty A) : Injective (ultraEmbedding P U A) := by
  intro x₁ x₂ y h₁ h₂
  have hx₁ : x₁ ∈ A := by
    have := mem_domain_of_kpair_mem h₁
    rwa [domain_ultraEmbedding] at this
  have hx₂ : x₂ ∈ A := by
    have := mem_domain_of_kpair_mem h₂
    rwa [domain_ultraEmbedding] at this
  have hv : (ultraEmbedding P U A) ‘ x₁ = (ultraEmbedding P U A) ‘ x₂ := by
    rw [value_eq_of_kpair_mem h₁, value_eq_of_kpair_mem h₂]
  exact (ultraEmbedding_value_eq_iff hAC (κ := κ) hU hcomp hω hA hx₁ hx₂).mp hv

end ZFVP
