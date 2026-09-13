import ZFVP.ModelTheory.ForcingNameNormalizationTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingRankNameFormula : SetTheorySemisentence 4 :=
  f“n P R t. !(formulaUniqueNameFormula sigmaOneRankFormula) n P R
    (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) t)”

def forcingCheckedValueBoundFormula : SetTheorySemisentence 6 :=
  f“b P R o d t. ∃ S, (∀ a, a ∈ S ↔ a ∈ d ∧ ∃ p ∈ P,
    p ∈ !atomicEqualityFormula P R t (!checkNameFormula o a)) ∧ b = !succ.dfn (!sUnion.dfn S)”

def forcingCanonicalNameFormula : SetTheorySemisentence 6 :=
  f“n P R o d t. ∀ r b U, !forcingRankNameFormula r P R t →
    !forcingCheckedValueBoundFormula b P R o d r →
    !(parameterRecursionFormula forcingNameHierarchyStepFormula) U P b →
    !forcingSaturatedNameFormula n P R U t”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingRankNameFormula_defined :
    ℒₛₑₜ-function₃[V] forcingRankName via forcingRankNameFormula :=
  ⟨fun v ↦ by simp [forcingRankNameFormula, forcingRankName, standardTuple]⟩

instance forcingRankName_definable : ℒₛₑₜ-function₃[V] forcingRankName :=
  forcingRankNameFormula_defined.to_definable

noncomputable def forcingCheckedValueBound (P R one δ τ : V) : V :=
  succ (⋃ˢ {α ∈ δ ; ∃ p ∈ P, p ∈ atomicEquality P R τ (checkName one α)})

instance forcingCheckedValueBoundFormula_defined :
    ℒₛₑₜ-function₅[V] forcingCheckedValueBound via forcingCheckedValueBoundFormula :=
  ⟨fun v ↦ by
    simp [forcingCheckedValueBoundFormula, forcingCheckedValueBound]
    constructor
    · rintro ⟨S, hS, he⟩
      have hS' : S = {α ∈ v 4 ; ∃ p ∈ v 1, p ∈ atomicEquality (v 1) (v 2) (v 5) (checkName (v 3) α)} := by
        apply mem_ext
        intro a
        simpa only [mem_sep_iff] using hS a
      exact hS' ▸ he
    · intro he
      exact ⟨_, fun a ↦ mem_sep_iff, he⟩⟩

instance forcingCheckedValueBound_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingCheckedValueBound (V := V)) :=
  forcingCheckedValueBoundFormula_defined.to_definable

theorem forcingCheckedValueBound_spec {P R one δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (τ : V) :
    forcingCheckedValueBound P R one δ τ ∈ δ ∧
      ∀ p ∈ P, ∀ α ∈ δ, p ∈ atomicEquality P R τ (checkName one α) →
        α ∈ forcingCheckedValueBound P R one δ τ := by
  let := hδ.1
  let S := {α ∈ δ ; ∃ p ∈ P, p ∈ atomicEquality P R τ (checkName one α)}
  have hSord : ∀ α ∈ S, IsOrdinal α := fun _ ha ↦ IsOrdinal.of_mem (mem_sep_iff.mp ha).1
  let := IsOrdinal.sUnion hSord
  obtain ⟨β, hβ, hb⟩ := small_forcing_checked_name_values_bounded hR ht hδ hP τ
  let := IsOrdinal.of_mem hβ
  have hsub : ⋃ˢ S ⊆ β := by
    intro a ha
    obtain ⟨α, hα, haα⟩ := mem_sUnion_iff.mp ha
    obtain ⟨hαδ, p, hp, he⟩ := mem_sep_iff.mp hα
    exact IsOrdinal.toIsTransitive.mem_trans haα (hb p hp α hαδ he)
  refine ⟨regularCardinal_succ_closed hδ.regular (ordinal_mem_of_subset_mem hsub hβ), ?_⟩
  intro p hp α hα he
  let := IsOrdinal.of_mem hα
  change α ∈ succ (⋃ˢ S)
  exact ordinal_mem_of_subset_mem (subset_sUnion_of_mem (mem_sep_iff.mpr ⟨hα, p, hp, he⟩))
    (show ⋃ˢ S ∈ succ (⋃ˢ S) by simp)

/-- A definable normalization, with its cutoff computed from all possible
checked values of the rank name. No choice of a representative is needed. -/
noncomputable def forcingCanonicalName (P R one δ τ : V) : V :=
  forcingSaturatedName P R
    (forcingNameHierarchy P (forcingCheckedValueBound P R one δ (forcingRankName P R τ))) τ

private theorem forall_six_eq {T : Type*} (a b c d e f : T) (F : T → T → T → T → T → T → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔
      F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

instance forcingCanonicalNameFormula_defined :
    ℒₛₑₜ-function₅[V] forcingCanonicalName via forcingCanonicalNameFormula :=
  ⟨fun v ↦ by
    simp [forcingCanonicalNameFormula, forcingCanonicalName]
    simp [Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq]
    constructor
    · intro h
      exact h _ _ _ rfl rfl rfl
    · rintro h x y z rfl rfl rfl
      exact h⟩

instance forcingCanonicalName_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingCanonicalName (V := V)) :=
  forcingCanonicalNameFormula_defined.to_definable

theorem forcingCanonicalName_isName (P R one δ τ : V) :
    IsForcingName P (forcingCanonicalName P R one δ τ) := forcingSaturatedName_isName _ _ _ _

theorem forcingCanonicalName_empty {P R : V} (hR : IsForcingPreorder P R) (one δ : V) :
    forcingCanonicalName P R one δ ∅ = ∅ := by
  apply mem_ext
  intro z
  simp [forcingCanonicalName, forcingSaturatedName, atomicMembership_empty hR]

theorem forcingCanonicalName_mem {P R one δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (τ : V) :
    forcingCanonicalName P R one δ τ ∈ forcingNameHierarchy P δ := by
  let := hδ.1
  exact (mem_forcingNameHierarchy _ _ _).mpr
    ⟨_, (forcingCheckedValueBound_spec hR ht hδ hP _).1, forcingSaturatedName_subset _ _ _ _⟩

namespace ForcingContext

theorem canonicalName_value (A : ForcingContext V) {δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ)
    (τ : ForcingName A.P) (hτ : A.ofName τ ∈ hierarchy (A.check δ)) :
    A.ofName ⟨forcingCanonicalName A.P A.R A.one δ τ.val, forcingCanonicalName_isName _ _ _ _ _⟩ =
      A.ofName τ := by
  let := hδ.1
  let β := forcingCheckedValueBound A.P A.R A.one δ (forcingRankName A.P A.R τ.val)
  have hb := forcingCheckedValueBound_spec A.order A.top hδ hP (forcingRankName A.P A.R τ.val)
  let := IsOrdinal.of_mem hb.1
  have hr : rank (A.ofName τ) ∈ A.check β := by
    rw [← A.forcingRankName_value τ]
    apply A.checked_name_value_bounded (δ := δ)
      ⟨forcingRankName A.P A.R τ.val, forcingRankName_isName _ _ _⟩ hb.2
    rw [A.forcingRankName_value τ]
    exact (mem_hierarchy_iff_rank_mem _ _).mp hτ
  apply A.saturatedName_value_of_hierarchy β τ
  exact subset_trans (subset_hierarchy_rank _) (hierarchy_mono
    (IsOrdinal.toIsTransitive.transitive _ hr))

end ForcingContext
end ZFVP
