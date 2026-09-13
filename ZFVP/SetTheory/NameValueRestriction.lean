import ZFVP.SetTheory.NameActionClosure
import ZFVP.SetTheory.NameValue
import ZFVP.SetTheory.NameAction

/-! The value of a name reads only the conditions that occur in the name. `nameConditionsClosure τ`
collects the second coordinates of all pairs occurring in the iterated subnames of `τ`, and two
filters that agree on that set give `τ` the same value. In particular cutting the filter down by
any set containing the conditions of `τ` does not change the value, which is the form the
Karagila-Schilhan Lemma 9.3 argument uses for names over a subalgebra. The last group of lemmas
transports the condition set along the action of a map on names. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The conditions occurring in a name -/

/-- `p` occurs as a condition in `τ` when some pair with second coordinate `p` lies in an
iterated subname of `τ`. -/
def OccursInName (τ p : V) : Prop := ∃ υ ∈ nameClosure τ, ∃ σ : V, ⟨σ, p⟩ₖ ∈ υ

instance occursInName_definable : ℒₛₑₜ-relation[V] OccursInName := by
  unfold OccursInName
  definability

theorem occursInName_of_mem {τ σ p : V} (h : ⟨σ, p⟩ₖ ∈ τ) : OccursInName τ p :=
  ⟨τ, mem_nameClosure_self τ, σ, h⟩

theorem occursInName_mono {τ υ : V} (hυ : υ ∈ nameClosure τ) {p : V}
    (h : OccursInName υ p) : OccursInName τ p := by
  obtain ⟨ρ, hρ, σ, hσ⟩ := h
  exact ⟨ρ, nameClosure_mem_mono hυ ρ hρ, σ, hσ⟩

theorem occursInName_sUnion {τ p : V} (h : OccursInName τ p) :
    p ∈ ⋃ˢ (⋃ˢ (⋃ˢ (nameClosure τ))) := by
  obtain ⟨υ, hυ, σ, hσ⟩ := h
  refine mem_sUnion_iff.mpr ⟨({σ, p} : V), mem_sUnion_iff.mpr ⟨(⟨σ, p⟩ₖ : V),
    mem_sUnion_iff.mpr ⟨υ, hυ, hσ⟩, ?_⟩, by simp⟩
  simp [kpair]

/-- The set of conditions occurring in `τ`. -/
noncomputable def nameConditionsClosure (τ : V) : V :=
  {p ∈ ⋃ˢ (⋃ˢ (⋃ˢ (nameClosure τ))) ; OccursInName τ p}

theorem mem_nameConditionsClosure_iff (τ p : V) :
    p ∈ nameConditionsClosure τ ↔ ∃ υ ∈ nameClosure τ, ∃ σ : V, ⟨σ, p⟩ₖ ∈ υ := by
  rw [nameConditionsClosure, mem_sep_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨occursInName_sUnion h, h⟩⟩

instance nameConditionsClosure_definable : ℒₛₑₜ-function₁[V] nameConditionsClosure := by
  have h : ℒₛₑₜ-relation[V] (fun C τ ↦ ∀ p, p ∈ C ↔
      ∃ υ ∈ nameClosure τ, ∃ σ : V, ⟨σ, p⟩ₖ ∈ υ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = nameConditionsClosure (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_nameConditionsClosure_iff]

theorem mem_nameConditionsClosure_of_mem {τ σ p : V} (h : ⟨σ, p⟩ₖ ∈ τ) :
    p ∈ nameConditionsClosure τ :=
  (mem_nameConditionsClosure_iff τ p).mpr ⟨τ, mem_nameClosure_self τ, σ, h⟩

theorem nameConditionsClosure_mono {τ υ : V} (hυ : υ ∈ nameClosure τ) :
    nameConditionsClosure υ ⊆ nameConditionsClosure τ := by
  intro p hp
  exact (mem_nameConditionsClosure_iff τ p).mpr
    (occursInName_mono hυ ((mem_nameConditionsClosure_iff υ p).mp hp))

/-- The conditions of a name over `P` all lie in `P`. -/
theorem nameConditionsClosure_subset_of_isForcingName {P τ : V} (hτ : IsForcingName P τ) :
    nameConditionsClosure τ ⊆ P := by
  intro p hp
  obtain ⟨υ, hυ, σ, hσ⟩ := (mem_nameConditionsClosure_iff τ p).mp hp
  obtain ⟨ν, q, hq, he⟩ := hτ υ hυ _ hσ
  exact (kpair_iff.mp he).2 ▸ hq

/-! ### The value depends only on the conditions of the name -/

/-- Two filters that agree on every condition occurring in `τ` give `τ` the same value. -/
theorem nameValue_congr_of_agree {G H τ : V}
    (h : ∀ p : V, OccursInName τ p → (p ∈ G ↔ p ∈ H)) :
    nameValue G τ = nameValue H τ := by
  have key := projectedRank_induction (nameClosure τ) (fun x : V ↦ x) (by definability)
    (fun υ : V ↦ nameValue G υ = nameValue H υ) (by definability) ?_
  · exact key τ (mem_nameClosure_self τ)
  · intro υ hυ ih
    apply SetTheory.mem_ext_iff.mpr
    intro z
    rw [mem_nameValue_iff, mem_nameValue_iff]
    have hstep (σ p : V) (hσp : ⟨σ, p⟩ₖ ∈ υ) :
        σ ∈ nameClosure τ ∧ nameValue G σ = nameValue H σ ∧ (p ∈ G ↔ p ∈ H) := by
      have hσ : σ ∈ nameClosure τ :=
        nameClosure_closed τ υ hυ σ (mem_domain_of_kpair_mem hσp)
      exact ⟨hσ, ih σ hσ (rank_subname_lt hσp), h p ⟨υ, hυ, σ, hσp⟩⟩
    constructor
    · rintro ⟨σ, p, hp, hσp, rfl⟩
      obtain ⟨_, hv, hG⟩ := hstep σ p hσp
      exact ⟨σ, p, hG.mp hp, hσp, hv⟩
    · rintro ⟨σ, p, hp, hσp, rfl⟩
      obtain ⟨_, hv, hG⟩ := hstep σ p hσp
      exact ⟨σ, p, hG.mpr hp, hσp, hv.symm⟩

/-- Cutting the filter by a set containing every condition of `τ` does not change the value. -/
theorem nameValue_inter_of_conditions {G D τ : V}
    (h : ∀ p : V, OccursInName τ p → p ∈ D) :
    nameValue (G ∩ D) τ = nameValue G τ := by
  apply nameValue_congr_of_agree
  intro p hp
  rw [mem_inter_iff]
  exact ⟨fun hq ↦ hq.1, fun hq ↦ ⟨hq, h p hp⟩⟩

theorem nameValue_inter_of_conditionsClosure {G D τ : V} (h : nameConditionsClosure τ ⊆ D) :
    nameValue (G ∩ D) τ = nameValue G τ :=
  nameValue_inter_of_conditions
    (fun p hp ↦ h p ((mem_nameConditionsClosure_iff τ p).mpr hp))

/-- The form Lemma 9.3 uses: a name whose conditions all lie in `D` is evaluated from `G ∩ D`. -/
theorem nameValue_eq_of_subalgebra {G D τ : V} (h : nameConditionsClosure τ ⊆ D) :
    nameValue (G ∩ D) τ = nameValue G τ :=
  nameValue_inter_of_conditionsClosure h

/-- `nameValue_inter_of_name` recovered from the condition set. -/
theorem nameValue_inter_of_conditions_of_isForcingName {G C τ : V} (hτ : IsForcingName C τ) :
    nameValue (G ∩ C) τ = nameValue G τ :=
  nameValue_inter_of_conditionsClosure (nameConditionsClosure_subset_of_isForcingName hτ)

/-! ### Transport along the action of a map on names -/

theorem mem_nameClosure_nameAction_iff {P π τ : V} (hτ : IsForcingName P τ) (ρ : V) :
    ρ ∈ nameClosure (nameAction π τ) ↔ ∃ υ ∈ nameClosure τ, ρ = nameAction π υ := by
  rw [nameClosure_nameAction hτ π]
  exact repl_spec (by definability)

/-- The conditions of `nameAction π τ` are the `π`-images of the conditions of `τ`. -/
theorem mem_nameConditionsClosure_nameAction_iff {P π τ : V} (hτ : IsForcingName P τ) (q : V) :
    q ∈ nameConditionsClosure (nameAction π τ) ↔
      ∃ p ∈ nameConditionsClosure τ, q = π ‘ p := by
  rw [mem_nameConditionsClosure_iff]
  constructor
  · rintro ⟨ν, hν, σ', hσ'⟩
    obtain ⟨υ, hυ, rfl⟩ := (mem_nameClosure_nameAction_iff hτ ν).mp hν
    obtain ⟨σ, p, hσp, he⟩ :=
      (mem_nameAction_iff (forcingName_mem_closure hτ hυ) π _).mp hσ'
    exact ⟨p, (mem_nameConditionsClosure_iff τ p).mpr ⟨υ, hυ, σ, hσp⟩, (kpair_iff.mp he).2⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨υ, hυ, σ, hσp⟩ := (mem_nameConditionsClosure_iff τ p).mp hp
    exact ⟨nameAction π υ, (mem_nameClosure_nameAction_iff hτ _).mpr ⟨υ, hυ, rfl⟩, nameAction π σ,
      (mem_nameAction_iff (forcingName_mem_closure hτ hυ) π _).mpr ⟨σ, p, hσp, rfl⟩⟩

end ZFVP
