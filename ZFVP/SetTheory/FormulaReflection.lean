import ZFVP.SetTheory.WitnessClosure
import ZFVP.SetTheory.FiniteCodingClosure
import ZFVP.SetTheory.Relativization
import ZFVP.Syntax.StandardTuples

/-! Reflection for externally finite families of set-theory formulas.
The witness relation is constructed separately for each formula. This does not
define a truth predicate for arbitrary internal formula codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def mergeWitnessRelations (R S : V → V → Prop) (p y : V) : Prop :=
  (kpair.π₁ p = 0 ∧ R (kpair.π₂ p) y) ∨ (kpair.π₁ p = 1 ∧ S (kpair.π₂ p) y)

theorem mergeWitnessRelations_definable (R S : V → V → Prop)
    (hR : ℒₛₑₜ-relation R) (hS : ℒₛₑₜ-relation S) : ℒₛₑₜ-relation (mergeWitnessRelations R S) := by
  unfold mergeWitnessRelations
  definability

theorem mergeWitnessClosed {R S : V → V → Prop} {δ : V} [IsOrdinal δ]
    (hω : (ω : V) ∈ δ) (hlim : ∀ ξ ∈ δ, succ ξ ∈ δ)
    (hc : IsWitnessClosed (mergeWitnessRelations R S) δ) : IsWitnessClosed R δ ∧ IsWitnessClosed S δ := by
  have hn (n : ℕ) : (n : V) ∈ hierarchy δ :=
    ordinal_subset_hierarchy δ _ (IsOrdinal.toIsTransitive.mem_trans (show (n : V) ∈ ω by simp) hω)
  constructor
  · intro x hx hex
    have hp := kpair_mem_hierarchy_limit hlim (hn 0) hx
    obtain ⟨y, hy, hRy⟩ := hc ⟨0, x⟩ₖ hp (by
      obtain ⟨y, hy⟩ := hex
      exact ⟨y, Or.inl ⟨by simp, by simpa using hy⟩⟩)
    refine ⟨y, hy, ?_⟩
    simpa [mergeWitnessRelations] using hRy
  · intro x hx hex
    have hp := kpair_mem_hierarchy_limit hlim (hn 1) hx
    obtain ⟨y, hy, hSy⟩ := hc ⟨1, x⟩ₖ hp (by
      obtain ⟨y, hy⟩ := hex
      exact ⟨y, Or.inr ⟨by simp, by simpa using hy⟩⟩)
    refine ⟨y, hy, ?_⟩
    simpa [mergeWitnessRelations] using hSy

def formulaWitnessRelation {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (s y : V) : Prop :=
  φ.Evalb (y :> fun i : Fin n ↦ s ‘ (i.val : V))

theorem formulaWitnessRelation_definable {n : ℕ} (φ : SetTheorySemisentence (n + 1)) :
    ℒₛₑₜ-relation[V] (formulaWitnessRelation φ) := by
  have hφ : Language.Definable ℒₛₑₜ (fun v : Fin (n + 1) → V ↦ φ.Evalb v) :=
    (show Defined (fun v : Fin (n + 1) → V ↦ φ.Evalb v) φ from ⟨fun _ ↦ Iff.rfl⟩).to_definable
  unfold formulaWitnessRelation
  apply Language.Definable.substitution hφ (f := fun i v ↦
    (v 1 :> fun j : Fin n ↦ (v 0) ‘ (j.val : V)) i)
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change Language.DefinableFunction ℒₛₑₜ (fun v : Fin 2 → V ↦ v 1)
    definability
  · change Language.DefinableFunction ℒₛₑₜ (fun v : Fin 2 → V ↦ (v 0) ‘ (j.val : V))
    definability

def reflectionWitnessRelation : {n : ℕ} → SetTheorySemisentence n → V → V → Prop
  | _, .verum => fun _ _ ↦ False
  | _, .falsum => fun _ _ ↦ False
  | _, .rel _ _ => fun _ _ ↦ False
  | _, .nrel _ _ => fun _ _ ↦ False
  | _, .and φ ψ => mergeWitnessRelations (reflectionWitnessRelation φ) (reflectionWitnessRelation ψ)
  | _, .or φ ψ => mergeWitnessRelations (reflectionWitnessRelation φ) (reflectionWitnessRelation ψ)
  | _, .all φ => mergeWitnessRelations (reflectionWitnessRelation φ) (fun s y ↦ ¬formulaWitnessRelation φ s y)
  | _, .exs φ => mergeWitnessRelations (reflectionWitnessRelation φ) (formulaWitnessRelation φ)

theorem reflectionWitnessRelation_definable {n : ℕ} (φ : SetTheorySemisentence n) :
    ℒₛₑₜ-relation[V] (reflectionWitnessRelation φ) := by
  induction φ with
  | verum => change ℒₛₑₜ-relation[V] (fun _ _ ↦ False); definability
  | falsum => change ℒₛₑₜ-relation[V] (fun _ _ ↦ False); definability
  | rel r ts => change ℒₛₑₜ-relation[V] (fun _ _ ↦ False); definability
  | nrel r ts => change ℒₛₑₜ-relation[V] (fun _ _ ↦ False); definability
  | and φ ψ ihφ ihψ => exact mergeWitnessRelations_definable _ _ ihφ ihψ
  | or φ ψ ihφ ihψ => exact mergeWitnessRelations_definable _ _ ihφ ihψ
  | all φ ih =>
    have := formulaWitnessRelation_definable (V := V) φ
    exact mergeWitnessRelations_definable _ _ ih (by definability)
  | exs φ ih => exact mergeWitnessRelations_definable _ _ ih (formulaWitnessRelation_definable φ)

theorem finiteSequence_mem_hierarchy_limit {δ s : V} [IsOrdinal δ]
    (hω : (ω : V) ∈ δ) (hlim : ∀ ξ ∈ δ, succ ξ ∈ δ)
    (hs : s ∈ finiteSequences (hierarchy δ)) : s ∈ hierarchy δ := by
  have hn (n : V) (hn : n ∈ (ω : V)) : n ∈ hierarchy δ :=
    ordinal_subset_hierarchy δ _ (IsOrdinal.toIsTransitive.mem_trans hn hω)
  apply finiteSequence_induction (hierarchy δ) (fun s ↦ s ∈ hierarchy δ) (by definability)
    (hn ∅ (by simp)) ?_ s hs
  intro n hnω t _ x hx ht
  have hp := kpair_mem_hierarchy_limit hlim (hn n hnω) hx
  have hsing : ({⟨n, x⟩ₖ} : V) ∈ hierarchy δ := by simpa using pair_mem_hierarchy_limit hlim hp hp
  have hu := sUnion_mem_hierarchy_limit hlim (pair_mem_hierarchy_limit hlim hsing ht)
  change ({⟨n, x⟩ₖ} : V) ∪ t ∈ hierarchy δ
  simpa only [pair_eq_doubleton, ← union_def] using hu

theorem standardTuple_mem_hierarchy_limit {δ : V} [IsOrdinal δ] {n : ℕ}
    (hω : (ω : V) ∈ δ) (hlim : ∀ ξ ∈ δ, succ ξ ∈ δ) (b : Fin n → V)
    (hb : ∀ i, b i ∈ hierarchy δ) : standardTuple b ∈ hierarchy δ :=
  finiteSequence_mem_hierarchy_limit hω hlim
    ((mem_finiteSequences_iff _ _).mpr ⟨(n : V), by simp, standardTuple_mem_function b hb⟩)

theorem formulaWitnessRelation_standardTuple {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (b : Fin n → V) (y : V) : formulaWitnessRelation φ (standardTuple b) y ↔ φ.Evalb (y :> b) := by
  simp only [formulaWitnessRelation, value_standardTuple]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem setDomain_term_val (A : V) {n : ℕ} (b : Fin n → SetDomain A) (t : SetTheorySemiterm Empty n) :
    (t.val b Empty.elim).val = t.val (fun i ↦ (b i).val) Empty.elim := by
  cases t with
  | bvar i => rfl
  | fvar e => exact Empty.elim e
  | func f ts => exact Empty.elim f

def IsFormulaAbsoluteAt {n : ℕ} (φ : SetTheorySemisentence n) (δ : V) : Prop :=
  ∀ b : Fin n → SetDomain (hierarchy δ), φ.Evalb b ↔ φ.Evalb (fun i ↦ (b i).val)

theorem formula_absolute_of_witnessClosed {δ : V} [IsOrdinal δ]
    (hω : (ω : V) ∈ δ) (hlim : ∀ ξ ∈ δ, succ ξ ∈ δ) {n : ℕ} (φ : SetTheorySemisentence n)
    (hc : IsWitnessClosed (reflectionWitnessRelation φ) δ) : IsFormulaAbsoluteAt φ δ := by
  induction φ with
  | verum => intro b; rfl
  | falsum => intro b; rfl
  | rel r ts =>
    intro b
    cases r <;> simp only [Semiformula.Evalb, Semiformula.eval_rel, Structure.rel, Function.comp_def,
      ← setDomain_term_val]
    · exact Subtype.ext_iff
    · rfl
  | nrel r ts =>
    intro b
    cases r <;> simp only [Semiformula.Evalb, Semiformula.eval_nrel, Structure.rel, Function.comp_def,
      ← setDomain_term_val]
    · exact not_congr Subtype.ext_iff
    · rfl
  | and φ ψ ihφ ihψ =>
    obtain ⟨hφ, hψ⟩ := mergeWitnessClosed hω hlim hc
    intro b
    exact and_congr (ihφ hφ b) (ihψ hψ b)
  | or φ ψ ihφ ihψ =>
    obtain ⟨hφ, hψ⟩ := mergeWitnessClosed hω hlim hc
    intro b
    exact or_congr (ihφ hφ b) (ihψ hψ b)
  | all φ ih =>
    obtain ⟨hφ, hw⟩ := mergeWitnessClosed hω hlim hc
    intro b
    change (∀ y : SetDomain (hierarchy δ), φ.Evalb (y :> b)) ↔
      ∀ y : V, φ.Evalb (y :> fun i ↦ (b i).val)
    constructor
    · intro h y
      by_contra hn
      let v := fun i ↦ (b i).val
      have hs := standardTuple_mem_hierarchy_limit hω hlim v (fun i ↦ (b i).property)
      obtain ⟨z, hz, hneg⟩ := hw (standardTuple v) hs ⟨y, by
        simpa only [formulaWitnessRelation_standardTuple] using hn⟩
      have htrue := (ih hφ (⟨z, hz⟩ :> b)).mp (h ⟨z, hz⟩)
      apply hneg
      apply (formulaWitnessRelation_standardTuple φ v z).mpr
      have he := setDomain_val_vecCons (hierarchy δ) (⟨z, hz⟩ : SetDomain (hierarchy δ)) b
      rw [he] at htrue
      exact htrue
    · intro h y
      apply (ih hφ (y :> b)).mpr
      simpa only [setDomain_val_vecCons] using h y.val
  | exs φ ih =>
    obtain ⟨hφ, hw⟩ := mergeWitnessClosed hω hlim hc
    intro b
    change (∃ y : SetDomain (hierarchy δ), φ.Evalb (y :> b)) ↔
      ∃ y : V, φ.Evalb (y :> fun i ↦ (b i).val)
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y.val, ?_⟩
      simpa only [setDomain_val_vecCons] using (ih hφ (y :> b)).mp hy
    · rintro ⟨y, hy⟩
      let v := fun i ↦ (b i).val
      have hs := standardTuple_mem_hierarchy_limit hω hlim v (fun i ↦ (b i).property)
      obtain ⟨z, hz, hrel⟩ := hw (standardTuple v) hs ⟨y, (formulaWitnessRelation_standardTuple φ v y).mpr hy⟩
      refine ⟨⟨z, hz⟩, (ih hφ (⟨z, hz⟩ :> b)).mpr ?_⟩
      have he := setDomain_val_vecCons (hierarchy δ) (⟨z, hz⟩ : SetDomain (hierarchy δ)) b
      rw [he]
      exact (formulaWitnessRelation_standardTuple φ v z).mp hrel

theorem ordinal_mem_of_subset_mem {α β δ : V} [IsOrdinal α] [IsOrdinal β] [IsOrdinal δ]
    (h : α ⊆ β) (hβ : β ∈ δ) : α ∈ δ := by
  rcases IsOrdinal.subset_iff.mp h with heq | hlt
  · exact heq.symm ▸ hβ
  · exact IsOrdinal.toIsTransitive.mem_trans hlt hβ

theorem formula_reflection_above {n : ℕ} (φ : SetTheorySemisentence n) (γ : V) [IsOrdinal γ] :
    ∃ δ : V, IsOrdinal δ ∧ γ ∈ δ ∧ (ω : V) ∈ δ ∧
      (∀ ξ ∈ δ, succ ξ ∈ δ) ∧ IsFormulaAbsoluteAt φ δ := by
  have : IsOrdinal (γ ∪ (ω : V)) := ordinal_union_ordinal _ _
  obtain ⟨δ, hδ, hbig, hlim, hc⟩ := witnessClosed_above (reflectionWitnessRelation φ)
    (reflectionWitnessRelation_definable φ) (γ ∪ (ω : V))
  have : IsOrdinal δ := hδ
  have hγ : γ ∈ δ := ordinal_mem_of_subset_mem (fun x hx ↦ mem_union_iff.mpr (Or.inl hx)) hbig
  have hω : (ω : V) ∈ δ := ordinal_mem_of_subset_mem (fun x hx ↦ mem_union_iff.mpr (Or.inr hx)) hbig
  exact ⟨δ, hδ, hγ, hω, hlim, formula_absolute_of_witnessClosed hω hlim φ hc⟩

abbrev FormulaWithArity := Σ n : ℕ, SetTheorySemisentence n

def finiteReflectionWitnessRelation : List FormulaWithArity → V → V → Prop
  | [] => fun _ _ ↦ False
  | φ :: Φ => mergeWitnessRelations (reflectionWitnessRelation φ.2) (finiteReflectionWitnessRelation Φ)

theorem finiteReflectionWitnessRelation_definable (Φ : List FormulaWithArity) :
    ℒₛₑₜ-relation[V] (finiteReflectionWitnessRelation Φ) := by
  induction Φ with
  | nil => change ℒₛₑₜ-relation[V] (fun _ _ ↦ False); definability
  | cons φ Φ ih => exact mergeWitnessRelations_definable _ _ (reflectionWitnessRelation_definable φ.2) ih

theorem finiteReflectionWitnessClosed {δ : V} [IsOrdinal δ]
    (hω : (ω : V) ∈ δ) (hlim : ∀ ξ ∈ δ, succ ξ ∈ δ) (Φ : List FormulaWithArity)
    (hc : IsWitnessClosed (finiteReflectionWitnessRelation Φ) δ) :
    ∀ φ ∈ Φ, IsWitnessClosed (reflectionWitnessRelation φ.2) δ := by
  induction Φ with
  | nil => intro φ hφ; cases hφ
  | cons ψ Φ ih =>
    obtain ⟨hψ, hΦ⟩ := mergeWitnessClosed hω hlim hc
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact hψ
    · exact ih hΦ φ hφ

theorem finite_formula_reflection_above (Φ : List FormulaWithArity) (γ : V) [IsOrdinal γ] :
    ∃ δ : V, IsOrdinal δ ∧ γ ∈ δ ∧ (ω : V) ∈ δ ∧
      (∀ ξ ∈ δ, succ ξ ∈ δ) ∧ ∀ φ ∈ Φ, IsFormulaAbsoluteAt φ.2 δ := by
  have : IsOrdinal (γ ∪ (ω : V)) := ordinal_union_ordinal _ _
  obtain ⟨δ, hδ, hbig, hlim, hc⟩ := witnessClosed_above (finiteReflectionWitnessRelation Φ)
    (finiteReflectionWitnessRelation_definable Φ) (γ ∪ (ω : V))
  have : IsOrdinal δ := hδ
  have hγ : γ ∈ δ := ordinal_mem_of_subset_mem (fun x hx ↦ mem_union_iff.mpr (Or.inl hx)) hbig
  have hω : (ω : V) ∈ δ := ordinal_mem_of_subset_mem (fun x hx ↦ mem_union_iff.mpr (Or.inr hx)) hbig
  refine ⟨δ, hδ, hγ, hω, hlim, ?_⟩
  intro φ hφ
  exact formula_absolute_of_witnessClosed hω hlim φ.2 (finiteReflectionWitnessClosed hω hlim Φ hc φ hφ)

theorem finite_formula_reflection_containing (Φ : List FormulaWithArity) (A : V) :
    ∃ δ : V, IsOrdinal δ ∧ A ∈ hierarchy δ ∧ (ω : V) ∈ δ ∧
      (∀ ξ ∈ δ, succ ξ ∈ δ) ∧ ∀ φ ∈ Φ, IsFormulaAbsoluteAt φ.2 δ := by
  obtain ⟨δ, hδ, hA, hω, hlim, hΦ⟩ := finite_formula_reflection_above Φ (rank A)
  have : IsOrdinal δ := hδ
  exact ⟨δ, hδ, (mem_hierarchy_iff_rank_mem A δ).mpr hA, hω, hlim, hΦ⟩

end ZFVP
