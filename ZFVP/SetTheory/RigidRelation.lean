import ZFVP.SetTheory.ChoiceDictionary
import ZFVP.SetTheory.WellOrderingChoice
import ZFVP.SetTheory.InternalPermutations
import ZFVP.SetTheory.InternalOrderType

/-! The rigid relation principle of Hamkins and Palumbo: every set carries a binary relation
whose only automorphism is the identity. Well-orderable sets have one, so the principle follows
from choice, and it transfers along elementary maps. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `f` is an automorphism of the structure `⟨A, R⟩`: a bijection of `A` with itself that
preserves and reflects `R`. -/
def IsAutomorphismOf (A R f : V) : Prop :=
  f ∈ A ^ A ∧ Injective f ∧ range f = A ∧
    ∀ x ∈ A, ∀ y ∈ A, (⟨x, y⟩ₖ ∈ R ↔ ⟨f ‘ x, f ‘ y⟩ₖ ∈ R)

instance isAutomorphismOf_definable : ℒₛₑₜ-relation₃[V] IsAutomorphismOf := by
  unfold IsAutomorphismOf
  definability

/-- `R` is a relation on `A` whose only automorphism is the identity. -/
def IsRigidRelation (A R : V) : Prop :=
  R ⊆ A ×ˢ A ∧ ∀ f, IsAutomorphismOf A R f → ∀ x ∈ A, f ‘ x = x

instance isRigidRelation_definable : ℒₛₑₜ-relation[V] IsRigidRelation := by
  unfold IsRigidRelation
  definability

/-- `A` carries a rigid relation. -/
def HasRigidRelation (A : V) : Prop := ∃ R, IsRigidRelation A R

instance hasRigidRelation_definable : ℒₛₑₜ-predicate[V] HasRigidRelation := by
  unfold HasRigidRelation
  definability

/-- The rigid relation principle RR: every set carries a rigid relation. -/
def RigidRelationPrinciple (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∀ A : V, HasRigidRelation A

/-! ### Basic facts about automorphisms -/

theorem IsAutomorphismOf.surjective {A R f : V} (hf : IsAutomorphismOf A R f) {y : V}
    (hy : y ∈ A) : ∃ x ∈ A, f ‘ x = y := by
  have : IsFunction f := IsFunction.of_mem hf.1
  obtain ⟨x, hx⟩ := mem_range_iff.mp (hf.2.2.1.symm ▸ hy)
  exact ⟨x, (mem_of_mem_functions hf.1 hx).1, value_eq_of_kpair_mem hx⟩

/-- A function into `B` on `B` whose values exhaust `B` has range `B`. -/
theorem range_eq_of_values {B h : V} (hh : h ∈ B ^ B) (hs : ∀ y ∈ B, ∃ x ∈ B, h ‘ x = y) :
    range h = B := by
  have : IsFunction h := IsFunction.of_mem hh
  apply subset_antisymm (range_subset_of_mem_function hh)
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hs y hy
  exact hxy ▸ mem_range_of_kpair_mem
    (kpair_value_mem (by simpa only [domain_eq_of_mem_function hh] using hx))

/-! ### Well orders are rigid -/

theorem isRigidRelation_of_isInternalWellOrder {R A : V} (h : IsInternalWellOrder R A) :
    IsRigidRelation A R := by
  refine ⟨h.1, ?_⟩
  intro f hf
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀A, hx₀⟩ := hcon
  have hBA : ({x ∈ A ; f ‘ x ≠ x} : V) ⊆ A := fun y hy ↦ (mem_sep_iff.mp hy).1
  have hBne : IsNonempty ({x ∈ A ; f ‘ x ≠ x} : V) := ⟨x₀, mem_sep_iff.mpr ⟨hx₀A, hx₀⟩⟩
  obtain ⟨a, haB, hmin⟩ := h.2.1 _ hBA hBne
  have haA : a ∈ A := hBA a haB
  have hane : f ‘ a ≠ a := (mem_sep_iff.mp haB).2
  have hfaA : f ‘ a ∈ A := function_value_mem hf.1 haA
  rcases h.2.2.2 a haA (f ‘ a) hfaA with hlt | heq | hgt
  · -- `a` lies strictly below `f ‘ a`, so the `f`-preimage of `a` lies strictly below `a`.
    obtain ⟨b, hbA, hbe⟩ := hf.surjective haA
    have hba : ⟨b, a⟩ₖ ∈ R := (hf.2.2.2 b hbA a haA).mpr (by rw [hbe]; exact hlt)
    have hbfix : f ‘ b = b := by
      by_contra hne
      exact hmin b (mem_sep_iff.mpr ⟨hbA, hne⟩) hba
    have : b = a := by rw [← hbfix, hbe]
    exact internalWellFounded_irrefl h.2.1 a haA (this ▸ hba)
  · exact hane heq.symm
  · -- `f ‘ a` lies strictly below `a`, hence is fixed, and injectivity forces `f ‘ a = a`.
    have hfix : f ‘ (f ‘ a) = f ‘ a := by
      by_contra hne
      exact hmin (f ‘ a) (mem_sep_iff.mpr ⟨hfaA, hne⟩) hgt
    exact hane (injective_value_eq hf.1 hf.2.1 hfaA haA hfix)

theorem hasRigidRelation_of_wellOrderable {A : V} (h : IsWellOrderable A) : HasRigidRelation A := by
  obtain ⟨R, hR⟩ := h
  exact ⟨R, isRigidRelation_of_isInternalWellOrder hR⟩

theorem rigidRelationPrinciple_of_internalChoice (hAC : InternalChoice V) :
    RigidRelationPrinciple V := fun A ↦
  hasRigidRelation_of_wellOrderable (wellOrderable_of_internalChoice hAC A)

/-! ### Transporting a rigid relation along a bijection -/

/-- The pullback of a relation `R` on the codomain of `f` to the domain `A`. -/
noncomputable def pullbackRelation (A f R : V) : V :=
  {z ∈ A ×ˢ A ; ⟨f ‘ (kpair.π₁ z), f ‘ (kpair.π₂ z)⟩ₖ ∈ R}

theorem kpair_mem_pullbackRelation {A f R x y : V} (hx : x ∈ A) (hy : y ∈ A) :
    ⟨x, y⟩ₖ ∈ pullbackRelation A f R ↔ ⟨f ‘ x, f ‘ y⟩ₖ ∈ R := by
  simp only [pullbackRelation, mem_sep_iff, kpair.π₁_kpair, kpair.π₂_kpair,
    kpair_mem_iff, and_iff_right (And.intro hx hy)]

theorem pullbackRelation_subset (A f R : V) : pullbackRelation A f R ⊆ A ×ˢ A :=
  fun _ hz ↦ (mem_sep_iff.mp hz).1

theorem hasRigidRelation_of_bijection {A B f : V} (hf : f ∈ B ^ A) (hinj : Injective f)
    (hran : range f = B) (hB : HasRigidRelation B) : HasRigidRelation A := by
  classical
  obtain ⟨S, hSsub, hSrig⟩ := hB
  have hfF : IsFunction f := IsFunction.of_mem hf
  -- the inverse bijection `B → A`
  have hfi : converseGraph f ∈ A ^ B := hran ▸ converseGraph_mem_function hf hinj
  have hfiinj : Injective (converseGraph f) := converseGraph_injective f
  have hfiF : IsFunction (converseGraph f) := IsFunction.of_mem hfi
  have hinv : ∀ x ∈ A, (converseGraph f) ‘ (f ‘ x) = x := fun x hx ↦
    converseGraph_value_value hf hinj hx
  have hinv' : ∀ y ∈ B, f ‘ ((converseGraph f) ‘ y) = y := fun y hy ↦
    value_converseGraph_value hf hinj (hran ▸ hy)
  refine ⟨pullbackRelation A f S, pullbackRelation_subset A f S, ?_⟩
  intro g hg x hxA
  -- conjugate `g` to an automorphism `h` of `⟨B, S⟩`
  set h : V := compose (converseGraph f) (compose g f) with hdef
  have hgf : compose g f ∈ B ^ A := compose_function hg.1 hf
  have hh : h ∈ B ^ B := compose_function hfi hgf
  have hvalue : ∀ y ∈ B, h ‘ y = f ‘ (g ‘ ((converseGraph f) ‘ y)) := by
    intro y hy
    rw [hdef, value_compose_of_mem_function hfi hgf hy,
      value_compose_of_mem_function hg.1 hf (function_value_mem hfi hy)]
  have hauto : IsAutomorphismOf B S h := by
    refine ⟨hh, compose_injective hfiinj (compose_injective hg.2.1 hinj), ?_, ?_⟩
    · refine range_eq_of_values hh ?_
      intro y hy
      obtain ⟨b, hbA, hbe⟩ := hg.surjective (function_value_mem hfi hy)
      refine ⟨f ‘ b, function_value_mem hf hbA, ?_⟩
      rw [hvalue _ (function_value_mem hf hbA), hinv b hbA, hbe, hinv' y hy]
    · intro u hu v hv
      have hau : (converseGraph f) ‘ u ∈ A := function_value_mem hfi hu
      have hav : (converseGraph f) ‘ v ∈ A := function_value_mem hfi hv
      rw [hvalue u hu, hvalue v hv]
      rw [← hinv' u hu, ← hinv' v hv]
      rw [← kpair_mem_pullbackRelation (f := f) (R := S) hau hav]
      rw [hg.2.2.2 _ hau _ hav]
      rw [kpair_mem_pullbackRelation (f := f) (R := S)
        (function_value_mem hg.1 hau) (function_value_mem hg.1 hav)]
      rw [hinv' u hu, hinv' v hv]
  -- rigidity of `S` fixes `h`, and injectivity of `f` transfers this back to `g`
  have hfx : h ‘ (f ‘ x) = f ‘ x := hSrig h hauto _ (function_value_mem hf hxA)
  rw [hvalue _ (function_value_mem hf hxA), hinv x hxA] at hfx
  exact injective_value_eq hf hinj (function_value_mem hg.1 hxA) hxA hfx

/-! ### Hereditary rigidity -/

/-- `R` restricts to a rigid relation on every subset of `A`. -/
def IsHereditarilyRigid (A R : V) : Prop := ∀ B, B ⊆ A → IsRigidRelation B (R ∩ (B ×ˢ B))

instance isHereditarilyRigid_definable : ℒₛₑₜ-relation[V] IsHereditarilyRigid := by
  unfold IsHereditarilyRigid
  definability

theorem isInternalWellOrder_restrict {R A B : V} (h : IsInternalWellOrder R A) (hBA : B ⊆ A) :
    IsInternalWellOrder (R ∩ (B ×ˢ B)) B := by
  refine ⟨fun z hz ↦ (mem_inter_iff.mp hz).2, ?_, ?_, ?_⟩
  · intro C hCB hC
    obtain ⟨x, hx, hmin⟩ := h.2.1 C (fun y hy ↦ hBA y (hCB y hy)) hC
    exact ⟨x, hx, fun y hy hmem ↦ hmin y hy (mem_inter_iff.mp hmem).1⟩
  · intro x hx y hy z hz hxy hyz
    refine mem_inter_iff.mpr ⟨h.2.2.1 x (hBA x hx) y (hBA y hy) z (hBA z hz)
      (mem_inter_iff.mp hxy).1 (mem_inter_iff.mp hyz).1, kpair_mem_iff.mpr ⟨hx, hz⟩⟩
  · intro x hx y hy
    rcases h.2.2.2 x (hBA x hx) y (hBA y hy) with hxy | heq | hyx
    · exact Or.inl (mem_inter_iff.mpr ⟨hxy, kpair_mem_iff.mpr ⟨hx, hy⟩⟩)
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr (mem_inter_iff.mpr ⟨hyx, kpair_mem_iff.mpr ⟨hy, hx⟩⟩))

theorem isHereditarilyRigid_of_isInternalWellOrder {R A : V} (h : IsInternalWellOrder R A) :
    IsHereditarilyRigid A R := fun _ hBA ↦
  isRigidRelation_of_isInternalWellOrder (isInternalWellOrder_restrict h hBA)

/-! ### The principle as a sentence, and transfer along elementary maps -/

def rigidRelationSentence : SetTheorySentence :=
  f“∀ A, ∃ R, R ⊆ !prod.dfn A A ∧ ∀ f, (f ∈ !function.dfn A A ∧ !Injective.dfn f ∧
      !range.dfn f = A ∧ ∀ x ∈ A, ∀ y ∈ A,
        (!kpair.dfn x y ∈ R ↔ !kpair.dfn (!value.dfn f x) (!value.dfn f y) ∈ R)) →
    ∀ x ∈ A, !value.dfn f x = x”

instance rigidRelationSentence_defined :
    Defined (fun _ : Fin 0 → V ↦ RigidRelationPrinciple V) rigidRelationSentence :=
  ⟨fun v ↦ by
    simp [rigidRelationSentence, RigidRelationPrinciple, HasRigidRelation, IsRigidRelation,
      IsAutomorphismOf]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rigidRelationPrinciple_iff (j : ElementaryMap V W) :
    RigidRelationPrinciple V ↔ RigidRelationPrinciple W :=
  j.map_defined rigidRelationSentence (fun _ ↦ RigidRelationPrinciple V)
    (fun _ ↦ RigidRelationPrinciple W) ![]

end ElementaryMap
end ZFVP
