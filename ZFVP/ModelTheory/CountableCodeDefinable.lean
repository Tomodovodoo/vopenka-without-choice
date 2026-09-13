import ZFVP.ModelTheory.GroundRealsHOD
import ZFVP.SetTheory.SetCodes
import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.NaturalPairing
import ZFVP.SetTheory.EndExtensionWellOrdering
import ZFVP.SetTheory.EndExtensionFinite

/-! A set of a forcing extension whose transitive closure is countable is definable from a real.

The transitive closure is enumerated by an injection into `ω`; transporting membership along the
enumeration gives a relation `E` on a set `D ⊆ ω` whose transitive collapse sends one point of `D`
to the set. The relation is coded as a subset of `ω` through a ground pairing function, so all four
parameters of the defining formula are allowed in `HOD_{V ∪ R}`: two reals, one check and one
natural number. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Coding a relation on naturals by a real -/

/-- The real coding a relation `E` on naturals through the pairing function `p`. -/
noncomputable def relationReal (p E : V) : V := {n ∈ (ω : V) ; ∃ q ∈ E, n = p ‘ q}

theorem relationReal_subset (p E : V) : relationReal p E ⊆ (ω : V) :=
  fun _ hn ↦ (mem_sep_iff.mp hn).1

/-- A pair of naturals lies in `E` exactly when its code lies in the real coding `E`. -/
theorem value_mem_relationReal_iff {p E q : V} (hp : p ∈ (ω : V) ^ ((ω : V) ×ˢ (ω : V)))
    (hpinj : Injective p) (hE : E ⊆ (ω : V) ×ˢ (ω : V)) (hq : q ∈ (ω : V) ×ˢ (ω : V)) :
    p ‘ q ∈ relationReal p E ↔ q ∈ E := by
  constructor
  · intro h
    obtain ⟨-, q', hq', heq⟩ := mem_sep_iff.mp h
    exact (injective_value_eq hp hpinj hq (hE q' hq') heq) ▸ hq'
  · intro h
    exact mem_sep_iff.mpr ⟨function_value_mem hp hq, q, h, rfl⟩

/-! ### The defining formula -/

/-- `b ∈ f ‘ t`, where `f` is the transitive collapse of the relation `E` on `D` that the real `r`
codes through the pairing `p`. -/
def collapseWitnessFormula : SetTheorySemisentence 5 :=
  f“b r D p t. ∃ E, (∀ q, q ∈ E ↔ (q ∈ !prod.dfn D D ∧ !value.dfn p q ∈ r)) ∧
    ∃ C, ∃ f ∈ !function.dfn C D, !IsTransitive.dfn C ∧ C = !range.dfn f ∧
      (∀ m ∈ D, ∀ n ∈ D, !value.dfn f m = !value.dfn f n → m = n) ∧
      (∀ m ∈ D, ∀ n ∈ D, (!value.dfn f m ∈ !value.dfn f n ↔ !kpair.dfn m n ∈ E)) ∧
      b ∈ !value.dfn f t”

theorem eval_collapseWitnessFormula (b r D p t : V) :
    collapseWitnessFormula.Evalb ![b, r, D, p, t] ↔
      ∃ E : V, (∀ q, q ∈ E ↔ (q ∈ D ×ˢ D ∧ p ‘ q ∈ r)) ∧
        ∃ C f : V, f ∈ C ^ D ∧ IsTransitive C ∧ C = range f ∧
          (∀ m ∈ D, ∀ n ∈ D, f ‘ m = f ‘ n → m = n) ∧
          (∀ m ∈ D, ∀ n ∈ D, (f ‘ m ∈ f ‘ n ↔ ⟨m, n⟩ₖ ∈ E)) ∧
          b ∈ f ‘ t := by
  simp [collapseWitnessFormula]

/-- The value of a transitive collapse at a point is defined by `collapseWitnessFormula` from the
real coding the relation, the domain, the pairing and the point. -/
theorem mem_iff_collapseWitness {D E C f p t : V} (hD : D ⊆ (ω : V)) (hE : E ⊆ D ×ˢ D)
    (hcol : IsTransitiveCollapse E D C f) (hp : p ∈ (ω : V) ^ ((ω : V) ×ˢ (ω : V)))
    (hpinj : Injective p) (_ht : t ∈ D) (b : V) :
    b ∈ f ‘ t ↔ collapseWitnessFormula.Evalb ![b, relationReal p E, D, p, t] := by
  have hEω : E ⊆ (ω : V) ×ˢ (ω : V) := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_prod_iff.mp (hE z hz)
    exact kpair_mem_iff.mpr ⟨hD u hu, hD v hv⟩
  have hdec : ∀ q : V, q ∈ E ↔ (q ∈ D ×ˢ D ∧ p ‘ q ∈ relationReal p E) := by
    intro q
    constructor
    · intro hq
      exact ⟨hE q hq, (value_mem_relationReal_iff hp hpinj hEω (hEω q hq)).mpr hq⟩
    · rintro ⟨hqD, hqr⟩
      have hqω : q ∈ (ω : V) ×ˢ (ω : V) := by
        obtain ⟨u, hu, v, hv, rfl⟩ := mem_prod_iff.mp hqD
        exact kpair_mem_iff.mpr ⟨hD u hu, hD v hv⟩
      exact (value_mem_relationReal_iff hp hpinj hEω hqω).mp hqr
  have hwf : IsInternallyWellFounded E D := isInternallyWellFounded_of_collapse hcol
  rw [eval_collapseWitnessFormula]
  constructor
  · intro hb
    exact ⟨E, hdec, C, f, hcol.2.1, hcol.1, hcol.2.2.1.symm, hcol.2.2.2.1, hcol.2.2.2.2, hb⟩
  · rintro ⟨E', hE', C', f', hf', hC', hrange', hinj', hmem', hb⟩
    have hEE : E' = E := by
      apply mem_ext
      intro q
      rw [hE' q, hdec q]
    subst hEE
    have hcol' : IsTransitiveCollapse E' D C' f' := ⟨hC', hf', hrange'.symm, hinj', hmem'⟩
    have h1 : f' = collapseGraph hwf := (transitiveCollapse_unique hwf hcol').1
    have h2 : f = collapseGraph hwf := (transitiveCollapse_unique hwf hcol).1
    rw [h2, ← h1]
    exact hb

/-! ### Codes for sets with countable transitive closure -/

/-- A member of a countable transitive set is the value of the transitive collapse of a relation on
a set of naturals. -/
theorem exists_countable_collapse_code {T x : V} [IsTransitive T] (hT : IsInternallyCountable T)
    (hx : x ∈ T) :
    ∃ D E C f t : V, D ⊆ (ω : V) ∧ E ⊆ D ×ˢ D ∧ IsTransitiveCollapse E D C f ∧ t ∈ D ∧
      f ‘ t = x := by
  obtain ⟨e, he, heinj⟩ := hT
  have : IsFunction e := IsFunction.of_mem he
  have hdom : domain e = T := domain_eq_of_mem_function he
  have hgf : converseGraph e ∈ T ^ range e := converseGraph_mem_function he heinj
  have hginj : Injective (converseGraph e) := converseGraph_injective e
  have hgrange : range (converseGraph e) = T := by rw [range_converseGraph, hdom]
  have hcol : IsTransitiveCollapse (valueRelation (converseGraph e) (range e)) (range e) T
      (converseGraph e) := isTransitiveCollapse_valueRelation hgf hginj hgrange
  refine ⟨range e, valueRelation (converseGraph e) (range e), T, converseGraph e, e ‘ x,
    range_subset_of_mem_function he, valueRelation_subset _ _, hcol, value_mem_range he hx,
    converseGraph_value_value he heinj hx⟩

namespace ForcingContext

variable {A : ForcingContext V}

/-- An n-ary form of the definition of `IsGroundRealDefinable`: a formula together with allowed
parameters that define the members of `x`. -/
theorem groundRealDefinable_of_definable_from_params {x : A.Model} {n : ℕ}
    (v : Fin n → A.Model) (hv : ∀ i, A.IsSolovayParameter (v i))
    (ψ : SetTheorySemisentence (n + 1)) (hx : ∀ b, b ∈ x ↔ ψ.Evalb (b :> v)) :
    A.IsGroundRealDefinable x := ⟨n, ψ, v, hv, hx⟩

/-- A set of the extension whose transitive closure is countable is definable from a real. -/
theorem groundRealDefinable_of_countable_transitiveClosure {x : A.Model}
    (h : IsInternallyCountable (transitiveClosure ({x} : A.Model))) :
    A.IsGroundRealDefinable x := by
  obtain ⟨pi, hpi, hpiinj⟩ := (omega_prod_cardLE_omega : ((ω : V) ×ˢ (ω : V)) ≤# (ω : V))
  have hcp : A.check pi ∈ (ω : A.Model) ^ ((ω : A.Model) ×ˢ (ω : A.Model)) := by
    have hc := (A.check_function_iff pi ((ω : V) ×ˢ (ω : V)) (ω : V)).mpr hpi
    have h1 : A.check ((ω : V) ×ˢ (ω : V)) = A.check (ω : V) ×ˢ A.check (ω : V) :=
      A.checkEmbedding.map_prod _ _
    rwa [h1, check_omega_eq] at hc
  have hcpinj : Injective (A.check pi) := (A.checkEmbedding.injective_iff pi).mpr hpiinj
  have : IsTransitive (transitiveClosure ({x} : A.Model)) := transitiveClosure_transitive _
  have hxT : x ∈ transitiveClosure ({x} : A.Model) :=
    subset_transitiveClosure _ _ (mem_singleton_iff.mpr rfl)
  obtain ⟨D, E, C, f, t, hDω, hEsub, hcol, htD, hft⟩ := exists_countable_collapse_code h hxT
  obtain ⟨m, hm⟩ := exists_check_of_mem_omega (hDω t htD)
  refine groundRealDefinable_of_definable_from_params
    ![relationReal (A.check pi) E, D, A.check pi, t] ?_ collapseWitnessFormula ?_
  · intro i
    match i with
    | 0 => exact Or.inr (Or.inl (by rw [check_omega_eq]; exact relationReal_subset _ _))
    | 1 => exact Or.inr (Or.inl (by rw [check_omega_eq]; exact hDω))
    | 2 => exact Or.inl ⟨pi, rfl⟩
    | 3 => exact Or.inl ⟨m, hm⟩
  · intro b
    rw [← hft]
    exact mem_iff_collapseWitness hDω hEsub hcol hcp hcpinj htD b

/-- A subset of a set with countable transitive closure is definable from a real. -/
theorem groundRealDefinable_of_countable_transitiveClosure_subset {x y : A.Model} (hxy : x ⊆ y)
    (h : IsInternallyCountable (transitiveClosure ({y} : A.Model))) :
    A.IsGroundRealDefinable x := by
  have hytr : IsTransitive (transitiveClosure ({y} : A.Model)) := transitiveClosure_transitive _
  have hyT : y ∈ transitiveClosure ({y} : A.Model) :=
    subset_transitiveClosure _ _ (mem_singleton_iff.mpr rfl)
  have hxsub : x ⊆ transitiveClosure ({y} : A.Model) :=
    fun z hz ↦ hytr.mem_trans (hxy z hz) hyT
  have hins : IsTransitive (insert x (transitiveClosure ({y} : A.Model)) : A.Model) := by
    refine ⟨fun u hu z hz ↦ ?_⟩
    rcases mem_insert.mp hu with rfl | hu
    · exact mem_insert.mpr (Or.inr (hxsub z hz))
    · exact mem_insert.mpr (Or.inr (hytr.mem_trans hz hu))
  have hsub : transitiveClosure ({x} : A.Model) ⊆ insert x (transitiveClosure ({y} : A.Model)) :=
    transitiveClosure_minimal _ _
      (by rw [singleton_subset_iff_mem]; exact mem_insert.mpr (Or.inl rfl)) hins
  exact groundRealDefinable_of_countable_transitiveClosure
    (internallyCountable_subset (internallyCountable_insert h x) hsub)

end ForcingContext

end ZFVP
