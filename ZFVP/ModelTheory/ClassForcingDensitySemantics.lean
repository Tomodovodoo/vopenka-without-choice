import ZFVP.ModelTheory.DefinableClassGeneric

/-! The semantic forcing argument in Proposition `prop:class-forcing-criteria`.

The carrier and the forcing relations may be proper classes of the ground model.
The indexed extensions and their forcing theorem are hypotheses, as in the paper.
No preservation of a large-cardinal property or of Vopenka's principle is assumed.
The only class-comprehension operation used is projection over ordinals above a
ground ordinal; this is an elementary comprehension instance in GBC.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u v w

variable (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (I : Type w) (W : I → Type v)
    [∀ i, SetStructure (W i)] [∀ i, Nonempty (W i)]
    [∀ i, (W i)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The forcing-theorem and same-ordinals hypotheses needed by the density
argument. `I` indexes the generic extensions. `classes` is the ground class part,
and `ordinalProjection_mem` is the indicated GBC comprehension instance.
The negation clause is the usual recursive clause, not semantic VP preservation. -/
structure ClassForcingDensitySemantics where
  P : V → Prop
  R : V → V → Prop
  top : V
  top_mem : P top
  le_top : ∀ p, P p → R p top
  classes : Set (Set V)
  ordinalProjection_mem : ∀ A ∈ classes, ∀ η : V,
    {p | ∃ κ : V, IsOrdinal κ ∧ η ∈ κ ∧ ⟨p, κ⟩ₖ ∈ A} ∈ classes
  filter : I → Set V
  filter_isFilter : ∀ i, IsExternalClassForcingFilter P R (filter i)
  generic_meets : ∀ i, ∀ D ∈ classes,
    ClassForcingDense P R (fun p ↦ p ∈ D) → ∃ p ∈ filter i, p ∈ D
  generic_through : ∀ p, P p → ∃ i, p ∈ filter i
  Names : Set V
  check : V → {τ : V // τ ∈ Names}
  eval : ∀ i, {τ : V // τ ∈ Names} → W i
  ground_mem_iff : ∀ i a b, eval i (check a) ∈ eval i (check b) ↔ a ∈ b
  ground_ordinal : ∀ i a, IsOrdinal a → IsOrdinal (eval i (check a))
  no_new_ordinals : ∀ i a, IsOrdinal a →
    ∃ b : V, IsOrdinal b ∧ eval i (check b) = a
  Forces : ∀ {n : ℕ}, V → SetTheorySemisentence n →
    (Fin n → {τ : V // τ ∈ Names}) → Prop
  forces_mem : ∀ {n} {p} {φ : SetTheorySemisentence n} {a}, Forces p φ a → P p
  forces_mono : ∀ {n} {p q} {φ : SetTheorySemisentence n} {a},
    Forces p φ a → P q → R q p → Forces q φ a
  forces_neg : ∀ {n} (p) (φ : SetTheorySemisentence n) (a),
    Forces p (∼φ) a ↔ P p ∧ ∀ q, P q → R q p → ¬ Forces q φ a
  truth : ∀ i {n} (φ : SetTheorySemisentence n) (a),
    φ.Evalb (fun j ↦ eval i (a j)) ↔ ∃ p ∈ filter i, Forces p φ a
  check_forcing_class : ∀ K : SetTheorySemisentence 1,
    {z | ∃ p κ : V, z = ⟨p, κ⟩ₖ ∧ Forces p K ![check κ]} ∈ classes

namespace ClassForcingDensitySemantics

variable {V I W} (S : ClassForcingDensitySemantics V I W)

/-- Every generic filter contains the largest condition. -/
theorem top_mem_filter (i : I) : S.top ∈ S.filter i := by
  obtain ⟨p, hp⟩ := (S.filter_isFilter i).2.1
  exact (S.filter_isFilter i).2.2.1 p hp S.top S.top_mem
    (S.le_top p ((S.filter_isFilter i).1 p hp))

/-- Forcing below a condition is exactly truth in all generics through it.
The reverse implication uses the recursive negation clause twice. -/
theorem forces_iff_all_generics {n : ℕ} {p : V} (hp : S.P p)
    (φ : SetTheorySemisentence n) (a : Fin n → {τ : V // τ ∈ S.Names}) :
    S.Forces p φ a ↔
      ∀ i, p ∈ S.filter i → φ.Evalb (fun j ↦ S.eval i (a j)) := by
  constructor
  · intro h i hi
    exact (S.truth i φ a).mpr ⟨p, hi, h⟩
  · intro h
    have hnn : S.Forces p (∼∼φ) a := by
      apply (S.forces_neg p (∼φ) a).mpr
      refine ⟨hp, ?_⟩
      intro q hq hqp hn
      obtain ⟨i, hi⟩ := S.generic_through q hq
      have hpi : p ∈ S.filter i := (S.filter_isFilter i).2.2.1 q hi p hp hqp
      have hnot := (S.truth i (∼φ) a).mpr ⟨q, hi, hn⟩
      have hnot' : ¬ φ.Evalb (fun j ↦ S.eval i (a j)) := by simpa using hnot
      exact hnot' (h i hpi)
    simpa using hnn

theorem top_forces_iff {n : ℕ} (φ : SetTheorySemisentence n)
    (a : Fin n → {τ : V // τ ∈ S.Names}) :
    S.Forces S.top φ a ↔ ∀ i, φ.Evalb (fun j ↦ S.eval i (a j)) := by
  rw [S.forces_iff_all_generics S.top_mem]
  exact ⟨fun h i ↦ h i (S.top_mem_filter i), fun h i _ ↦ h i⟩

theorem eval_singleton (i : I) (τ : {τ : V // τ ∈ S.Names}) :
    (fun j : Fin 1 ↦ S.eval i (![τ] j)) = ![S.eval i τ] := by
  funext j
  exact Fin.cases rfl (Fin.elim0 ·) j

/-- Conditions forcing a witness above the ground ordinal `η`. -/
def aboveClass (K : SetTheorySemisentence 1) (η : V) : Set V :=
  {p | ∃ κ : V, IsOrdinal κ ∧ η ∈ κ ∧ S.Forces p K ![S.check κ]}

theorem aboveClass_mem (K : SetTheorySemisentence 1) (η : V) :
    S.aboveClass K η ∈ S.classes := by
  have h := S.ordinalProjection_mem _ (S.check_forcing_class K) η
  convert h using 1
  ext p
  simp only [aboveClass, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨κ, hκ, hηκ, hp⟩
    exact ⟨κ, hκ, hηκ, p, κ, rfl, hp⟩
  · rintro ⟨κ, hκ, hηκ, p', κ', heq, hp⟩
    have hh : p = p' ∧ κ = κ' := kpair_inj heq
    exact ⟨κ, hκ, hηκ, by simpa only [hh.1, hh.2] using hp⟩

/-- The right side of the density criterion, for a fixed property of ordinals. -/
def denselyUnbounded (K : SetTheorySemisentence 1) : Prop :=
  ∀ p : V, S.P p → ∀ η : V, IsOrdinal η →
    ∃ q : V, S.P q ∧ S.R q p ∧
      ∃ κ : V, IsOrdinal κ ∧ η ∈ κ ∧ S.Forces q K ![S.check κ]

/-- Actual unboundedness in every indexed extension, with its own ordinals. -/
def extensionsUnbounded (_S : ClassForcingDensitySemantics V I W)
    (K : SetTheorySemisentence 1) : Prop :=
  ∀ i, ∀ η : W i, IsOrdinal η →
    ∃ κ : W i, IsOrdinal κ ∧ η ∈ κ ∧ K.Evalb ![κ]

/-- The semantic core of the class-forcing density criterion. The same-ordinals
hypothesis places bounds in the ground in the forward direction and witnesses
in the ground in the reverse direction. Truth and directedness produce a
condition below the prescribed `p`. -/
theorem denselyUnbounded_iff (K : SetTheorySemisentence 1) :
    S.denselyUnbounded K ↔ S.extensionsUnbounded K := by
  constructor
  · intro hd i η hη
    obtain ⟨η₀, hη₀, rfl⟩ := S.no_new_ordinals i η hη
    have hD : ClassForcingDense S.P S.R (fun p ↦ p ∈ S.aboveClass K η₀) := by
      constructor
      · rintro p ⟨κ, hκ, hηκ, hp⟩
        exact S.forces_mem hp
      · intro p hp
        obtain ⟨q, hq, hqp, κ, hκ, hηκ, hqK⟩ := hd p hp η₀ hη₀
        exact ⟨q, ⟨κ, hκ, hηκ, hqK⟩, hqp⟩
    obtain ⟨p, hp, κ, hκ, hηκ, hpK⟩ :=
      S.generic_meets i _ (S.aboveClass_mem K η₀) hD
    refine ⟨S.eval i (S.check κ), S.ground_ordinal i κ hκ,
      (S.ground_mem_iff i η₀ κ).mpr hηκ, ?_⟩
    simpa only [S.eval_singleton] using (S.truth i K ![S.check κ]).mpr ⟨p, hp, hpK⟩
  · intro h p hp η hη
    obtain ⟨i, hpi⟩ := S.generic_through p hp
    obtain ⟨κ, hκ, hηκ, hK⟩ := h i (S.eval i (S.check η)) (S.ground_ordinal i η hη)
    obtain ⟨κ₀, hκ₀, rfl⟩ := S.no_new_ordinals i κ hκ
    obtain ⟨r, hri, hrK⟩ := (S.truth i K ![S.check κ₀]).mp
      (by simpa only [S.eval_singleton] using hK)
    obtain ⟨q, hqi, hqp, hqr⟩ := (S.filter_isFilter i).2.2.2 p hpi r hri
    have hq := (S.filter_isFilter i).1 q hqi
    exact ⟨q, hq, hqp, κ₀, hκ₀, (S.ground_mem_iff i η κ₀).mp hηκ,
      S.forces_mono hrK hq hqr⟩

end ClassForcingDensitySemantics
end ZFVP
