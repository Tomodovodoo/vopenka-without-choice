import ZFVP.ModelTheory.SchmerlCodedFunctionCandidateSemantics
import ZFVP.ModelTheory.SchmerlCodedDeadEndSemantics

/-! A single actual binary color graph extends every component coloring to
the whole carrier. Its rows have one common internally countable cover. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedFunctionColorValue (I T c H s x : V) : V := by
  classical
  exact if s ∈ I then codedClassColorValue (T ‘ s) c (H ‘ s) x else c ‘ (0 : V)

instance codedFunctionColorValue_definable (I T c H : V) :
    ℒₛₑₜ-function₂[V] (codedFunctionColorValue I T c H) := by
  have h : ℒₛₑₜ-relation₃[V] (fun y s x ↦
    (s ∈ I ∧ x ∈ T ‘ s ∧ y = c ‘ ((H ‘ s) ‘ x)) ∨
      ((s ∉ I ∨ x ∉ T ‘ s) ∧ y = c ‘ (0 : V))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = codedFunctionColorValue I T c H (v 1) (v 2) ↔ _
  unfold codedFunctionColorValue codedClassColorValue
  split_ifs <;> simp_all

noncomputable def codedFunctionColorGraph (D I T c H : V) : V :=
  definableGraph (D ×ˢ D) (fun p ↦ codedFunctionColorValue I T c H (kpair.π₁ p) (kpair.π₂ p)) (by definability)

noncomputable def codedFunctionColorRow (D I T c H s : V) : V :=
  definableGraph D (codedFunctionColorValue I T c H s) (by definability)

theorem codedFunctionColorGraph_value {D I T c H s x : V} (hs : s ∈ D) (hx : x ∈ D) :
    (codedFunctionColorGraph D I T c H) ‘ ⟨s, x⟩ₖ = codedFunctionColorValue I T c H s x := by
  rw [codedFunctionColorGraph, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hs, hx⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

theorem codedFunctionColorRow_value {D I T c H s x : V} (hx : x ∈ D) :
    (codedFunctionColorRow D I T c H s) ‘ x = codedFunctionColorValue I T c H s x :=
  value_definableGraph _ _ _ hx

theorem codedFunctionColorValue_in_cover {I T c H : V}
    (hH : ∀ s ∈ I, H ‘ s ∈ (ω : V) ^ (T ‘ s)) (s x : V) :
    codedFunctionColorValue I T c H s x ∈ repl (fun n : V ↦ c ‘ n) (by definability) (ω : V) := by
  unfold codedFunctionColorValue codedClassColorValue
  split_ifs with hs hx
  · exact (repl_spec (by definability)).mpr ⟨(H ‘ s) ‘ x, function_value_mem (hH s hs) hx, rfl⟩
  · exact (repl_spec (by definability)).mpr ⟨0, by simp, rfl⟩
  · exact (repl_spec (by definability)).mpr ⟨0, by simp, rfl⟩

end ZFVP.Schmerl

namespace ZFVP.BinaryRelationRepresentation
open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W]
variable (R : BinaryRelationRepresentation (V := V) W)
variable {I T c H : V}
variable (hc : IsInternalCofinalStrictChain (hartogsNumber (ω : V))
  (codedOrdinals R.code) (codedOrdinalOrder R.code) c)
variable (hH : ∀ s ∈ I, H ‘ s ∈ (ω : V) ^ (T ‘ s))

include hc hH

theorem codedFunctionColorValue_mem (s x : V) : codedFunctionColorValue I T c H s x ∈ R.carrier := by
  obtain ⟨n, hn, he⟩ := (repl_spec (by definability)).mp (codedFunctionColorValue_in_cover (c := c) hH s x)
  rw [he]
  have hnO := function_value_mem hc.1 (IsOrdinal.toIsTransitive.mem_trans hn omega_mem_hartogs_omega)
  obtain ⟨a, ha⟩ := (R.mem_ordinals_iff _).mp hnO
  rw [← ha]
  exact (R.equiv a.val).property

theorem codedFunctionColorGraph_function :
    codedFunctionColorGraph R.carrier I T c H ∈ R.carrier ^ (R.carrier ×ˢ R.carrier) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ _ ↦ R.codedFunctionColorValue_mem hc hH _ _)

theorem codedFunctionColorRow_function (s : V) :
    codedFunctionColorRow R.carrier I T c H s ∈ R.carrier ^ R.carrier :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun x _ ↦ R.codedFunctionColorValue_mem hc hH s x)

theorem representedFunctionColor_eq_row (s x : W) :
    R.representedFunctionColor (R.codedFunctionColorGraph_function hc hH) s x =
      R.representedColor (R.codedFunctionColorRow_function hc hH (R.equiv s).val) x := by
  apply R.equiv_val_injective
  dsimp only
  rw [R.representedFunctionColor_val, R.representedColor_val,
    codedFunctionColorGraph_value (R.equiv s).property (R.equiv x).property,
    codedFunctionColorRow_value (R.equiv x).property]

theorem codedFunctionColorRow_not_Q (s : V) :
    ¬R.representedQ (Set.range (R.representedColor (R.codedFunctionColorRow_function hc hH s))) := by
  intro hQ
  apply hQ
  refine ⟨repl (fun n : V ↦ c ‘ n) (by definability) (ω : V),
    internallyCountable_repl _ _ internallyCountable_omega, ?_⟩
  rintro y ⟨x, rfl⟩
  rw [R.representedColor_val, codedFunctionColorRow_value (R.equiv x).property]
  exact codedFunctionColorValue_in_cover hH s (R.equiv x).val

theorem codedFunctionColorRow_internalWeak {s S : V} (hs : s ∈ I)
    (hTD : T ‘ s ⊆ R.carrier) (hweak : InternallyWeakSpecialization (T ‘ s) S (H ‘ s)) :
    InternallyWeakSpecialization (T ‘ s) S (codedFunctionColorRow R.carrier I T c H s) := by
  intro x hx y hy z hz hxy hxz hexy hexz
  have he {a b : V} (ha : a ∈ T ‘ s) (hb : b ∈ T ‘ s)
      (hab : (codedFunctionColorRow R.carrier I T c H s) ‘ a =
        (codedFunctionColorRow R.carrier I T c H s) ‘ b) : (H ‘ s) ‘ a = (H ‘ s) ‘ b := by
    rw [codedFunctionColorRow_value (hTD a ha), codedFunctionColorRow_value (hTD b hb)] at hab
    simp only [codedFunctionColorValue, codedClassColorValue, hs, ha, hb, ite_true] at hab
    exact hc.value_injective
      (IsOrdinal.toIsTransitive.mem_trans (function_value_mem (hH s hs) ha) omega_mem_hartogs_omega)
      (IsOrdinal.toIsTransitive.mem_trans (function_value_mem (hH s hs) hb) omega_mem_hartogs_omega) hab
  exact hweak x hx y hy z hz hxy hxz (he hx hy hexy) (he hx hz hexz)

end ZFVP.BinaryRelationRepresentation
