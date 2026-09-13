import ZFVP.SetTheory.HODCantorTransport
import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.WellOrderingChoice
import ZFVP.SetTheory.FiniteCardinalArithmetic

/-! Two ingredients for reading off `ω₁` of the HOD class model.

The first works in any model of ZF: under Choice the Hartogs number of `ω` injects into the Cantor
space, because the Cantor space is well-orderable and uncountable.

The second identifies the Hartogs number of `ω` inside the HOD class model with a given ordinal `K`
of that model, from the two halves "every member of `K` is countable" and "`K` is not countable",
together with the transport lemmas that carry countability and ordinalhood from the class model to
the ambient model along the inclusion. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Characteristic functions inject the power set of `ω` into the Cantor space. -/
theorem power_omega_cardLE_cantorSpace : ℘ (ω : V) ≤# cantorSpace V := by
  refine cardLE_of_injective_map charFun (by definability) ?_ ?_
  · intro S hS
    exact charFun_mem_cantorSpace (mem_power_iff.mp hS)
  · intro S hS T hT h
    have hSω : S ⊆ (ω : V) := mem_power_iff.mp hS
    have hTω : T ⊆ (ω : V) := mem_power_iff.mp hT
    apply mem_ext
    intro k
    constructor
    · intro hk
      have h1 : (charFun S) ‘ k = succ ∅ := (charFun_value hSω (hSω k hk)).mpr hk
      rw [h] at h1
      exact (charFun_value hTω (hSω k hk)).mp h1
    · intro hk
      have h1 : (charFun T) ‘ k = succ ∅ := (charFun_value hTω (hTω k hk)).mpr hk
      rw [← h] at h1
      exact (charFun_value hSω (hTω k hk)).mp h1

/-- The Cantor space is uncountable. -/
theorem cantorSpace_not_countable : ¬IsInternallyCountable (cantorSpace V) := fun h ↦
  power_omega_not_countable (power_omega_cardLE_cantorSpace.trans h)

/-- Under Choice the Hartogs number of `ω` injects into the Cantor space. -/
theorem hartogs_omega_cardLE_cantorSpace (hAC : InternalChoice V) :
    hartogsNumber (ω : V) ≤# cantorSpace V := by
  have hwo : IsWellOrderable (cantorSpace V) := wellOrderable_of_internalChoice hAC _
  have heq : wellOrderedCardinal (cantorSpace V) ≋ cantorSpace V := wellOrderedCardinal_cardEQ hwo
  have hord : IsOrdinal (wellOrderedCardinal (cantorSpace V)) := (wellOrderedCardinal_initial hwo).1
  have hnot : ¬wellOrderedCardinal (cantorSpace V) ≤# (ω : V) := fun h ↦
    cantorSpace_not_countable (heq.2.trans h)
  exact (cardLE_of_subset (hartogsNumber_minimal hnot)).trans heq.1

/-- The injection of the previous theorem, written out. -/
theorem exists_injective_hartogs_cantorSpace (hAC : InternalChoice V) :
    ∃ f ∈ (cantorSpace V) ^ (hartogsNumber (ω : V)), Injective f :=
  hartogs_omega_cardLE_cantorSpace hAC

/-- An ordinal all of whose members are countable and which is itself uncountable is the Hartogs
number of `ω`. -/
theorem hartogsNumber_omega_eq_of_countable_below {K : V} [IsOrdinal K]
    (hbelow : ∀ a ∈ K, IsInternallyCountable a) (habove : ¬IsInternallyCountable K) :
    hartogsNumber (ω : V) = K := by
  rw [hartogsNumber_eq_iff]
  refine ⟨inferInstance, habove, ?_⟩
  intro β hβ hnot
  by_contra hsub
  have : IsOrdinal β := hβ
  rcases IsOrdinal.subset_or_supset (α := K) (β := β) with h | h
  · exact hsub h
  · rcases IsOrdinal.subset_iff.mp h with h' | h'
    · subst h'
      exact hsub (subset_refl _)
    · exact hnot (hbelow β h')

section

variable (Pf : SetTheorySemisentence 2) (p : V)
  [Nonempty (HODDom Pf p)] [(HODDom Pf p)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- If `K` is an ordinal of the HOD class model whose members are all countable there and which is
itself uncountable there, then `K` is the first uncountable ordinal of the class model. -/
theorem hod_hartogs_eq (K : HODDom Pf p) [IsOrdinal K]
    (hbelow : ∀ a ∈ K, IsInternallyCountable a) (habove : ¬IsInternallyCountable K) :
    hartogsNumber (ω : HODDom Pf p) = K :=
  hartogsNumber_omega_eq_of_countable_below hbelow habove

/-- Countability in the HOD class model gives countability in `V`. -/
theorem hod_cardLE_omega_of_val {A : HODDom Pf p} (h : A ≤# (ω : HODDom Pf p)) :
    A.val ≤# (ω : V) := by
  obtain ⟨f, hf, hinj⟩ := h
  refine ⟨f.val, ?_, (injective_val Pf p f).mpr hinj⟩
  rw [← val_omega Pf p]
  exact (mem_function_val Pf p f A (ω : HODDom Pf p)).mp hf

/-- Ordinals of the HOD class model are ordinals of `V`. -/
theorem hod_isOrdinal_val (x : HODDom Pf p) [hx : IsOrdinal x] : IsOrdinal x.val := by
  have h := (hodInclusion Pf p).bounded_defined isOrdinalFormula_bounded
    (fun v ↦ IsOrdinal (v 0)) (fun v ↦ IsOrdinal (v 0)) ![x]
  simp only [Matrix.cons_val_zero] at h
  exact h.mp hx

end

end ZFVP
