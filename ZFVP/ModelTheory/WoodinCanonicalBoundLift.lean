import ZFVP.ModelTheory.ForcingLimitCode
import ZFVP.ModelTheory.InverseCollapseCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The stronger-lift function of `forcingInverseCode θ s` from the old coordinate `i`
to the new coordinate `θ`. -/
noncomputable def woodinInverseCodeLift (θ s i : V) : V :=
  (forcingCodeL (forcingInverseCode θ s)) ‘ ⟨i, θ⟩ₖ

/-- The new lift column is the limit lift built from the data of `s`. -/
theorem woodinInverseCodeLift_eq {θ s i : V} (hi : i ∈ θ) :
    woodinInverseCodeLift θ s i =
      forcingLimitLift (forcingInverseCodePoset θ s) ((forcingCodeP s) ‘ i) θ
        (forcingCodeπ s) (forcingCodeL s) i := by
  simp only [woodinInverseCodeLift, forcingInverseCode, forcingThreadCode,
    forcingIterationCodeNext, forcingCodeL_code, forcingMatrixNext_column hi,
    forcingLimitLiftColumn_value hi, forcingInverseCodePoset]

/-- Pointwise description of the order on the new coordinate. This is
`forcingThreadOrder θ (forcingCodeR s) (forcingInverseCodePoset θ s)` unfolded. -/
theorem mem_forcingInverseCodeOrder_iff {θ s c d : V} [IsOrdinal θ] :
    ⟨c, d⟩ₖ ∈ forcingInverseCodeOrder θ s ↔
      c ∈ forcingInverseCodePoset θ s ∧ d ∈ forcingInverseCodePoset θ s ∧
      ∀ j ∈ θ, ⟨c ‘ j, d ‘ j⟩ₖ ∈ (forcingCodeR s) ‘ j :=
  mem_forcingThreadOrder_iff _ _ _ _ _

/-- The lift data at the new coordinate, in the shape consumed by
`ForcingContext.projectionQuotient_separative_of_lift`. -/
theorem woodinInverseCodeLift_spec {θ s i : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ) (hi : i ∈ θ) :
    ∀ r ∈ forcingInverseCodePoset θ s, ∀ b ∈ (forcingCodeP s) ‘ i,
      ⟨b, (forcingThreadCoordinate (forcingInverseCodePoset θ s) i) ‘ r⟩ₖ ∈ (forcingCodeR s) ‘ i →
      (woodinInverseCodeLift θ s i) ‘ ⟨r, b⟩ₖ ∈ forcingInverseCodePoset θ s ∧
      ⟨(woodinInverseCodeLift θ s i) ‘ ⟨r, b⟩ₖ, r⟩ₖ ∈ forcingInverseCodeOrder θ s ∧
      (forcingThreadCoordinate (forcingInverseCodePoset θ s) i) ‘
        ((woodinInverseCodeLift θ s i) ‘ ⟨r, b⟩ₖ) = b := by
  intro r hr b hb hle
  let := IsOrdinal.of_mem hi
  rw [forcingThreadCoordinate_value hr] at hle
  have hπ : ∀ j ∈ i, ∀ p ∈ (forcingCodeP s) ‘ i, ∀ q ∈ (forcingCodeP s) ‘ i,
      ⟨p, q⟩ₖ ∈ (forcingCodeR s) ‘ i →
      ⟨((forcingCodeπ s) ‘ ⟨j, i⟩ₖ) ‘ p, ((forcingCodeπ s) ‘ ⟨j, i⟩ₖ) ‘ q⟩ₖ ∈
        (forcingCodeR s) ‘ j := by
    intro j hj p hp q hq hpq
    exact h.system.order.projMono j (IsOrdinal.toIsTransitive.mem_trans hj hi) i hi
      (IsOrdinal.toIsTransitive.transitive _ hj) p hp q hq hpq
  obtain ⟨k1, k2, k3⟩ := forcingLimitLift_inverse_lift (E := forcingCodeE s)
    h.system.split h.system.lifts hr hi hb hle h.subset_universe hπ
  rw [woodinInverseCodeLift_eq hi]
  exact ⟨k1, k2, (forcingThreadCoordinate_value k1).trans k3⟩

/-- Value of the lift at a coordinate `j` above `i`. -/
theorem woodinInverseCodeLift_value_of_le {θ s i j r b : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ) (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    (hr : r ∈ forcingInverseCodePoset θ s) (hb : b ∈ (forcingCodeP s) ‘ i) :
    ((woodinInverseCodeLift θ s i) ‘ ⟨r, b⟩ₖ) ‘ j =
      ((forcingCodeL s) ‘ ⟨i, j⟩ₖ) ‘ ⟨r ‘ j, b⟩ₖ := by
  rw [woodinInverseCodeLift_eq hi, forcingLimitLift_commute hr hb hj hij]

/-- Value of the lift at a coordinate `j` below `i`. -/
theorem woodinInverseCodeLift_value_of_mem {θ s i j r b : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ) (hi : i ∈ θ) (hj : j ∈ i)
    (hr : r ∈ forcingInverseCodePoset θ s) (hb : b ∈ (forcingCodeP s) ‘ i) :
    ((woodinInverseCodeLift θ s i) ‘ ⟨r, b⟩ₖ) ‘ j = ((forcingCodeπ s) ‘ ⟨j, i⟩ₖ) ‘ b := by
  classical
  rw [woodinInverseCodeLift_eq hi, forcingLimitLift_value hr hb,
    forcingThreadSplice_value (IsOrdinal.toIsTransitive.mem_trans hj hi)]
  simp only [forcingSpliceValue, hj, ↓reduceIte]

end ZFVP
