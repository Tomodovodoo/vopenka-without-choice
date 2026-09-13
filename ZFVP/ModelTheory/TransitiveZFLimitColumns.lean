import ZFVP.ModelTheory.RankForcingLimits

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingSectionValue_val (π E k p i : SetDomain U) :
    (forcingSectionValue π E k p i).val = forcingSectionValue π.val E.val k.val p.val i.val := by
  classical
  by_cases hi : i ∈ k
  · have hv : i.val ∈ k.val := hi
    simp only [forcingSectionValue, hi, hv, ↓reduceIte, value_val_total U, kpair_val U]
  · have hv : i.val ∉ k.val := hi
    simp only [forcingSectionValue, hi, hv, ↓reduceIte, value_val_total U, kpair_val U]

theorem forcingSectionThread_val (θ π E k p : SetDomain U) :
    (forcingSectionThread θ π E k p).val = forcingSectionThread θ.val π.val E.val k.val p.val := by
  unfold forcingSectionThread
  apply definableGraph_val U
  intro i _
  exact forcingSectionValue_val U π E k p i

theorem forcingThreadCoordinate_val (C i : SetDomain U) :
    (forcingThreadCoordinate C i).val = forcingThreadCoordinate C.val i.val := by
  unfold forcingThreadCoordinate
  apply definableGraph_val U
  intro f _
  exact value_val_total U f i

theorem forcingThreadSection_val (θ P π E i : SetDomain U) :
    (forcingThreadSection θ P π E i).val = forcingThreadSection θ.val P.val π.val E.val i.val := by
  unfold forcingThreadSection
  rw [← value_val_total U P i]
  apply definableGraph_val U
  intro p _
  exact forcingSectionThread_val U θ π E i p

theorem forcingLimitProjectionColumn_val (θ C : SetDomain U) :
    (forcingLimitProjectionColumn θ C).val = forcingLimitProjectionColumn θ.val C.val := by
  unfold forcingLimitProjectionColumn
  apply definableGraph_val U
  intro i _
  exact forcingThreadCoordinate_val U C i

theorem forcingLimitSectionColumn_val (θ P π E : SetDomain U) :
    (forcingLimitSectionColumn θ P π E).val = forcingLimitSectionColumn θ.val P.val π.val E.val := by
  unfold forcingLimitSectionColumn
  apply definableGraph_val U
  intro i _
  exact forcingThreadSection_val U θ P π E i

theorem forcingSpliceValue_val (π L f i b j : SetDomain U) :
    (forcingSpliceValue π L f i b j).val = forcingSpliceValue π.val L.val f.val i.val b.val j.val := by
  classical
  by_cases hj : j ∈ i
  · have hv : j.val ∈ i.val := hj
    simp only [forcingSpliceValue, hj, hv, ↓reduceIte, value_val_total U, kpair_val U]
  · have hv : j.val ∉ i.val := hj
    simp only [forcingSpliceValue, hj, hv, ↓reduceIte, value_val_total U, kpair_val U]

theorem forcingThreadSplice_val (θ π L f i b : SetDomain U) :
    (forcingThreadSplice θ π L f i b).val = forcingThreadSplice θ.val π.val L.val f.val i.val b.val := by
  unfold forcingThreadSplice
  apply definableGraph_val U
  intro j _
  exact forcingSpliceValue_val U π L f i b j

theorem forcingLimitLift_val (C A θ π L i : SetDomain U) :
    (forcingLimitLift C A θ π L i).val = forcingLimitLift C.val A.val θ.val π.val L.val i.val := by
  unfold forcingLimitLift
  rw [← prod_val U]
  apply definableGraph_val U
  intro z _
  rw [forcingThreadSplice_val U, kpair_first_val U, kpair_second_val U]

theorem forcingLimitLiftColumn_val (C θ P π L : SetDomain U) :
    (forcingLimitLiftColumn C θ P π L).val = forcingLimitLiftColumn C.val θ.val P.val π.val L.val := by
  unfold forcingLimitLiftColumn
  apply definableGraph_val U
  intro i _
  rw [forcingLimitLift_val U, value_val_total U]

theorem forcingCodeUniverse_val (s : SetDomain U) :
    (forcingCodeUniverse s).val = forcingCodeUniverse s.val := by
  simp only [forcingCodeUniverse, sUnion_val U, range_val U, forcingCodeP_val U]

theorem forcingThreadCode_val (θ s C : SetDomain U) :
    (forcingThreadCode θ s C).val = forcingThreadCode θ.val s.val C.val := by
  simp only [forcingThreadCode, forcingIterationCodeNext_val U, forcingThreadOrder_val U,
    forcingLimitProjectionColumn_val U, forcingLimitSectionColumn_val U, forcingLimitLiftColumn_val U,
    forcingSectionThread_val U, forcingCodeP_val U, forcingCodeR_val U, forcingCodeπ_val U,
    forcingCodeE_val U, forcingCodeL_val U, forcingCodet_val U, value_val_total U, empty_val U]

end TransitiveZF

theorem rank_forcingDirectCode_val {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
    [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hs : ∀ β ∈ ξ, succ β ∈ ξ) (θ s : SetDomain (hierarchy ξ)) :
    (forcingDirectCode θ s).val = forcingDirectCode θ.val s.val := by
  let := hierarchy_transitive ξ
  simp only [forcingDirectCode, TransitiveZF.forcingThreadCode_val, rank_forcingDirectLimit_val hs,
    TransitiveZF.forcingCodeP_val, TransitiveZF.forcingCodeπ_val, TransitiveZF.forcingCodeE_val,
    TransitiveZF.forcingCodeUniverse_val]

theorem rank_forcingInverseCode_val {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
    [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hs : ∀ β ∈ ξ, succ β ∈ ξ) (θ s : SetDomain (hierarchy ξ)) :
    (forcingInverseCode θ s).val = forcingInverseCode θ.val s.val := by
  let := hierarchy_transitive ξ
  simp only [forcingInverseCode, TransitiveZF.forcingThreadCode_val, rank_forcingInverseLimit_val hs,
    TransitiveZF.forcingCodeP_val, TransitiveZF.forcingCodeπ_val, TransitiveZF.forcingCodeUniverse_val]

end ZFVP
