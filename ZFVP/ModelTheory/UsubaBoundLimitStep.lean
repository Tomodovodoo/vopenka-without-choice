import ZFVP.ModelTheory.UsubaCommonLiftInduction
import ZFVP.ModelTheory.UsubaBoundCoordinates
import ZFVP.ModelTheory.QuotientLiftCompatibility

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

/-- At a full inverse limit, normalization at the earlier successors gives
one common lift below each selected source condition. -/
theorem usubaQuotientBoundAt_limit_normalized [Countable V] {θ i j p α : V}
    [IsOrdinal θ] [IsOrdinal i] [IsOrdinal j] [IsOrdinal α]
    (hi : i ∈ j) (hjθ : j ⊆ θ) (hs : j ≠ succ (⋃ˢ j)) (hp : p ∈ (T).P i)
    (f : ForcingName ((T).P i)) (hf : ForcesUsubaQuotientSequence θ i p f.val α)
    (hprev : ∀ k ∈ j, IsUsubaNormalizedQuotientBoundAt θ i p f.val α k) :
    IsUsubaNormalizedQuotientBoundAt θ i p f.val α j := by
  have hz : j ≠ ∅ := by intro he; exact not_mem_empty (he ▸ hi)
  have hij : i ⊆ j := IsOrdinal.toIsTransitive.transitive _ hi
  have hiθ : i ⊆ θ := subset_trans hij hjθ
  have hmem : ∀ k ∈ j, usubaQuotientBoundRec θ i p f.val k ∈ (T).P k :=
    fun k hk ↦ (hprev k hk).1.1
  have hhistory := usubaQuotientBoundHistory_inverse_condition hz hs hi hmem
  have hq : usubaQuotientBoundRec θ i p f.val j ∈ (T).P j := by
    rw [usubaQuotientBoundRec_limit hi hs]
    exact hhistory.1
  have hqproj : ((T).projection i j) ‘ (usubaQuotientBoundRec θ i p f.val j) = p := by
    rw [usubaQuotientBoundRec_limit hi hs]
    exact hhistory.2
  have hmemall : ∀ k ∈ succ j, usubaQuotientBoundRec θ i p f.val k ∈ (T).P k := by
    intro k hk
    rcases mem_succ_iff.mp hk with rfl | hk
    · exact hq
    · exact hmem k hk
  have hnormall : ∀ k ∈ succ j, IsUsubaBoundNormalizationAt θ i p f.val k := by
    intro k hk
    rcases mem_succ_iff.mp hk with rfl | hk
    · exact fun _ he ↦ False.elim (hs he)
    · exact (hprev k hk).2
  refine ⟨?_, fun _ he ↦ False.elim (hs he)⟩
  apply (usubaQuotientBoundAt_iff_generics hij hp f).mpr
  refine ⟨hq, ?_⟩
  intro G hG hpG
  let A := usubaStageContext i hG
  have hπ := (T).projection_function i j inferInstance inferInstance hij
  have hqG : A.check (usubaQuotientBoundRec θ i p f.val j) ∈
      A.projectionQuotient ((T).P j) ((T).projection i j) :=
    (A.check_mem_projectionQuotient_iff hπ).mpr ⟨hq, hqproj.symm ▸ hpG⟩
  refine ⟨hqG, ?_⟩
  intro a ha
  have hdesc := usubaQuotientSequence_semantics hiθ f hf hG hpG
  have hfun := mem_function_of_mem_function_of_subset hdesc.1 sep_subset
  have hva := function_value_mem hdesc.1 ha
  obtain ⟨c, hc, hac⟩ := (A.mem_check_iff _ _).mp (sep_subset _ hva)
  have hcG : ((T).projection i θ) ‘ c ∈ A.G :=
    ((A.check_mem_projectionQuotient_iff
      ((T).projection_function i θ inferInstance inferInstance hiθ)).mp (hac ▸ hva)).2
  have hco := usubaBoundCoordinate_at hjθ hG f hfun ha hc hac
  rw [hco]
  have hdj := usubaBoundCoordinate_descending hij hjθ hG f hdesc
  have htG : A.check (((T).projection j θ) ‘ c) ∈
      A.projectionQuotient ((T).P j) ((T).projection i j) := hco ▸ function_value_mem hdj.1 ha
  obtain ⟨d, hdG, hdc, hselected⟩ := A.exists_usubaSelectedDecision_below rfl rfl rfl f hfun ha hac hcG
  have hd : d ∈ (T).P i := A.generic.1.1 d hdG
  have hcommon := usubaCommonLiftBoundAt_all hjθ hi f hc hd hdc hmemall hnormall hselected
  apply A.projectionQuotient_separative_of_lift hπ
    (fun r hr b hb hbr ↦ usubaTowerLift_spec hij hr hb hbr) hqG htG hdG
  exact hcommon j (mem_succ_self j) hij

end ZFVP
