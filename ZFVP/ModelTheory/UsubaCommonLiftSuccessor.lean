import ZFVP.ModelTheory.UsubaCommonLiftInvariant
import ZFVP.ModelTheory.UsubaSelectedDecision
import ZFVP.ModelTheory.NormalizedUnionStrongerBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

set_option maxHeartbeats 800000 in
theorem usubaCommonLiftBoundAt_successor [Countable V] {θ i k p c d : V}
    [IsOrdinal θ] [IsOrdinal i] [IsOrdinal k]
    (hk : succ k ⊆ θ) (hi : i ∈ succ k)
    (f : ForcingName ((T).P i)) (hc : c ∈ (T).P θ) (hd : d ∈ (T).P i)
    (hdc : ⟨d, ((T).projection i θ) ‘ c⟩ₖ ∈ (T).R i)
    (hqnext : usubaQuotientBoundRec θ i p f.val (succ k) ∈ (T).P (succ k))
    (hnorm : IsUsubaBoundNormalizationAt θ i p f.val (succ k))
    (hselected : IsUsubaSelectedDecision θ i f.val c d)
    (hprev : IsUsubaCommonLiftBoundAt θ i p f.val c d k) :
    IsUsubaCommonLiftBoundAt θ i p f.val c d (succ k) := by
  have hik : i ⊆ k := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hi)
  have hks : k ⊆ succ k := IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k)
  let P := (T).P k
  let R := (T).R k
  let o := (T).top k
  let τ := (T).projection i k
  let E := (T).sectionMap i k
  let Q := usubaSaturatedPosetName P R
  let S := reverseInclusionOrderName P R Q
  let q := usubaQuotientBoundRec θ i p f.val k
  let ν := usubaBoundSuccessorTail θ i p f.val k
  let μ : ForcingName ((T).P i) :=
    ⟨usubaBoundCoordinateName θ i f.val (succ k), usubaBoundCoordinateName_isName _ _ _ _⟩
  have hR := (T).order k inferInstance
  have ho := (T).top_spec k inferInstance
  have hbaseR := (T).order i inferInstance
  have hbaseo := (T).top_spec i inferInstance
  have hsplit := (T).splitProjection hik
  have hiter := usubaSaturated_iterand hR ho
  have hPnext := usubaTower_P_succ k
  have hRnext := usubaTower_R_succ k
  have hcn := (T).projection_mem hk hc
  intro hij r hr hrq b hb hbr hbd
  obtain ⟨r₀, hr₀, σ, hσ, heqr, hrσ⟩ := (mem_twoStepConditions _ _ _ _ _).mp (hPnext ▸ hr)
  subst r
  let l := (usubaTowerLift i (succ k)) ‘ ⟨⟨r₀, σ⟩ₖ, b⟩ₖ
  let w := kpair.π₁ l
  have hl := usubaTowerLift_spec hij hr hb hbr
  have hwl : l = ⟨w, σ⟩ₖ := by
    dsimp only [l, w]
    rw [usubaTowerLift_successor_value hik hr hb]
    simp only [successorForcingLiftValue, twoStepStronger, kpair.π₁_kpair, kpair.π₂_kpair]
  have hw : w ∈ P := by
    have hh := (T).projection_mem hks hl.1
    rw [usubaTower_projection_first hl.1] at hh
    exact hh
  have hwr : ⟨w, r₀⟩ₖ ∈ R := by
    have hh := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp (hRnext ▸ hl.2.1)).2.2.1
    simpa only [kpair.π₁_kpair] using hh
  have hqp : ((T).projection k (succ k)) ‘
      (usubaQuotientBoundRec θ i p f.val (succ k)) = q := by
    rw [usubaTower_projection_first hqnext, usubaQuotientBoundRec_successor hi, kpair.π₁_kpair]
  have hwc : ⟨w, kpair.π₁ (((T).projection (succ k) θ) ‘ c)⟩ₖ ∈ R := by
    have hh := usubaCommonLift_project_le hk hi (mem_succ_self k) hc hd hdc hqnext
      hqp hprev hr hrq hb hbr hbd
    rw [usubaTower_projection_first hl.1] at hh
    have he := (T).projection_comp k (succ k) θ inferInstance inferInstance inferInstance hks hk c hc
    rw [usubaTower_projection_first hcn] at he
    exact he.symm ▸ hh
  have hwd : ⟨τ ‘ w, d⟩ₖ ∈ (T).R i := by
    have he : τ ‘ w = b := (usubaTower_projection_succ hik hl.1).symm.trans hl.2.2
    exact he.symm ▸ hbd
  have hn : q ∈ atomicEquality P R ν
      (forcingSelectedUnion P R o (twoStepNames Q ∅) (twoStepTailSelector P R Q ∅)
        (nameAction E μ.val)) := by
    have hh := hnorm hi (by rw [sUnion_succ_of_transitive])
    simpa only [sUnion_succ_of_transitive, usubaBoundSuccessorRawTail, usubaSelectedUnionName] using hh
  have hrq' : ⟨⟨r₀, σ⟩ₖ, ⟨q, ν⟩ₖ⟩ₖ ∈ twoStepOrder P R Q S ∅ := by
    rw [hRnext, usubaQuotientBoundRec_successor hi] at hrq
    exact hrq
  have hh := twoStepStronger_le_selected_of_normalization hbaseR hbaseo hR ho hsplit hiter μ
    hrq' (hPnext ▸ hcn) hw hwr hwc hd hwd hn ?_ ?_
  · change ⟨l, ((T).projection (succ k) θ) ‘ c⟩ₖ ∈ _
    rw [hRnext, hwl]
    exact hh
  · intro G hG hdG
    let A : ForcingContext V := ⟨_, _, _, G, hbaseR, hbaseo, hG⟩
    have hh := A.usubaCoordinate_selected hk rfl rfl rfl hc hselected hdG f rfl
    simpa only [hPnext] using hh
  · intro H hH _
    let C : ForcingContext V := ⟨P, R, o, H, hR, ho, hH⟩
    exact C.reverseOrderName_value ⟨Q, hiter.posetName⟩

end ZFVP
