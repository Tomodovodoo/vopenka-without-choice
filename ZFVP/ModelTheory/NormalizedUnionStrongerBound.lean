import ZFVP.ModelTheory.TwoStepTailInclusionOrder
import ZFVP.ModelTheory.ProjectionNameTransport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem twoStepStronger_le_selected_of_normalization_of_names [Countable V]
    {B R ob T U ot π E Q S t d r q w c σ ν : V}
    (hR : IsForcingPreorder B R) (hob : IsForcingTop B R ob)
    (hU : IsForcingPreorder T U) (hot : IsForcingTop T U ot)
    (hπ : IsForcingSplitProjection B R T U π E) (hQ : IsForcingName T Q) (hSN : IsForcingName T S)
    (hN : ∀ ν ∈ twoStepNames Q t, IsForcingName T ν)
    (f : ForcingName B)
    (hrq : ⟨⟨r, σ⟩ₖ, ⟨q, ν⟩ₖ⟩ₖ ∈ twoStepOrder T U Q S t)
    (hc : c ∈ twoStepConditions T U Q t) (_hw : w ∈ T)
    (hwσ : ⟨w, σ⟩ₖ ∈ twoStepConditions T U Q t)
    (hwr : ⟨w, r⟩ₖ ∈ U) (hwc : ⟨w, kpair.π₁ c⟩ₖ ∈ U)
    (hd : d ∈ B) (hwd : ⟨π ‘ w, d⟩ₖ ∈ R)
    (hn : q ∈ atomicEquality T U ν
      (forcingSelectedUnion T U ot (twoStepNames Q t) (twoStepTailSelector T U Q t) (nameAction E f.val)))
    (hselected : ∀ (G : Set V) (hG : IsExternalForcingGeneric B R G), d ∈ G →
      let A : ForcingContext V := ⟨B, R, ob, G, hR, hob, hG⟩
      ∃ X a : A.Model, A.ofName f ∈ A.check (twoStepConditions T U Q t) ^ X ∧
        a ∈ X ∧ (A.ofName f) ‘ a = A.check c)
    (horder : ∀ (H : Set V) (hH : IsExternalForcingGeneric T U H), w ∈ H →
      let C : ForcingContext V := ⟨T, U, ot, H, hU, hot, hH⟩
      C.ofName ⟨S, hSN⟩ = reverseInclusionOrder (C.ofName ⟨Q, hQ⟩)) :
    ⟨⟨w, σ⟩ₖ, c⟩ₖ ∈ twoStepOrder T U Q S t := by
  obtain ⟨r', hr', τ, hτ, rfl, hcτ⟩ := (mem_twoStepConditions _ _ _ _ _).mp hc
  simp only [kpair.π₁_kpair] at hwc
  have hr := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hrq).1
  have hq := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hrq).2.1
  have hc : ⟨r', τ⟩ₖ ∈ twoStepConditions T U Q t :=
    (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hr', hτ, hcτ⟩
  apply twoStep_order_of_tail_inclusion_of_names hU hot hQ hSN hN hwσ hc hwc
  intro H hH hwH
  let C : ForcingContext V := ⟨T, U, ot, H, hU, hot, hH⟩
  let A : ForcingContext V := ⟨B, R, ob, forcingProjectionGeneric B R π H,
    hR, hob, hπ.projection.generic hR hH⟩
  have hdG : d ∈ A.G := A.generic.1.2.2.1 _ (hπ.projection.image_mem hR hH.1 hwH) d hd hwd
  obtain ⟨X, a, hf, ha, hac⟩ := hselected A.G A.generic hdG
  let e := A.projectionInclusion C hπ rfl
  let g : ForcingName T := ⟨nameAction E f.val, nameAction_isName hπ.maps f.property⟩
  have hg : C.ofName g ∈ C.check (twoStepConditions T U Q t) ^ e X := by
    rw [A.projectionInclusion_nameAction C hπ rfl f]
    have hh := (e.function_iff (A.ofName f) X (A.check (twoStepConditions T U Q t))).mpr hf
    rwa [A.projectionInclusion_check C hπ rfl] at hh
  have hea : e a ∈ e X := (e.mem_iff a X).mpr ha
  have hec : (C.ofName g) ‘ (e a) = C.check ⟨r', τ⟩ₖ := by
    rw [A.projectionInclusion_nameAction C hπ rfl f, ← e.map_value_total, hac,
      A.projectionInclusion_check C hπ rfl]
  have hrP := ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp hr).1
  have hqP := ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp hq).1
  have hrH : r ∈ H := hH.1.2.2.1 w hwH r hrP hwr
  have hrq' : ⟨r, q⟩ₖ ∈ U := by
    simpa only [kpair.π₁_kpair] using ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hrq).2.2.1
  have hqH : q ∈ H := hH.1.2.2.1 r hrH q hqP hrq'
  let ν' : ForcingName T := ⟨ν, hN _ ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp hq).2.1⟩
  let σ' : ForcingName T := ⟨σ, hN _ ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp hr).2.1⟩
  have hτν : C.ofName ⟨τ, hN _ hτ⟩ ⊆ C.ofName ν' := by
    have hh := C.selectedName_subset_normalizedUnion hN
      (twoStepTailSelector_maps T U Q t) g ν' hg hea hc hec hqH hn
    simpa only [twoStepTailSelector_value hc, kpair.π₂_kpair] using hh
  have hσν : ⟨C.ofName σ', C.ofName ν'⟩ₖ ∈ C.ofName ⟨S, hSN⟩ := by
    apply C.ofName_pair_mem_of_forced ⟨S, hSN⟩ σ' ν' hrH
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
      ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hrq).2.2.2
  have hS := horder H hH hwH
  rw [hS] at hσν
  exact ⟨hS, subset_trans hτν ((pair_mem_reverseInclusionOrder _ _ _).mp hσν).2.2⟩

theorem twoStepStronger_le_selected_of_normalization [Countable V]
    {B R ob T U ot π E Q S t d r q w c σ ν : V}
    (hR : IsForcingPreorder B R) (hob : IsForcingTop B R ob)
    (hU : IsForcingPreorder T U) (hot : IsForcingTop T U ot)
    (hπ : IsForcingSplitProjection B R T U π E) (h : IsForcingIterand T U Q S t)
    (f : ForcingName B)
    (hrq : ⟨⟨r, σ⟩ₖ, ⟨q, ν⟩ₖ⟩ₖ ∈ twoStepOrder T U Q S t)
    (hc : c ∈ twoStepConditions T U Q t) (hw : w ∈ T)
    (hwr : ⟨w, r⟩ₖ ∈ U) (hwc : ⟨w, kpair.π₁ c⟩ₖ ∈ U)
    (hd : d ∈ B) (hwd : ⟨π ‘ w, d⟩ₖ ∈ R)
    (hn : q ∈ atomicEquality T U ν
      (forcingSelectedUnion T U ot (twoStepNames Q t) (twoStepTailSelector T U Q t) (nameAction E f.val)))
    (hselected : ∀ (G : Set V) (hG : IsExternalForcingGeneric B R G), d ∈ G →
      let A : ForcingContext V := ⟨B, R, ob, G, hR, hob, hG⟩
      ∃ X a : A.Model, A.ofName f ∈ A.check (twoStepConditions T U Q t) ^ X ∧
        a ∈ X ∧ (A.ofName f) ‘ a = A.check c)
    (horder : ∀ (H : Set V) (hH : IsExternalForcingGeneric T U H), w ∈ H →
      let C : ForcingContext V := ⟨T, U, ot, H, hU, hot, hH⟩
      C.ofName ⟨S, h.orderName⟩ = reverseInclusionOrder (C.ofName ⟨Q, h.posetName⟩)) :
    ⟨⟨w, σ⟩ₖ, c⟩ₖ ∈ twoStepOrder T U Q S t := by
  have hr := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hrq).1
  have hwσ : ⟨w, σ⟩ₖ ∈ twoStepConditions T U Q t := by
    simpa only [twoStepStronger, kpair.π₂_kpair] using
      (twoStepStronger_lift hU hot h hr hw (by simpa only [kpair.π₁_kpair] using hwr)).1
  exact twoStepStronger_le_selected_of_normalization_of_names hR hob hU hot hπ
    h.posetName h.orderName (fun _ hν ↦ h.name hν) f hrq hc hw hwσ hwr hwc hd hwd hn hselected horder

end ZFVP
