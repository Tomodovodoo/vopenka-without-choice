import ZFVP.ModelTheory.LevyProductLemma

/-! The product factorization `V[G] ≃ V[G_β][G ∩ Coll(ω,[β,κ))]` over the ground model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ : V} (β : V) [IsOrdinal β] (hβ : β ⊆ κ) {G : Set V}
  (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- The ground model inside the two-step extension `V[G_β][G ∩ Coll(ω,[β,κ))]`. -/
noncomputable def levyProductGround : MembershipEndExtension V (levyProductContext β hβ hG).Model :=
  (levySubContext β hβ hG).checkEmbedding.trans (levyProductContext β hβ hG).checkEmbedding

theorem levyProductGround_apply (x : V) :
    levyProductGround β hβ hG x = (levyProductContext β hβ hG).check ((levySubContext β hβ hG).check x) :=
  rfl

/-- The generic `G` recovered inside the two-step extension: conditions whose lower part lies in
`G_β` and whose upper part lies in the upper generic. -/
noncomputable def levyProductRecoveredGeneric : (levyProductContext β hβ hG).Model :=
  sep ((levyProductContext β hβ hG).check ((levySubContext β hβ hG).check (levyCollapse κ)))
    (fun x ↦ ((levyProductContext β hβ hG).check ((levySubContext β hβ hG).check (levyCutFunction κ β))) ‘ x ∈
        (levyProductContext β hβ hG).check (levySubContext β hβ hG).genericSet ∧
      ((levyProductContext β hβ hG).check ((levySubContext β hβ hG).check (levyUpperFunction κ β))) ‘ x ∈
        (levyProductContext β hβ hG).genericSet)
    (by definability)

theorem levyProductGround_mem_recovered_iff (p : V) :
    levyProductGround β hβ hG p ∈ levyProductRecoveredGeneric β hβ hG ↔ p ∈ G := by
  let C := levySubContext β hβ hG
  let Q := levyProductContext β hβ hG
  unfold levyProductRecoveredGeneric
  rw [levyProductGround_apply, mem_sep_iff, Q.check_mem_iff, C.check_mem_iff]
  constructor
  · rintro ⟨hp, hcut, hup⟩
    rw [Q.check_value (by rw [C.check_domain, levyCutFunction_domain]; exact (C.check_mem_iff _ _).mpr hp),
      C.check_value (by rw [levyCutFunction_domain]; exact hp), levyCutFunction_value hp,
      Q.check_mem_iff, C.check_mem_genericSet_iff] at hcut
    rw [Q.check_value (by rw [C.check_domain, levyUpperFunction_domain]; exact (C.check_mem_iff _ _).mpr hp),
      C.check_value (by rw [levyUpperFunction_domain]; exact hp), levyUpperFunction_value hp,
      Q.check_mem_genericSet_iff] at hup
    have hup' := (check_mem_levyProductGeneric_iff β hβ hG _).mp hup
    obtain ⟨r, hr, hr1, hr2⟩ := hG.1.2.2.2 _ hcut.1 _ hup'.1
    have h1 : levyCut β p ⊆ r := ((pair_mem_reverseInclusionOrder _ _ _).mp hr1).2.2
    have h2 : levyUpper β p ⊆ r := ((pair_mem_reverseInclusionOrder _ _ _).mp hr2).2.2
    refine hG.1.2.2.1 r hr p hp ((pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hG.1.1 r hr, hp, ?_⟩)
    intro z hz
    rw [← levyCut_union_levyUpper β p] at hz
    rcases mem_union_iff.mp hz with h | h
    · exact h1 z h
    · exact h2 z h
  · intro hpG
    have hp := hG.1.1 p hpG
    refine ⟨hp, ?_, ?_⟩
    · rw [Q.check_value (by rw [C.check_domain, levyCutFunction_domain]; exact (C.check_mem_iff _ _).mpr hp),
        C.check_value (by rw [levyCutFunction_domain]; exact hp), levyCutFunction_value hp,
        Q.check_mem_iff, C.check_mem_genericSet_iff]
      exact ⟨levyCut_mem_of_mem hG hpG, levyCut_mem hp⟩
    · rw [Q.check_value (by rw [C.check_domain, levyUpperFunction_domain]; exact (C.check_mem_iff _ _).mpr hp),
        C.check_value (by rw [levyUpperFunction_domain]; exact hp), levyUpperFunction_value hp,
        Q.check_mem_genericSet_iff]
      exact (check_mem_levyProductGeneric_iff β hβ hG _).mpr ⟨levyUpper_mem_of_mem hG hpG, levyUpper_mem_above hp⟩

/-- `V[G]` realized inside the two-step extension. -/
noncomputable def levyProductRealization :
    ForcingRealization (levyContext κ hG) (levyProductContext β hβ hG).Model where
  ground := levyProductGround β hβ hG
  genericSet := levyProductRecoveredGeneric β hβ hG
  generic_subset := fun x hx ↦ (mem_sep_iff.mp hx).1
  generic_mem := levyProductGround_mem_recovered_iff β hβ hG

/-- Names over the subcollapse are names over the whole collapse. -/
def levySubNameLift (τ : ForcingName (levySubContext β hβ hG).P) : ForcingName (levyContext κ hG).P :=
  ⟨τ.val, τ.property.mono (levyCollapse_mono hβ)⟩

theorem levyProductRecovered_inter_eq :
    levyProductRecoveredGeneric β hβ hG ∩
        (levyProductContext β hβ hG).check ((levySubContext β hβ hG).check (levyCollapse β)) =
      (levyProductContext β hβ hG).check (levySubContext β hβ hG).genericSet ∩
        (levyProductContext β hβ hG).check ((levySubContext β hβ hG).check (levyCollapse β)) := by
  let C := levySubContext β hβ hG
  let Q := levyProductContext β hβ hG
  ext z
  rw [mem_inter_iff, mem_inter_iff]
  constructor
  · rintro ⟨hz, hzC⟩
    refine ⟨?_, hzC⟩
    obtain ⟨y, hy, rfl⟩ := (Q.mem_check_iff _ _).mp hzC
    obtain ⟨p, hp, rfl⟩ := (C.mem_check_iff _ _).mp hy
    have hpG := (levyProductGround_mem_recovered_iff β hβ hG p).mp hz
    rw [Q.check_mem_iff, C.check_mem_genericSet_iff]
    exact ⟨hpG, hp⟩
  · rintro ⟨hz, hzC⟩
    refine ⟨?_, hzC⟩
    obtain ⟨y, hy, rfl⟩ := (Q.mem_check_iff _ _).mp hzC
    obtain ⟨p, _, rfl⟩ := (C.mem_check_iff _ _).mp hy
    rw [Q.check_mem_iff, C.check_mem_genericSet_iff] at hz
    exact (levyProductGround_mem_recovered_iff β hβ hG p).mpr hz.1

theorem levyProductRealization_value_lift (τ : ForcingName (levySubContext β hβ hG).P) :
    (levyProductRealization β hβ hG).value ((levyContext κ hG).ofName (levySubNameLift β hβ hG τ)) =
      (levyProductContext β hβ hG).check ((levySubContext β hβ hG).ofName τ) := by
  let C := levySubContext β hβ hG
  let Q := levyProductContext β hβ hG
  rw [ForcingRealization.value_ofName, ← C.nameValue_genericSet_check τ]
  change nameValue (levyProductRecoveredGeneric β hβ hG) (Q.check (C.check τ.val)) =
    Q.checkEmbedding (nameValue C.genericSet (C.check τ.val))
  rw [Q.checkEmbedding.map_nameValue]
  change nameValue (levyProductRecoveredGeneric β hβ hG) (Q.check (C.check τ.val)) =
    nameValue (Q.check C.genericSet) (Q.check (C.check τ.val))
  have hn : IsForcingName (Q.check (C.check (levyCollapse β))) (Q.check (C.check τ.val)) :=
    Q.checkEmbedding.map_forcingName (C.checkEmbedding.map_forcingName τ.property)
  rw [← nameValue_inter_of_name hn, levyProductRecovered_inter_eq β hβ hG, nameValue_inter_of_name hn]

theorem levyProductRealization_value_upperGeneric :
    (levyProductRealization β hβ hG).value
        ((levyContext κ hG).genericSet ∩ (levyContext κ hG).check (levyCollapseAbove κ β)) =
      (levyProductContext β hβ hG).genericSet := by
  let A := levyContext κ hG
  let Q := levyProductContext β hβ hG
  let L := levyProductRealization β hβ hG
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := L.value_endExtension _ hz
    obtain ⟨hxG, hxA⟩ := mem_inter_iff.mp hx
    obtain ⟨p, hp, rfl⟩ := (A.mem_genericSet_iff x).mp hxG
    have hpA : p ∈ levyCollapseAbove κ β := (A.check_mem_iff _ _).mp hxA
    rw [L.value_check]
    show Q.check ((levySubContext β hβ hG).check p) ∈ Q.genericSet
    rw [Q.check_mem_genericSet_iff]
    exact (check_mem_levyProductGeneric_iff β hβ hG p).mpr ⟨hp, hpA⟩
  · intro hz
    obtain ⟨y, hy, rfl⟩ := (Q.mem_genericSet_iff z).mp hz
    obtain ⟨p, hp, rfl⟩ := hy
    have hx : A.check p ∈ A.genericSet ∩ A.check (levyCollapseAbove κ β) :=
      mem_inter_iff.mpr ⟨(A.check_mem_genericSet_iff p).mpr hp.1, (A.check_mem_iff _ _).mpr hp.2⟩
    have := (L.value_mem_iff _ _).mpr hx
    rw [L.value_check] at this
    exact this

theorem levyProductRealization_surjective : Function.Surjective (levyProductRealization β hβ hG).value :=
  ForcingRealization.value_surjective_of_generators (levyProductContext β hβ hG)
    (levyProductRealization β hβ hG)
    (fun x ↦ by
      obtain ⟨τ, rfl⟩ := (levySubContext β hβ hG).ofName_surjective x
      exact ⟨_, levyProductRealization_value_lift β hβ hG τ⟩)
    ⟨_, levyProductRealization_value_upperGeneric β hβ hG⟩

/-- The product factorization `V[G] ≃ V[G_β][G ∩ Coll(ω,[β,κ))]`. -/
noncomputable def levyProductEquiv : (levyContext κ hG).Model ≃ (levyProductContext β hβ hG).Model :=
  Equiv.ofBijective (levyProductRealization β hβ hG).value
    ⟨(levyProductRealization β hβ hG).value_injective, levyProductRealization_surjective β hβ hG⟩

theorem levyProductEquiv_mem_iff (x y : (levyContext κ hG).Model) :
    levyProductEquiv β hβ hG x ∈ levyProductEquiv β hβ hG y ↔ x ∈ y :=
  (levyProductRealization β hβ hG).value_mem_iff x y

theorem levyProductEquiv_check (x : V) :
    levyProductEquiv β hβ hG ((levyContext κ hG).check x) =
      (levyProductContext β hβ hG).check ((levySubContext β hβ hG).check x) :=
  (levyProductRealization β hβ hG).value_check x

theorem levyProductEquiv_lift (τ : ForcingName (levySubContext β hβ hG).P) :
    levyProductEquiv β hβ hG ((levyContext κ hG).ofName (levySubNameLift β hβ hG τ)) =
      (levyProductContext β hβ hG).check ((levySubContext β hβ hG).ofName τ) :=
  levyProductRealization_value_lift β hβ hG τ

end

end ZFVP
