import ZFVP.ModelTheory.ExternalGenericRestriction
import ZFVP.ModelTheory.TransitiveZFSymmetry
import ZFVP.ModelTheory.CodedMembershipEmbedding
import ZFVP.SetTheory.ElementaryForcing
import ZFVP.SetTheory.NameMapGraph
import ZFVP.SetTheory.NameActionBounds

/-! The hypotheses for the symmetric graph name follow from an elementary ground embedding. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameAction_mem (P : SetDomain U) {π τ : V} (hπ : π ∈ U) (hτ : τ ∈ U)
    (hn : IsForcingName P.val τ) : nameAction π τ ∈ U := by
  let π' : SetDomain U := ⟨π, hπ⟩
  let τ' : SetDomain U := ⟨τ, hτ⟩
  have h := (nameAction π' τ').property
  rw [nameAction_val U P π' τ' ((forcingName_iff U P τ').mpr hn)] at h
  exact h

theorem symmetricNameDomain_permuted (P Γ F : SetDomain U) {R π : V}
    (hΓ : IsForcingAutomorphismGroup P.val R Γ.val)
    (hF : IsNormalSubgroupFilter P.val Γ.val F.val) (hπ : π ∈ Γ.val) (ν : V) :
    ν ∈ {τ ∈ U ; IsHereditarilySymmetricName P.val Γ.val F.val τ} ↔
      ∃ σ ∈ {τ ∈ U ; IsHereditarilySymmetricName P.val Γ.val F.val τ}, ν = nameAction π σ := by
  constructor
  · intro hν
    obtain ⟨hνU, hνHS⟩ := mem_sep_iff.mp hν
    have hi := hΓ.2.2.2 π hπ
    have hiU := (inferInstance : IsTransitive U).mem_trans hi Γ.property
    refine ⟨nameAction (converseGraph π) ν, mem_sep_iff.mpr ⟨nameAction_mem U P hiU hνU hνHS.1,
      hereditarilySymmetric_nameAction hΓ hF hi hνHS⟩, ?_⟩
    exact (nameAction_cancel_inverse (hΓ.1 π hπ) hνHS.1).symm
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨hσU, hσHS⟩ := mem_sep_iff.mp hσ
    exact mem_sep_iff.mpr ⟨nameAction_mem U P
      ((inferInstance : IsTransitive U).mem_trans hπ Γ.property) hσU hσHS.1,
      hereditarilySymmetric_nameAction hΓ hF hπ hσHS⟩

end TransitiveZF

namespace IsCodedMembershipEmbedding

variable {U W f : V} [IsTransitive U] [IsTransitive W]
variable [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
variable [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem preserves_forcingName (h : IsCodedMembershipEmbedding U W f) (P τ : SetDomain U)
    (hP : f ‘ P.val = P.val) (hτ : IsForcingName P.val τ.val) :
    IsForcingName P.val (f ‘ τ.val) := by
  have hh := (h.toElementaryMap.forcingName_iff P τ).mp ((TransitiveZF.forcingName_iff U P τ).mpr hτ)
  have hr := (TransitiveZF.forcingName_iff W (h.toFunction P) (h.toFunction τ)).mp hh
  change IsForcingName (f ‘ P.val) (f ‘ τ.val) at hr
  simpa only [hP] using hr

theorem preserves_hereditarilySymmetricName (h : IsCodedMembershipEmbedding U W f)
    (P Γ F τ : SetDomain U) (hP : f ‘ P.val = P.val) (hΓ : f ‘ Γ.val = Γ.val)
    (hF : f ‘ F.val = F.val) (hτ : IsHereditarilySymmetricName P.val Γ.val F.val τ.val) :
    IsHereditarilySymmetricName P.val Γ.val F.val (f ‘ τ.val) := by
  have hh := (h.toElementaryMap.hereditarilySymmetricName_iff P Γ F τ).mp
    ((TransitiveZF.hereditarilySymmetricName_iff U P Γ F τ).mpr hτ)
  have hr := (TransitiveZF.hereditarilySymmetricName_iff W
    (h.toFunction P) (h.toFunction Γ) (h.toFunction F) (h.toFunction τ)).mp hh
  change IsHereditarilySymmetricName (f ‘ P.val) (f ‘ Γ.val) (f ‘ F.val) (f ‘ τ.val) at hr
  simpa only [hP, hΓ, hF] using hr

theorem nameAction_equivariant (h : IsCodedMembershipEmbedding U W f)
    (P π τ : SetDomain U) (hτ : IsForcingName P.val τ.val) (hπ : f ‘ π.val = π.val) :
    f ‘ (nameAction π.val τ.val) = nameAction π.val (f ‘ τ.val) := by
  have hn := (TransitiveZF.forcingName_iff U P τ).mpr hτ
  have hn' := (h.toElementaryMap.forcingName_iff P τ).mp hn
  have he := congrArg Subtype.val (h.toElementaryMap.map_nameAction π τ)
  change f ‘ (nameAction π τ).val = (nameAction (h.toFunction π) (h.toFunction τ)).val at he
  rw [TransitiveZF.nameAction_val U P π τ hn,
    TransitiveZF.nameAction_val W (h.toFunction P) (h.toFunction π) (h.toFunction τ) hn'] at he
  change f ‘ (nameAction π.val τ.val) = nameAction (f ‘ π.val) (f ‘ τ.val) at he
  simpa only [hπ] using he

theorem genericMeets_atomicEquality_map (h : IsCodedMembershipEmbedding U W f)
    (P R σ τ : SetDomain U) (G : Set V) (hP : f ‘ P.val = P.val) (hR : f ‘ R.val = R.val)
    (hfix : ∀ p ∈ G, f ‘ p = p)
    (he : GenericMeets G (atomicEquality P.val R.val σ.val τ.val)) :
    GenericMeets G (atomicEquality P.val R.val (f ‘ σ.val) (f ‘ τ.val)) := by
  obtain ⟨p, hpG, hpE⟩ := (TransitiveZF.genericMeets_atomicEquality_restrict_iff U P R σ τ G).mpr he
  have hm := (h.toElementaryMap.map_mem_iff p (atomicEquality P R σ τ)).mpr hpE
  rw [h.toElementaryMap.map_atomicEquality] at hm
  have htarget : GenericMeets {q : SetDomain W | q.val ∈ G}
      (atomicEquality (h.toFunction P) (h.toFunction R) (h.toFunction σ) (h.toFunction τ)) :=
    ⟨h.toFunction p, (by change f ‘ p.val ∈ G; rw [hfix p.val hpG]; exact hpG), hm⟩
  have ht := (TransitiveZF.genericMeets_atomicEquality_restrict_iff W
    (h.toFunction P) (h.toFunction R) (h.toFunction σ) (h.toFunction τ) G).mp htarget
  change GenericMeets G (atomicEquality (f ‘ P.val) (f ‘ R.val) (f ‘ σ.val) (f ‘ τ.val)) at ht
  simpa only [hP, hR] using ht

theorem symmetric_graphName (h : IsCodedMembershipEmbedding U W f)
    (P Γ F : SetDomain U) {R one : V} (hR : IsForcingPoset P.val R)
    (hΓ : IsForcingAutomorphismGroup P.val R Γ.val) (hF : IsNormalSubgroupFilter P.val Γ.val F.val)
    (hone : IsForcingTop P.val R one) (hfixP : f ‘ P.val = P.val)
    (hfixΓ : f ‘ Γ.val = Γ.val) (hfixF : f ‘ F.val = F.val)
    (hfix : ∀ π ∈ Γ.val, f ‘ π = π) :
    IsHereditarilySymmetricName P.val Γ.val F.val
      (nameMapGraph one {τ ∈ U ; IsHereditarilySymmetricName P.val Γ.val F.val τ} f) := by
  apply hereditarilySymmetric_nameMapGraph hR hΓ hF hone
  · intro σ hσ
    exact (mem_sep_iff.mp hσ).2
  · intro σ hσ
    obtain ⟨hσU, hσHS⟩ := mem_sep_iff.mp hσ
    exact h.preserves_hereditarilySymmetricName P Γ F ⟨σ, hσU⟩ hfixP hfixΓ hfixF hσHS
  · exact fun π hπ ν ↦ TransitiveZF.symmetricNameDomain_permuted U P Γ F hΓ hF hπ ν
  · intro π hπ σ hσ
    obtain ⟨hσU, hσHS⟩ := mem_sep_iff.mp hσ
    exact h.nameAction_equivariant P
      ⟨π, (inferInstance : IsTransitive U).mem_trans hπ Γ.property⟩ ⟨σ, hσU⟩ hσHS.1 (hfix π hπ)

end IsCodedMembershipEmbedding
end ZFVP
