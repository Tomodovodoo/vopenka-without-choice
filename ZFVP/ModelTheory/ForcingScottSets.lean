import ZFVP.ModelTheory.TransitiveZFScottSets
import ZFVP.ModelTheory.TransitiveZFAtomicForcing
import ZFVP.ModelTheory.TransitiveZFForcingOrders
import ZFVP.SetTheory.AtomicEqualityTransitivity

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def ForcingScottRelated (P R p σ τ : V) : Prop :=
  IsForcingName P τ ∧ p ∈ atomicEquality P R σ τ

instance forcingScottRelated_definable (P R p : V) : ℒₛₑₜ-relation[V] (ForcingScottRelated P R p) := by
  unfold ForcingScottRelated
  definability

theorem forcingScottSet_exists {U : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (P R p σ : SetDomain U) (hR : IsForcingPreorder P.val R.val)
    (hp : p.val ∈ P.val) (hσ : IsForcingName P.val σ.val) :
    ∃ X : V, IsLocalScottSet U (ForcingScottRelated P.val R.val p.val) σ.val X := by
  refine transitiveZF_localScottSet_exists (ForcingScottRelated P R p) (by infer_instance)
    (ForcingScottRelated P.val R.val p.val) ?_ σ ?_
  · intro x y
    unfold ForcingScottRelated
    rw [TransitiveZF.forcingName_iff U P y]
    apply and_congr_right
    intro _
    change p.val ∈ (atomicEquality P R x y).val ↔ _
    rw [TransitiveZF.atomicEquality_val U]
  · refine ⟨σ, (TransitiveZF.forcingName_iff U P σ).mpr hσ, ?_⟩
    rw [atomicEquality_refl ((TransitiveZF.forcingPreorder_iff U P R).mpr hR)]
    exact hp

theorem forcingScottSet_eq {U P R p σ τ X Y : V} [IsTransitive U]
    (hR : IsForcingPreorder P R) (he : p ∈ atomicEquality P R σ τ)
    (hX : IsLocalScottSet U (ForcingScottRelated P R p) σ X)
    (hY : IsLocalScottSet U (ForcingScottRelated P R p) τ Y) : X = Y := by
  apply IsLocalScottSet.unique (hX.congr ?_) hY
  intro ν _
  apply and_congr_right
  intro _
  constructor
  · intro hσν
    exact atomicEquality_trans hR τ σ ν p ((atomicEquality_symm P R σ τ) ▸ he) hσν
  · intro hτν
    exact atomicEquality_trans hR σ τ ν p he hτν

theorem sUnion_forcingName {P X : V} (hX : ∀ τ ∈ X, IsForcingName P τ) :
    IsForcingName P (⋃ˢ X) := by
  apply (forcingName_iff P _).mpr
  intro z hz
  obtain ⟨τ, hτ, hz⟩ := mem_sUnion_iff.mp hz
  exact (forcingName_iff P τ).mp (hX τ hτ) z hz

theorem atomicEquality_sUnion {P R σ X p : V} (hne : IsNonempty X)
    (hX : ∀ τ ∈ X, p ∈ atomicEquality P R σ τ) :
    p ∈ atomicEquality P R σ (⋃ˢ X) := by
  obtain ⟨τ, hτ⟩ := hne.nonempty
  obtain ⟨hp, hστ⟩ := (mem_atomicEquality_iff _ _ _ _ _).mp (hX τ hτ)
  apply (mem_atomicEquality_iff _ _ _ _ _).mpr
  refine ⟨hp, ?_, ?_⟩
  · intro υ s hυ q hq hqp hqs
    obtain ⟨r, hr, hrq, ν, t, hν, hrt, he⟩ := hστ.1 υ s hυ q hq hqp hqs
    exact ⟨r, hr, hrq, ν, t, mem_sUnion_iff.mpr ⟨τ, hτ, hν⟩, hrt, he⟩
  · intro ν t hν q hq hqp hqt
    obtain ⟨η, hη, hνη⟩ := mem_sUnion_iff.mp hν
    exact ((mem_atomicEquality_iff _ _ _ _ _).mp (hX η hη)).2.2 ν t hνη q hq hqp hqt

theorem forcingScottSet_union {U P R p σ X : V} [hU : IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hX : IsLocalScottSet U (ForcingScottRelated P R p) σ X) :
    (⋃ˢ X) ∈ U ∧ IsForcingName P (⋃ˢ X) ∧ p ∈ atomicEquality P R σ (⋃ˢ X) := by
  have hx (τ : V) (hτ : τ ∈ X) : ForcingScottRelated P R p σ τ :=
    (hX.2.2 τ (hU.mem_trans hτ hX.1)).mp hτ |>.1
  have hu : (⋃ˢ X) ∈ U := by
    let X' : SetDomain U := ⟨X, hX.1⟩
    have he := TransitiveZF.sUnion_val U X'
    have hm : (⋃ˢ X' : SetDomain U).val ∈ U := (⋃ˢ X' : SetDomain U).property
    rwa [he] at hm
  exact ⟨hu, sUnion_forcingName (fun τ hτ ↦ (hx τ hτ).1),
    atomicEquality_sUnion hX.2.1 (fun τ hτ ↦ (hx τ hτ).2)⟩

end ZFVP
