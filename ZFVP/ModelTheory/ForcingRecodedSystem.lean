import ZFVP.ModelTheory.ForcingRecodedCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s Q T m : V}
variable (hs : IsForcingIterationCode θ s)
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
  (Q ‘ i) (T ‘ i) (m ‘ i))
local notation "π" => forcingRecodedProjections θ s m
local notation "E" => forcingRecodedSections θ s m
local notation "L" => forcingRecodedLifts θ s Q m
local notation "t" => forcingRecodedTops θ s m

include hs hm

theorem forcingRecoded_split : IsSplitForcingSystem θ Q π E := by
  constructor
  · intro i hi j hj hij p hp
    exact function_value_mem (forcingRecodedProjections_function hs hm hi hj hij) hp
  · intro i hi j hj hij p hp
    exact function_value_mem (forcingRecodedSections_function hs hm hi hj hij) hp
  · intro i hi p hp
    obtain ⟨p, hp₀, rfl⟩ := (hm i hi).surjective p hp
    have hp := hp₀
    rw [forcingRecodedSections_image hs hm hi hi (subset_refl _) hp,
      hs.system.split.secId i hi p hp]
  · intro i hi j hj k hk hij hjk p hp
    obtain ⟨p, hp₀, rfl⟩ := (hm k hk).surjective p hp
    have hp := hp₀
    rw [forcingRecodedProjections_image hs hm hj hk hjk hp,
      forcingRecodedProjections_image hs hm hi hj hij (hs.system.split.projMaps j hj k hk hjk p hp),
      forcingRecodedProjections_image hs hm hi hk (fun x hx ↦ hjk x (hij x hx)) hp,
      hs.system.split.projComp i hi j hj k hk hij hjk p hp]
  · intro i hi j hj k hk hij hjk p hp
    obtain ⟨p, hp₀, rfl⟩ := (hm i hi).surjective p hp
    have hp := hp₀
    rw [forcingRecodedSections_image hs hm hi hj hij hp,
      forcingRecodedSections_image hs hm hj hk hjk (hs.system.split.secMaps i hi j hj hij p hp),
      forcingRecodedSections_image hs hm hi hk (fun x hx ↦ hjk x (hij x hx)) hp,
      hs.system.split.secComp i hi j hj k hk hij hjk p hp]
  · intro i hi j hj hij p hp
    obtain ⟨p, hp₀, rfl⟩ := (hm i hi).surjective p hp
    have hp := hp₀
    rw [forcingRecodedSections_image hs hm hi hj hij hp,
      forcingRecodedProjections_image hs hm hi hj hij (hs.system.split.secMaps i hi j hj hij p hp),
      hs.system.split.retraction i hi j hj hij p hp]

theorem forcingRecoded_functions : IsFunctionalSplitForcingSystem θ Q π E :=
  ⟨fun _ hi _ hj hij ↦ forcingRecodedProjections_function hs hm hi hj hij,
    fun _ hi _ hj hij ↦ forcingRecodedSections_function hs hm hi hj hij⟩

theorem forcingRecoded_order (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i)) :
    IsOrderedSplitForcingSystem θ Q T π E := by
  refine ⟨hT, ?_, ?_⟩
  · intro i hi j hj hij a ha b hb hab
    obtain ⟨a, ha₀, rfl⟩ := (hm j hj).surjective a ha
    have ha := ha₀
    obtain ⟨b, hb₀, rfl⟩ := (hm j hj).surjective b hb
    have hb := hb₀
    rw [forcingRecodedProjections_image hs hm hi hj hij ha,
      forcingRecodedProjections_image hs hm hi hj hij hb]
    exact ((hm i hi).2.2.2 _ (hs.system.split.projMaps i hi j hj hij a ha)
      _ (hs.system.split.projMaps i hi j hj hij b hb)).mp
        (hs.system.order.projMono i hi j hj hij a ha b hb (((hm j hj).2.2.2 a ha b hb).mpr hab))
  · intro i hi j hj hij a ha b hb
    obtain ⟨a, ha₀, rfl⟩ := (hm j hj).surjective a ha
    have ha := ha₀
    obtain ⟨b, hb₀, rfl⟩ := (hm i hi).surjective b hb
    have hb := hb₀
    rw [forcingRecodedSections_image hs hm hi hj hij hb,
      forcingRecodedProjections_image hs hm hi hj hij ha,
      ← (hm j hj).2.2.2 a ha _ (hs.system.split.secMaps i hi j hj hij b hb),
      ← (hm i hi).2.2.2 _ (hs.system.split.projMaps i hi j hj hij a ha) b hb]
    exact hs.system.order.below i hi j hj hij a ha b hb

theorem forcingRecoded_tops : IsToppedSplitForcingSystem θ Q T π E t := by
  constructor
  · intro i hi
    rw [forcingRecodedTops_value hi]
    refine ⟨function_value_mem (hm i hi).1 (hs.system.tops.top i hi).1, ?_⟩
    intro p hp
    obtain ⟨p, hp₀, rfl⟩ := (hm i hi).surjective p hp
    have hp := hp₀
    exact ((hm i hi).2.2.2 p hp _ (hs.system.tops.top i hi).1).mp ((hs.system.tops.top i hi).2 p hp)
  · intro i hi j hj hij
    rw [forcingRecodedTops_value hj,
      forcingRecodedProjections_image hs hm hi hj hij (hs.system.tops.top j hj).1,
      hs.system.tops.projTop i hi j hj hij, forcingRecodedTops_value hi]
  · intro i hi j hj hij
    rw [forcingRecodedTops_value hi,
      forcingRecodedSections_image hs hm hi hj hij (hs.system.tops.top i hi).1,
      hs.system.tops.secTop i hi j hj hij, forcingRecodedTops_value hj]

theorem forcingRecoded_lifts : IsCoherentForcingLift θ Q T π L := by
  constructor
  · intro i hi j hj hij a ha b hb hle
    obtain ⟨a, ha₀, rfl⟩ := (hm j hj).surjective a ha
    have ha := ha₀
    obtain ⟨b, hb₀, rfl⟩ := (hm i hi).surjective b hb
    have hb := hb₀
    rw [forcingRecodedProjections_image hs hm hi hj hij ha,
      ← (hm i hi).2.2.2 b hb _ (hs.system.split.projMaps i hi j hj hij a ha)] at hle
    have hl := hs.system.lifts.lift i hi j hj hij a ha b hb hle
    rw [forcingRecodedLifts_image hm hi hj ha hb]
    refine ⟨function_value_mem (hm j hj).1 hl.1,
      ((hm j hj).2.2.2 _ hl.1 a ha).mp hl.2.1, ?_⟩
    rw [forcingRecodedProjections_image hs hm hi hj hij hl.1, hl.2.2]
  · intro i hi j hj k hk hij hjk a ha b hb hle
    have hik : i ⊆ k := fun x hx ↦ hjk x (hij x hx)
    obtain ⟨a, ha₀, rfl⟩ := (hm k hk).surjective a ha
    have ha := ha₀
    obtain ⟨b, hb₀, rfl⟩ := (hm i hi).surjective b hb
    have hb := hb₀
    rw [forcingRecodedProjections_image hs hm hi hk hik ha,
      ← (hm i hi).2.2.2 b hb _ (hs.system.split.projMaps i hi k hk hik a ha)] at hle
    have hl := hs.system.lifts.lift i hi k hk hik a ha b hb hle
    rw [forcingRecodedLifts_image hm hi hk ha hb,
      forcingRecodedProjections_image hs hm hj hk hjk hl.1,
      forcingRecodedProjections_image hs hm hj hk hjk ha,
      forcingRecodedLifts_image hm hi hj (hs.system.split.projMaps j hj k hk hjk a ha) hb,
      hs.system.lifts.commute i hi j hj k hk hij hjk a ha b hb hle]

theorem forcingRecoded_compatible : IsSectionCompatibleForcingLift θ Q T π E L := by
  constructor
  intro i hi k hk j hj hik hkj a ha b hb hle
  obtain ⟨a, ha₀, rfl⟩ := (hm k hk).surjective a ha
  have ha := ha₀
  obtain ⟨b, hb₀, rfl⟩ := (hm i hi).surjective b hb
  have hb := hb₀
  rw [forcingRecodedProjections_image hs hm hi hk hik ha,
    ← (hm i hi).2.2.2 b hb _ (hs.system.split.projMaps i hi k hk hik a ha)] at hle
  have hl := hs.system.lifts.lift i hi k hk hik a ha b hb hle
  rw [forcingRecodedSections_image hs hm hk hj hkj ha,
    forcingRecodedLifts_image hm hi hj (hs.system.split.secMaps k hk j hj hkj a ha) hb,
    forcingRecodedLifts_image hm hi hk ha hb,
    forcingRecodedSections_image hs hm hk hj hkj hl.1,
    hs.system.compatible.compatible i hi k hk j hj hik hkj a ha b hb hle]

theorem forcingRecoded_system (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i)) :
    IsForcingIterationSystem θ Q T π E L t :=
  ⟨forcingRecoded_split hs hm, forcingRecoded_order hs hm hT,
    forcingRecoded_functions hs hm, forcingRecoded_tops hs hm,
    forcingRecoded_lifts hs hm, forcingRecoded_compatible hs hm⟩

theorem forcingRecoded_code (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQtable : IsIterationTable θ Q) (hTtable : IsIterationTable θ T) :
    IsForcingIterationCode θ (forcingRecodedCode θ s Q T m) := by
  unfold forcingRecodedCode
  constructor <;> simp only [forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code,
    forcingCodeE_code, forcingCodeL_code, forcingCodet_code]
  · exact forcingRecoded_system hs hm hT
  · exact hQtable
  · exact hTtable
  · unfold forcingRecodedProjections
    exact ⟨inferInstance, domain_definableGraph _ _ _⟩
  · unfold forcingRecodedSections
    exact ⟨inferInstance, domain_definableGraph _ _ _⟩
  · unfold forcingRecodedLifts
    exact ⟨inferInstance, domain_definableGraph _ _ _⟩
  · unfold forcingRecodedTops
    exact ⟨inferInstance, domain_definableGraph _ _ _⟩

end ZFVP
