import ZFVP.ModelTheory.BooleanAutomorphismLift
import ZFVP.SetTheory.LevyCollapseFull
import ZFVP.SetTheory.LevyCollapseRowPermutations

/-! The base-poset side of the Galois step for the Levy collapse. The Solovay symmetric system
lives over the Boolean completion `B = booleanConditions P R` of a poset `(P, R)`, and its names
are nice names whose conditions are elements of `B`. The automorphisms of `B` that one can build
by hand are the lifts `booleanLift P R π` of automorphisms `π` of `(P, R)`, so the hypothesis
"every automorphism in the forced stabilizer of `E` fixes `b`" can be tested against those lifts.

The lift of `π` fixes a nice name over `B` as soon as `π` fixes every condition occurring in that
name, so it lies in the forced stabilizer of `E`; feeding that back into the hypothesis turns an
abstract fixed-point assumption about the stabilizer into the concrete statement that the image
action of `π` fixes `b`. For the Levy collapse this applies to the row permutations
`levyPermutation κ β σ`, which are the automorphisms used in the localization argument.

The rigidity direction is here too: in a weakly homogeneous poset the only nonzero regular set
fixed by every automorphism is the whole poset. Together these give the Galois step in the case
where the conditions of `E` are rigid, and identify what is still missing in general. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The conditions occurring in a set of names -/

/-- The second coordinates of the pairs making up the names in `E`. For names over the Boolean
completion these are the elements of the completion that the names mention. -/
noncomputable def nameConditions (E : V) : V :=
  repl (fun z ↦ kpair.π₂ z) (by definability) (⋃ˢ E)

theorem mem_nameConditions_iff (E d : V) :
    d ∈ nameConditions E ↔ ∃ σ ∈ E, ∃ z ∈ σ, d = kpair.π₂ z := by
  unfold nameConditions
  rw [repl_spec]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨σ, hσ, hzσ⟩ := mem_sUnion_iff.mp hz
    exact ⟨σ, hσ, z, hzσ, rfl⟩
  · rintro ⟨σ, hσ, z, hzσ, rfl⟩
    exact ⟨z, mem_sUnion_iff.mpr ⟨σ, hσ, hzσ⟩, rfl⟩

theorem kpair_snd_mem_nameConditions {E σ ν p : V} (hσ : σ ∈ E) (h : (⟨ν, p⟩ₖ : V) ∈ σ) :
    p ∈ nameConditions E :=
  (mem_nameConditions_iff E p).mpr ⟨σ, hσ, ⟨ν, p⟩ₖ, h, (kpair.π₂_kpair ν p).symm⟩

/-! ### Lifts that fix a nice name over the completion -/

/-- The lift of `π` fixes a nice name over the Boolean completion whenever the image action of
`π` fixes every condition occurring in that name. -/
theorem nameAction_booleanLift_eq_self {P R K π σ : V} (hP : ∃ p, p ∈ P)
    (hπ : IsForcingAutomorphism P R π)
    (hσ : IsNiceName (booleanConditions P R) P K σ)
    (hfix : ∀ ν p : V, (⟨ν, p⟩ₖ : V) ∈ σ → imageAction π p = p) :
    nameAction (booleanLift P R π) σ = σ := by
  have hPB : P ∈ booleanConditions P R := top_mem_booleanConditions hP
  have hname : IsForcingName (booleanConditions P R) σ := hσ.isName hPB
  have htop : (booleanLift P R π) ‘ P = P := by
    rw [booleanLift_value hPB]
    exact imageAction_eq_of_iff hπ (fun _ h ↦ h) (fun _ h ↦ h)
      (fun q hq ↦ ⟨fun _ ↦ hq, fun _ ↦ function_value_mem hπ.1 hq⟩)
  apply mem_ext
  intro z
  rw [mem_nameAction_iff hname]
  constructor
  · rintro ⟨ν, b, hb, rfl⟩
    obtain ⟨k, -, c, hc, he⟩ := hσ _ hb
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    rw [nameAction_checkName hPB htop k, booleanLift_value hc, hfix _ _ hb]
    exact hb
  · intro hz
    obtain ⟨k, -, c, hc, he⟩ := hσ z hz
    refine ⟨checkName P k, c, he ▸ hz, ?_⟩
    rw [nameAction_checkName hPB htop k, booleanLift_value hc,
      hfix _ _ (he ▸ hz)]
    exact he

/-- A base automorphism fixing every condition of every name in `E` lifts to an automorphism of
the completion lying in the forced stabilizer of `E`. -/
theorem booleanLift_mem_forcedStabilizer {P R K E π : V} (hP : ∃ p, p ∈ P)
    (hπ : IsForcingAutomorphism P R π)
    (hE : ∀ σ ∈ E, IsNiceName (booleanConditions P R) P K σ)
    (hcond : ∀ d ∈ nameConditions E, imageAction π d = d) :
    booleanLift P R π ∈ forcedStabilizer (booleanConditions P R) (booleanOrder P R)
      (forcingAutomorphisms (booleanConditions P R) (booleanOrder P R)) E := by
  refine (mem_forcedStabilizer _ _ _ _ _).mpr
    ⟨booleanLift_mem_forcingAutomorphisms hπ, fun σ hσ ↦ ?_⟩
  rw [nameAction_booleanLift_eq_self hP hπ (hE σ hσ)
    (fun ν p hp ↦ hcond _ (kpair_snd_mem_nameConditions hσ hp))]
  exact forcedEqual_refl (booleanOrder_poset P R).1 σ

/-- Testing the fixed-point hypothesis against the lifts of base automorphisms: if every
automorphism of the completion in the forced stabilizer of `E` fixes `b`, then the image action of
every base automorphism fixing the conditions of `E` fixes `b`. -/
theorem imageAction_eq_self_of_forcedStabilizer_fixed {P R K E b π : V} (hP : ∃ p, p ∈ P)
    (hπ : IsForcingAutomorphism P R π)
    (hE : ∀ σ ∈ E, IsNiceName (booleanConditions P R) P K σ)
    (hcond : ∀ d ∈ nameConditions E, imageAction π d = d)
    (hb : b ∈ booleanConditions P R)
    (hfix : ∀ Θ ∈ forcedStabilizer (booleanConditions P R) (booleanOrder P R)
      (forcingAutomorphisms (booleanConditions P R) (booleanOrder P R)) E, Θ ‘ b = b) :
    imageAction π b = b := by
  rw [← booleanLift_value (P := P) (R := R) (π := π) hb]
  exact hfix _ (booleanLift_mem_forcedStabilizer hP hπ hE hcond)

/-! ### Row permutations of the Levy collapse -/

/-- The Levy form of the previous lemma: the row permutations above `β` are the base automorphisms
one feeds into it. -/
theorem levyPermutation_imageAction_eq_self {κ β s K E b : V}
    (hs : IsInternalPermutation (ω : V) s)
    (hE : ∀ σ ∈ E, IsNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (levyCollapse κ) K σ)
    (hcond : ∀ d ∈ nameConditions E, imageAction (levyPermutation κ β s) d = d)
    (hb : b ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hfix : ∀ Θ ∈ forcedStabilizer (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ))
      (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))) E, Θ ‘ b = b) :
    imageAction (levyPermutation κ β s) b = b :=
  imageAction_eq_self_of_forcedStabilizer_fixed ⟨∅, empty_mem_levyCollapse κ⟩
    (levyPermutation_automorphism hs) hE hcond hb hfix

/-! ### Rigidity from weak homogeneity -/

/-- In a weakly homogeneous poset the only nonzero regular set fixed by every automorphism that
fixes the top is the whole poset. -/
theorem eq_top_of_imageAction_fixed {P R one A : V} (hhom : IsWeaklyHomogeneous P R one)
    (hA : A ∈ booleanConditions P R)
    (hfix : ∀ π, IsForcingAutomorphism P R π → π ‘ one = one → imageAction π A = A) :
    A = P := by
  obtain ⟨hreg, a, ha⟩ := (mem_booleanConditions_iff P R A).mp hA
  apply SetTheory.subset_antisymm hreg.1
  intro p hp
  apply hreg.2.2 p hp
  intro q hq _
  obtain ⟨π, hπ, hone, r, hr, hrπ, hrq⟩ := hhom a (hreg.1 a ha) q hq
  have hπa : π ‘ a ∈ A := by
    rw [← hfix π hπ hone]
    exact (value_mem_imageAction_iff hπ hreg.1 (hreg.1 a ha)).mpr ha
  exact ⟨r, hreg.2.1 _ hπa r hr hrπ, hrq⟩

/-! ### Passing between a condition and its regular cone -/

/-- The image action of an automorphism on the regular cone of `p` is the regular cone of the
image of `p`. This is the bridge between an element of the completion and the corresponding
element of the completion of the completion. -/
theorem imageAction_coneRegular {P R π p : V} (hπ : IsForcingAutomorphism P R π) (hp : p ∈ P) :
    imageAction π (coneRegular P R p) = coneRegular P R (π ‘ p) := by
  apply imageAction_eq_of_iff hπ (fun _ h ↦ (mem_coneRegular_iff.mp h).1)
    (fun _ h ↦ (mem_coneRegular_iff.mp h).1)
  intro q hq
  rw [mem_coneRegular_iff, mem_coneRegular_iff]
  constructor
  · rintro ⟨-, hh⟩
    refine ⟨hq, fun r hr hrq ↦ ?_⟩
    obtain ⟨s, hs, hsp, hsr⟩ := hh (π ‘ r) (function_value_mem hπ.1 hr)
      ((hπ.2.2.2 r hr q hq).mp hrq)
    obtain ⟨t, ht, rfl⟩ := forcingAutomorphism_surjective hπ s hs
    exact ⟨t, ht, (hπ.2.2.2 t ht p hp).mpr hsp, (hπ.2.2.2 t ht r hr).mpr hsr⟩
  · rintro ⟨-, hh⟩
    refine ⟨function_value_mem hπ.1 hq, fun r hr hrq ↦ ?_⟩
    obtain ⟨t, ht, rfl⟩ := forcingAutomorphism_surjective hπ r hr
    obtain ⟨s, hs, hsp, hst⟩ := hh t ht ((hπ.2.2.2 t ht q hq).mpr hrq)
    exact ⟨π ‘ s, function_value_mem hπ.1 hs, (hπ.2.2.2 s hs p hp).mp hsp,
      (hπ.2.2.2 s hs t ht).mp hst⟩

/-- The regular cone of the top condition is the whole poset. -/
theorem coneRegular_top {P R one : V} (hR : IsForcingPreorder P R) (hone : IsForcingTop P R one) :
    coneRegular P R one = P := by
  apply SetTheory.subset_antisymm (fun q h ↦ (mem_coneRegular_iff.mp h).1)
  intro q hq
  exact mem_coneRegular_iff.mpr ⟨hq, fun r hr _ ↦ ⟨r, hr, hone.2 r hr, hR.2.1 r hr⟩⟩

/-- The top of the completion always lies in a generated complete subalgebra. -/
theorem top_mem_generatedSubalgebra (P R S : V) : P ∈ generatedSubalgebra P R S :=
  (mem_generatedSubalgebra_iff _ _ _ _).mpr
    ⟨∅, omega_subset_stageBound P R _ empty_mem_ω,
      generators_subset_closureStage (P := P) (R := R) (S := insert P S)
        (omega_subset_stageBound P R _ empty_mem_ω) P (mem_insert.mpr (Or.inl rfl))⟩

theorem top_mem_supportAlgebra (P R one K E : V) : P ∈ supportAlgebra P R one K E :=
  top_mem_generatedSubalgebra P R _

/-! ### The Galois step when the conditions of the names are rigid -/

/-- If every condition occurring in the names of `E` is fixed by every automorphism of the base
poset that fixes the top, then a condition of the completion fixed by the whole forced stabilizer
of `E` is the top of the completion, and so its regular cone lies in the support algebra. This is
the Galois step of Karagila-Schilhan Lemma 9.3 in the case where the conditions of `E` are rigid;
the general case needs the missing localization step. -/
theorem coneRegular_mem_supportAlgebra_of_rigid {P R one K E b : V} (hP : ∃ p, p ∈ P)
    (hhom : IsWeaklyHomogeneous P R one)
    (hE : ∀ σ ∈ E, IsNiceName (booleanConditions P R) P K σ)
    (hcond : ∀ d ∈ nameConditions E, ∀ π, IsForcingAutomorphism P R π →
      π ‘ one = one → imageAction π d = d)
    (hb : b ∈ booleanConditions P R)
    (hfix : ∀ Θ ∈ forcedStabilizer (booleanConditions P R) (booleanOrder P R)
      (forcingAutomorphisms (booleanConditions P R) (booleanOrder P R)) E, Θ ‘ b = b) :
    coneRegular (booleanConditions P R) (booleanOrder P R) b ∈
      supportAlgebra (booleanConditions P R) (booleanOrder P R) P K E := by
  have hbtop : b = P := by
    refine eq_top_of_imageAction_fixed hhom hb (fun π hπ hone ↦ ?_)
    exact imageAction_eq_self_of_forcedStabilizer_fixed hP hπ hE
      (fun d hd ↦ hcond d hd π hπ hone) hb hfix
  rw [hbtop, coneRegular_top (booleanOrder_poset P R).1 (booleanOrder_top hP)]
  exact top_mem_supportAlgebra _ _ _ _ _

/-- The Levy collapse instance of the rigid Galois step. -/
theorem levy_coneRegular_mem_supportAlgebra_of_rigid {κ K E b : V}
    (hE : ∀ σ ∈ E, IsNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (levyCollapse κ) K σ)
    (hcond : ∀ d ∈ nameConditions E, ∀ π, IsForcingAutomorphism (levyCollapse κ) (levyOrder κ) π →
      π ‘ (∅ : V) = ∅ → imageAction π d = d)
    (hb : b ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hfix : ∀ Θ ∈ forcedStabilizer (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ))
      (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))) E, Θ ‘ b = b) :
    coneRegular (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) b ∈
      supportAlgebra (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) K E :=
  coneRegular_mem_supportAlgebra_of_rigid ⟨∅, empty_mem_levyCollapse κ⟩
    (levyCollapse_homogeneous κ) hE hcond hb hfix

end ZFVP
