import ZFVP.ModelTheory.DirectedElementaryAmbientUnion
import ZFVP.SetTheory.NaturalClosureCardinality
import ZFVP.SetTheory.FiniteCardinalArithmetic
import ZFVP.SetTheory.WellOrderedSurjection

/-! A well-order-selected witness operation for internal membership formulas. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 800000

noncomputable def internalSkolemCandidates (B d q b : V) : V :=
  {x ∈ B ; MembershipSatisfies B (succ (domain b)) (kpair.π₂ q)
    (assignmentPrepend (domain b) b x) ↔ d = 0}

instance internalSkolemCandidates_definable : ℒₛₑₜ-function₄[V] internalSkolemCandidates := by
  have h : ℒₛₑₜ-relation₅ (fun C B d q b : V ↦ ∀ x, x ∈ C ↔ x ∈ B ∧
    (MembershipSatisfies B (succ (domain b)) (kpair.π₂ q)
      (assignmentPrepend (domain b) b x) ↔ d = 0)) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [internalSkolemCandidates, mem_sep_iff]
  rfl

attribute [local irreducible] internalSkolemCandidates

noncomputable def internalSkolemChoice (B w p : V) : V :=
  wellOrderSelection w (internalSkolemCandidates B (kpair.π₁ p)
    (kpair.π₁ (kpair.π₂ p)) (kpair.π₂ (kpair.π₂ p)))

instance internalSkolemChoice_definable : ℒₛₑₜ-function₃[V] internalSkolemChoice := by
  have hC : ℒₛₑₜ-function₃[V] (fun B (_w) p ↦ internalSkolemCandidates B (kpair.π₁ p)
      (kpair.π₁ (kpair.π₂ p)) (kpair.π₂ (kpair.π₂ p))) :=
    Language.DefinableFunction.substitution
      (f := ![fun v : Fin 3 → V ↦ v 0, fun v ↦ kpair.π₁ (v 2),
        fun v ↦ kpair.π₁ (kpair.π₂ (v 2)), fun v ↦ kpair.π₂ (kpair.π₂ (v 2))])
      internalSkolemCandidates_definable
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ]; all_goals definability)
  unfold internalSkolemChoice
  definability

attribute [local irreducible] internalSkolemChoice

noncomputable def internalSkolemInputs (C X : V) : V :=
  (ω : V) ×ˢ (C ×ˢ finiteSequences X)

instance internalSkolemInputs_definable : ℒₛₑₜ-function₂[V] internalSkolemInputs := by
  unfold internalSkolemInputs
  definability

noncomputable def internalSkolemImage (B w I : V) : V :=
  repl (internalSkolemChoice B w) (by definability) I

instance internalSkolemImage_definable : ℒₛₑₜ-function₃[V] internalSkolemImage := by
  have h : ℒₛₑₜ-relation₄ (fun Y B w I : V ↦ ∀ y, y ∈ Y ↔
    ∃ p ∈ I, y = internalSkolemChoice B w p) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [internalSkolemImage, repl_spec]

attribute [local irreducible] internalSkolemImage

noncomputable def internalSkolemStep (B w C X : V) : V :=
  X ∪ (internalSkolemImage B w (internalSkolemInputs C X) ∩ B)

instance internalSkolemStep_definable : ℒₛₑₜ-function₄[V] internalSkolemStep := by
  have hI : ℒₛₑₜ-function₄[V] (fun B w C X ↦ internalSkolemImage B w (internalSkolemInputs C X)) :=
    Language.DefinableFunction.substitution
      (f := ![fun v : Fin 4 → V ↦ v 0, fun v ↦ v 1,
        fun v ↦ internalSkolemInputs (v 2) (v 3)]) internalSkolemImage_definable
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ]; all_goals definability)
  unfold internalSkolemStep
  definability

theorem subset_internalSkolemStep (B w C X : V) : X ⊆ internalSkolemStep B w C X :=
  subset_union_left _ _

theorem internalSkolemStep_subset {B w C X : V} (hX : X ⊆ B) :
    internalSkolemStep B w C X ⊆ B := by
  intro x hx
  rcases mem_union_iff.mp hx with hx | hx
  · exact hX x hx
  · exact (mem_inter_iff.mp hx).2

theorem internalSkolemStep_witness {B w C X α n φ b d : V} [IsOrdinal α]
    (hw : w ∈ α ^ B) (hwi : Injective w) (hn : n ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hcode : ⟨succ n, φ⟩ₖ ∈ C) (hb : b ∈ X ^ n)
    (hex : ∃ x ∈ B, MembershipSatisfies B (succ n) φ (assignmentPrepend n b x) ↔ d = 0) :
    ∃ x ∈ internalSkolemStep B w C X,
      MembershipSatisfies B (succ n) φ (assignmentPrepend n b x) ↔ d = 0 := by
  let q := ⟨succ n, φ⟩ₖ
  let p := ⟨d, ⟨q, b⟩ₖ⟩ₖ
  have hp : p ∈ internalSkolemInputs C X :=
    kpair_mem_iff.mpr ⟨hd, kpair_mem_iff.mpr ⟨hcode, (mem_finiteSequences_iff X b).mpr ⟨n, hn, hb⟩⟩⟩
  have hc : IsNonempty (internalSkolemCandidates B d q b) := by
    obtain ⟨x, hx, hs⟩ := hex
    refine ⟨x, ?_⟩
    simpa [internalSkolemCandidates, q, domain_eq_of_mem_function hb] using And.intro hx hs
  have hs := wellOrderSelection_mem hw hwi
    (show internalSkolemCandidates B d q b ⊆ B from by
      intro x hx
      unfold internalSkolemCandidates at hx
      exact (mem_sep_iff.mp hx).1) hc
  have hx : internalSkolemChoice B w p ∈ B ∧
      (MembershipSatisfies B (succ n) φ
        (assignmentPrepend n b (internalSkolemChoice B w p)) ↔ d = 0) := by
    simpa [internalSkolemCandidates, internalSkolemChoice, p, q, domain_eq_of_mem_function hb] using hs
  refine ⟨internalSkolemChoice B w p, mem_union_iff.mpr (Or.inr (mem_inter_iff.mpr ⟨?_, hx.1⟩)), hx.2⟩
  unfold internalSkolemImage
  exact (repl_spec (show ℒₛₑₜ-function₁ (internalSkolemChoice B w) by definability)).mpr ⟨p, hp, rfl⟩

theorem union_cardLE_of_cardLE_initial {lam X Y : V}
    (hlam : IsInitialOrdinal lam) (hω : (ω : V) ⊆ lam) (hX : X ≤# lam) (hY : Y ≤# lam) :
    X ∪ Y ≤# lam := by
  have htwo : ((2 : ℕ) : V) ≤# lam := cardLE_of_subset (subset_trans
    (IsOrdinal.toIsTransitive.transitive _ (show ((2 : ℕ) : V) ∈ ω from by simp)) hω)
  have h := (union_cardLE_disjointUnion X Y).trans (disjointUnion_cardLE hX hY)
  rw [disjointUnion_self_eq] at h
  exact h.trans (prod_cardLE_of_cardLE_initial hlam hω (CardLE.refl lam) htwo)

theorem internalSkolemStep_cardLE (hAC : InternalChoice V) {lam B w C X : V}
    (hlam : IsInitialOrdinal lam) (hω : (ω : V) ⊆ lam) (hC : C ≤# lam) (hX : X ≤# lam) :
    internalSkolemStep B w C X ≤# lam := by
  have hi : internalSkolemInputs C X ≤# lam := prod_cardLE_of_cardLE_initial hlam hω
    (cardLE_of_subset hω) (prod_cardLE_of_cardLE_initial hlam hω hC
      (finiteSequences_cardLE_of_cardLE_initial hAC hlam hω hX))
  let F := internalSkolemChoice B w
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  have himage : repl F hF (internalSkolemInputs C X) ≤# internalSkolemInputs C X := by
    let g := definableGraph (internalSkolemInputs C X) F hF
    have hr : range g = repl F hF (internalSkolemInputs C X) := range_definableGraph _ _ _
    exact cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC _)
      (function_mem_of_isFunction' (domain_definableGraph _ _ _) hr) hr
  unfold internalSkolemStep internalSkolemImage
  exact union_cardLE_of_cardLE_initial hlam hω hX
    ((cardLE_of_subset (fun _ hx ↦ (mem_inter_iff.mp hx).1)).trans (himage.trans hi))

end ZFVP
