import ZFVP.SetTheory.HODReals
import ZFVP.SetTheory.HODDependentChoice
import ZFVP.SetTheory.EndExtensionCoding
import ZFVP.SetTheory.EndExtensionRelations
import ZFVP.SetTheory.EndExtensionSets
import ZFVP.SetTheory.EndExtensionWellOrdering
import ZFVP.SetTheory.EndExtensionLevyCollapse
import ZFVP.SetTheory.EndExtensionRegular
import ZFVP.SetTheory.EndExtensionFinite
import ZFVP.SetTheory.FiniteSets
import ZFVP.SetTheory.LebesgueNull

/-! Transport of the Cantor space vocabulary between `V` and the HOD class model along the
inclusion: reals, finite sequences, tree bodies, open sets, trees, perfect and nowhere dense trees,
images and shadows. Finite sets of HOD elements are HOD. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def insertFormula : SetTheorySemisentence 4 := f“w q₁ q₂ P. w = q₁ ∨ w ∈ q₂”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_insertFormula (w q₁ q₂ P : V) : insertFormula.Evalb ![w, q₁, q₂, P] ↔ w = q₁ ∨ w ∈ q₂ := by
  simp [insertFormula]

theorem function_power_subset_binarySequences {N : V} (hN : N ∈ (ω : V)) :
    ((2 : ℕ) : V) ^ N ⊆ binarySequences V :=
  fun s hs ↦ (mem_binarySequences_iff s).mpr ⟨N, hN, hs⟩

section

variable (Pf : SetTheorySemisentence 2) (p : V)

def finiteHODFormula (Pf : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  f“A p. (∀ y ∈ A, !(hodFormula Pf) y p) → !(hodFormula Pf) A p”

instance finiteHODFormula_defined :
    ℒₛₑₜ-relation[V] (fun A p ↦ (∀ y ∈ A, IsHOD Pf y p) → IsHOD Pf A p) via finiteHODFormula Pf :=
  ⟨fun v ↦ by simp [finiteHODFormula]⟩

theorem isHOD_insert {a A : V} (ha : IsHOD Pf a p) (hA : IsHOD Pf A p) : IsHOD Pf (insert a A) p := by
  refine isHOD_of_od Pf ?_ (fun w hw ↦ ?_)
  · refine isOD_of_two Pf insertFormula (IsHOD.od Pf ha) (IsHOD.od Pf hA)
      (isParameterTree_of_allowed Pf (isAllowed_empty Pf p)) ?_
    intro w
    rw [eval_insertFormula, mem_insert]
  · rcases mem_insert.mp hw with rfl | hw
    · exact ha
    · exact hA.mem Pf hw

/-- Finite sets of HOD elements are HOD. -/
theorem isHOD_of_finite {A : V} (hA : IsInternallyFinite A) (h : ∀ y ∈ A, IsHOD Pf y p) :
    IsHOD Pf A p := by
  refine internallyFinite_induction (fun A ↦ (∀ y ∈ A, IsHOD Pf y p) → IsHOD Pf A p)
    (definablePred_of_defined (finiteHODFormula_defined Pf) p) ?_ ?_ A hA h
  · intro _
    exact isHOD_of_ordinal Pf ∅ p
  · intro B a ih hall
    exact isHOD_insert Pf p (hall a (mem_insert.mpr (Or.inl rfl)))
      (ih (fun y hy ↦ hall y (mem_insert.mpr (Or.inr hy))))

/-- The class model of the hereditarily ordinal definable sets. -/
abbrev HODDom : Type _ := ClassDomain (classOf (hodFormula Pf) p)

/-- The inclusion of HOD into `V`. -/
noncomputable def hodInclusion : MembershipEndExtension (HODDom Pf p) V :=
  classDomain_endExtension (hodFormula Pf) p (hod_transitive Pf p)

/-- An element of HOD as an element of the class model. -/
def toHOD {x : V} (hx : IsHOD Pf x p) : (HODDom Pf p) := ⟨x, (hodClass_iff Pf p x).mpr hx⟩

theorem toHOD_val {x : V} (hx : IsHOD Pf x p) : (toHOD Pf p hx).val = x := rfl

theorem hod_val_isHOD (x : (HODDom Pf p)) : IsHOD Pf x.val p := (hodClass_iff Pf p _).mp x.property

variable [Nonempty (HODDom Pf p)] [(HODDom Pf p)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem val_omega : (ω : (HODDom Pf p)).val = (ω : V) := (hodInclusion Pf p).map_omega

theorem val_two : (((2 : ℕ) : (HODDom Pf p))).val = ((2 : ℕ) : V) := (hodInclusion Pf p).map_numeral 2

theorem val_empty : ((∅ : (HODDom Pf p))).val = (∅ : V) := (hodInclusion Pf p).map_empty

theorem mem_omega_val (n : (HODDom Pf p)) : n ∈ (ω : (HODDom Pf p)) ↔ n.val ∈ (ω : V) :=
  ((hodInclusion Pf p).natural_iff n).symm

theorem mem_val_iff (x y : (HODDom Pf p)) : x.val ∈ y.val ↔ x ∈ y := Iff.rfl

theorem subset_val_iff (x y : (HODDom Pf p)) : x.val ⊆ y.val ↔ x ⊆ y := (hodInclusion Pf p).subset_iff x y

theorem exists_val_of_mem {x : (HODDom Pf p)} {y : V} (hy : y ∈ x.val) : ∃ z ∈ x, y = z.val :=
  (hodInclusion Pf p).endExtension x y hy

theorem val_binarySequences : (binarySequences (HODDom Pf p)).val = binarySequences V := by
  have h := (hodInclusion Pf p).map_finiteSequences ((2 : ℕ) : (HODDom Pf p))
  have h2 : (hodInclusion Pf p) ((2 : ℕ) : (HODDom Pf p)) = ((2 : ℕ) : V) := (hodInclusion Pf p).map_numeral 2
  rw [h2] at h
  exact h

theorem mem_function_val (f A B : (HODDom Pf p)) : f ∈ B ^ A ↔ f.val ∈ B.val ^ A.val :=
  ((hodInclusion Pf p).function_iff f A B).symm

theorem mem_cantorSpace_val (x : (HODDom Pf p)) : x ∈ cantorSpace (HODDom Pf p) ↔ x.val ∈ cantorSpace V := by
  rw [mem_cantorSpace_iff, mem_cantorSpace_iff, mem_function_val Pf p, val_two Pf p, val_omega Pf p]

theorem val_domain (f : (HODDom Pf p)) : (domain f).val = domain f.val := (hodInclusion Pf p).map_relationDomain f

theorem val_restrict (f A : (HODDom Pf p)) : (f ↾ A).val = f.val ↾ A.val := (hodInclusion Pf p).map_restrict f A

theorem val_range (f : (HODDom Pf p)) : (range f).val = range f.val := (hodInclusion Pf p).map_range f

theorem val_image (f k : (HODDom Pf p)) : (image f k).val = image f.val k.val := by
  unfold image
  rw [val_range Pf p, val_restrict Pf p]

theorem val_prod (A B : (HODDom Pf p)) : (A ×ˢ B).val = A.val ×ˢ B.val := (hodInclusion Pf p).map_prod A B

theorem val_sdiff (A B : (HODDom Pf p)) : (A \ B).val = A.val \ B.val := (hodInclusion Pf p).map_sdiff A B

theorem val_union (A B : (HODDom Pf p)) : (A ∪ B).val = A.val ∪ B.val := (hodInclusion Pf p).map_union A B

theorem val_finitePower (A : (HODDom Pf p)) {n : (HODDom Pf p)} (hn : n ∈ (ω : (HODDom Pf p))) :
    (A ^ n).val = A.val ^ n.val := (hodInclusion Pf p).map_finiteFunctionSet A hn

theorem isFunction_val (f : (HODDom Pf p)) [IsFunction f] : IsFunction f.val := (hodInclusion Pf p).map_function f

theorem isFunction_of_val (f : (HODDom Pf p)) (h : IsFunction f.val) : IsFunction f :=
  (((hodInclusion Pf p).function_on_iff f (domain f)).mp ⟨h, ((hodInclusion Pf p).map_relationDomain f).symm⟩).1

theorem val_value (f x : (HODDom Pf p)) [IsFunction f] (hx : x ∈ domain f) : (f ‘ x).val = f.val ‘ x.val :=
  (hodInclusion Pf p).map_value f x hx

theorem injective_val (f : (HODDom Pf p)) : Injective f.val ↔ Injective f := (hodInclusion Pf p).injective_iff f

theorem val_injective {x y : (HODDom Pf p)} (h : x.val = y.val) : x = y := Subtype.ext h

variable (hreal : ∀ x ∈ cantorSpace V, IsAllowed Pf x p)

include hreal in
theorem val_cantorSpace : (cantorSpace (HODDom Pf p)).val = cantorSpace V := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := exists_val_of_mem Pf p hy
    exact (mem_cantorSpace_val Pf p z).mp hz
  · intro hy
    have hz : toHOD Pf p (isHOD_of_real Pf p hreal hy) ∈ cantorSpace (HODDom Pf p) :=
      (mem_cantorSpace_val Pf p _).mpr hy
    exact hz

include hreal in
theorem val_treeBody (T : (HODDom Pf p)) : (treeBody T).val = treeBody T.val := by
  have h := (hodInclusion Pf p).map_separation (cantorSpace (HODDom Pf p)) (fun x ↦ ∀ n ∈ (ω : (HODDom Pf p)), x ↾ n ∈ T)
    (fun x ↦ ∀ n ∈ (ω : V), x ↾ n ∈ T.val) (by definability) (by definability) (by
      intro x _
      show (∀ n ∈ (ω : HODDom Pf p), x ↾ n ∈ T) ↔ ∀ n ∈ (ω : V), x.val ↾ n ∈ T.val
      constructor
      · intro hx n hn
        rw [← val_omega Pf p] at hn
        obtain ⟨n', hn', rfl⟩ := exists_val_of_mem Pf p hn
        rw [← val_restrict Pf p]
        exact hx n' hn'
      · intro hx n hn
        have := hx n.val ((mem_omega_val Pf p n).mp hn)
        rw [← val_restrict Pf p] at this
        exact this)
  change (treeBody T).val = sep (cantorSpace V) _ _
  rw [← val_cantorSpace Pf p hreal]
  exact h

include hreal in
theorem val_openFrom (S : (HODDom Pf p)) : (openFrom S).val = openFrom S.val := by
  have h := (hodInclusion Pf p).map_separation (cantorSpace (HODDom Pf p)) (fun x ↦ ∃ s ∈ S, x ↾ (domain s) = s)
    (fun x ↦ ∃ s ∈ S.val, x ↾ (domain s) = s) (by definability) (by definability) (by
      intro x _
      show (∃ s ∈ S, x ↾ (domain s) = s) ↔ ∃ s ∈ S.val, x.val ↾ (domain s) = s
      constructor
      · rintro ⟨s, hs, hxs⟩
        refine ⟨s.val, hs, ?_⟩
        rw [← val_domain Pf p, ← val_restrict Pf p, hxs]
      · rintro ⟨s, hs, hxs⟩
        obtain ⟨s', hs', rfl⟩ := exists_val_of_mem Pf p hs
        refine ⟨s', hs', val_injective Pf p ?_⟩
        rw [val_restrict Pf p, val_domain Pf p]
        exact hxs)
  change (openFrom S).val = sep (cantorSpace V) _ _
  rw [← val_cantorSpace Pf p hreal]
  exact h

include hreal in
theorem val_gDelta {g : (HODDom Pf p)} (hg : g ∈ (℘ (binarySequences (HODDom Pf p))) ^ (ω : (HODDom Pf p))) :
    (gDelta g).val = gDelta g.val := by
  have hgf : IsFunction g := IsFunction.of_mem hg
  have hgd : domain g = (ω : (HODDom Pf p)) := domain_eq_of_mem_function hg
  have h := (hodInclusion Pf p).map_separation (cantorSpace (HODDom Pf p)) (fun x ↦ ∀ n ∈ (ω : (HODDom Pf p)), x ∈ openFrom (g ‘ n))
    (fun x ↦ ∀ n ∈ (ω : V), x ∈ openFrom (g.val ‘ n)) (by definability) (by definability) (by
      intro x _
      show (∀ n ∈ (ω : HODDom Pf p), x ∈ openFrom (g ‘ n)) ↔ ∀ n ∈ (ω : V), x.val ∈ openFrom (g.val ‘ n)
      constructor
      · intro hx n hn
        rw [← val_omega Pf p] at hn
        obtain ⟨n', hn', rfl⟩ := exists_val_of_mem Pf p hn
        rw [← val_value Pf p g n' (by rw [hgd]; exact hn'), ← val_openFrom Pf p hreal]
        exact hx n' hn'
      · intro hx n hn
        have := hx n.val ((mem_omega_val Pf p n).mp hn)
        rw [← val_value Pf p g n (by rw [hgd]; exact hn), ← val_openFrom Pf p hreal] at this
        exact this)
  change (gDelta g).val = sep (cantorSpace V) _ _
  rw [← val_cantorSpace Pf p hreal]
  exact h

theorem isTree_val (T : (HODDom Pf p)) : IsTree T ↔ IsTree T.val := by
  unfold IsTree
  rw [← val_binarySequences Pf p, subset_val_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h s hs n hn
    obtain ⟨s', hs', rfl⟩ := exists_val_of_mem Pf p hs
    rw [← val_domain Pf p] at hn
    obtain ⟨n', hn', rfl⟩ := exists_val_of_mem Pf p hn
    rw [← val_restrict Pf p]
    exact h s' hs' n' hn'
  · intro h s hs n hn
    have := h s.val hs n.val (by rw [← val_domain Pf p]; exact hn)
    rw [← val_restrict Pf p] at this
    exact this

theorem incompatible_val {t u : (HODDom Pf p)} (ht : t ∈ binarySequences (HODDom Pf p))
    (hu : u ∈ binarySequences (HODDom Pf p)) : Incompatible t u ↔ Incompatible t.val u.val := by
  have htf : IsFunction t := binarySequence_isFunction ht
  have huf : IsFunction u := binarySequence_isFunction hu
  unfold Incompatible
  constructor
  · rintro ⟨i, hit, hiu, hne⟩
    refine ⟨i.val, by rw [← val_domain Pf p]; exact hit, by rw [← val_domain Pf p]; exact hiu, ?_⟩
    rw [← val_value Pf p t i hit, ← val_value Pf p u i hiu]
    intro h
    exact hne (val_injective Pf p h)
  · rintro ⟨i, hit, hiu, hne⟩
    rw [← val_domain Pf p] at hit hiu
    obtain ⟨i', hi', rfl⟩ := exists_val_of_mem Pf p hit
    refine ⟨i', hi', hiu, ?_⟩
    intro h
    apply hne
    rw [← val_value Pf p t i' hi', ← val_value Pf p u i' hiu, h]

theorem isPerfectTree_val (T : (HODDom Pf p)) : IsPerfectTree T ↔ IsPerfectTree T.val := by
  unfold IsPerfectTree
  rw [isTree_val Pf p]
  constructor
  · rintro ⟨hT, h0, hsplit⟩
    refine ⟨hT, by rw [← val_empty Pf p]; exact h0, fun s hs ↦ ?_⟩
    obtain ⟨s', hs', rfl⟩ := exists_val_of_mem Pf p hs
    obtain ⟨t, ht, u, hu, hst, hsu, htu⟩ := hsplit s' hs'
    have hTB : T ⊆ binarySequences (HODDom Pf p) := ((isTree_val Pf p T).mpr hT).1
    refine ⟨t.val, ht, u.val, hu, (subset_val_iff Pf p _ _).mpr hst, (subset_val_iff Pf p _ _).mpr hsu, ?_⟩
    exact (incompatible_val Pf p (hTB t ht) (hTB u hu)).mp htu
  · rintro ⟨hT, h0, hsplit⟩
    refine ⟨hT, by rw [← val_empty Pf p] at h0; exact h0, fun s hs ↦ ?_⟩
    obtain ⟨t, ht, u, hu, hst, hsu, htu⟩ := hsplit s.val hs
    obtain ⟨t', ht', rfl⟩ := exists_val_of_mem Pf p ht
    obtain ⟨u', hu', rfl⟩ := exists_val_of_mem Pf p hu
    have hTB : T ⊆ binarySequences (HODDom Pf p) := ((isTree_val Pf p T).mpr hT).1
    refine ⟨t', ht', u', hu', (subset_val_iff Pf p _ _).mp hst, (subset_val_iff Pf p _ _).mp hsu, ?_⟩
    exact (incompatible_val Pf p (hTB t' ht') (hTB u' hu')).mpr htu

theorem isNowhereDenseTree_val (T : (HODDom Pf p)) : IsNowhereDenseTree T ↔ IsNowhereDenseTree T.val := by
  unfold IsNowhereDenseTree
  rw [isTree_val Pf p]
  apply and_congr_right
  intro _
  constructor
  · intro h s hs
    rw [← val_binarySequences Pf p] at hs
    obtain ⟨s', hs', rfl⟩ := exists_val_of_mem Pf p hs
    obtain ⟨t, ht, hst, htT⟩ := h s' hs'
    refine ⟨t.val, by rw [← val_binarySequences Pf p]; exact ht, (subset_val_iff Pf p _ _).mpr hst, htT⟩
  · intro h s hs
    obtain ⟨t, ht, hst, htT⟩ := h s.val (by rw [← val_binarySequences Pf p]; exact hs)
    rw [← val_binarySequences Pf p] at ht
    obtain ⟨t', ht', rfl⟩ := exists_val_of_mem Pf p ht
    exact ⟨t', ht', (subset_val_iff Pf p _ _).mp hst, htT⟩

theorem val_shadow (F N : (HODDom Pf p)) (hN : N ∈ (ω : (HODDom Pf p))) : (shadow F N).val = shadow F.val N.val := by
  have h := (hodInclusion Pf p).map_separation (((2 : ℕ) : (HODDom Pf p)) ^ N) (fun t ↦ ∃ s ∈ F, s ⊆ t)
    (fun t ↦ ∃ s ∈ F.val, s ⊆ t) (by definability) (by definability) (by
      intro t _
      show (∃ s ∈ F, s ⊆ t) ↔ ∃ s ∈ F.val, s ⊆ t.val
      constructor
      · rintro ⟨s, hs, hst⟩
        exact ⟨s.val, hs, (subset_val_iff Pf p _ _).mpr hst⟩
      · rintro ⟨s, hs, hst⟩
        obtain ⟨s', hs', rfl⟩ := exists_val_of_mem Pf p hs
        exact ⟨s', hs', (subset_val_iff Pf p _ _).mp hst⟩)
  change (shadow F N).val = sep (((2 : ℕ) : V) ^ N.val) _ _
  rw [← val_two Pf p, ← val_finitePower Pf p _ hN]
  exact h

end

end ZFVP
