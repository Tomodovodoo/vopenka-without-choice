import ZFVP.SetTheory.SmallSubsetsStage
import ZFVP.SetTheory.SupercompactMeasure

/-! # Supercompactness in the measure sense inside a rank stage

`normalFineMeasureFormula` says "U is a normal fine measure on `P_k(l)`" and
`supercompactStageFormula` says "a is supercompact in the measure sense". Both are read twice:
in the ambient universe, and inside a rank stage `hierarchy δ` with `δ` closed under successor.
The stage reading is what a later module transfers along an elementary embedding of two stages,
so no ZF axiom is assumed for the stage.

The formulas introduce their auxiliary sets by guarded universal quantifiers: the base set
`P_k(l)`, its power set, and the power sets of `P_k(l) ×ˢ l` and of `a ×ˢ U`. A stage closed
under successor contains all four, so those quantifiers pick out the same sets there as outside.
Everything below them is bounded, hence absolute by `bounded_formula_absolute`, and every
subset, family and function the measure conditions speak about lies in the stage.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- `P` is the power set of `S`. -/
def powerSetGuardFormula : SetTheorySemisentence 2 :=
  “P S. (∀ y ∈ P, y ⊆ S) ∧ ∀ y, y ⊆ S → y ∈ P”

/-- `w` is a set of Kuratowski pairs with first entry in `A` and second entry in `B`. -/
def pairSubsetFormula : SetTheorySemisentence 3 :=
  “w A B. ∀ p ∈ w, ∃ a ∈ A, ∃ b ∈ B, !boundedKpairFormula p a b”

theorem pairSubsetFormula_bounded : IsBoundedSetFormula pairSubsetFormula := by
  exact .all (.bvar 0) (.exs (.bvar 2) (.exs (.bvar 4)
    (boundedKpairFormula_bounded.subst _)))

/-- `W` is the power set of `A ×ˢ B`. -/
def pairSetGuardFormula : SetTheorySemisentence 3 :=
  “W A B. (∀ w ∈ W, !pairSubsetFormula w A B) ∧ ∀ w, !pairSubsetFormula w A B → w ∈ W”

/-- `U` is an ultrafilter on `S`, where `P` is the power set of `S`. -/
def boundedUltrafilterFormula : SetTheorySemisentence 3 :=
  “S P U. (∀ X ∈ U, X ⊆ S) ∧ S ∈ U ∧ (∀ X ∈ U, ∃ z ∈ X, ⊤) ∧
    (∀ X ∈ U, ∀ Y ∈ P, X ⊆ Y → Y ∈ U) ∧
    (∀ X ∈ U, ∀ Y ∈ U, ∃ Z ∈ P, (∀ z ∈ Z, z ∈ X ∧ z ∈ Y) ∧ (∀ z ∈ X, z ∈ Y → z ∈ Z) ∧ Z ∈ U) ∧
    (∀ X ∈ P, X ∈ U ∨ ∃ Z ∈ P, (∀ z ∈ Z, z ∈ S ∧ ¬z ∈ X) ∧ (∀ z ∈ S, ¬z ∈ X → z ∈ Z) ∧ Z ∈ U)”

theorem boundedUltrafilterFormula_bounded : IsBoundedSetFormula boundedUltrafilterFormula := by
  exact .and (.all (.bvar 2) (isSubsetOf_bounded.subst _)) (.and (.rel _ _) (.and
    (.all (.bvar 2) (.exs (.bvar 0) .verum)) (.and
    (.all (.bvar 2) (.all (.bvar 2) (.or (isSubsetOf_bounded.subst _).neg (.rel _ _)))) (.and
    (.all (.bvar 2) (.all (.bvar 3) (.exs (.bvar 3) (.and
      (.all (.bvar 0) (.and (.rel _ _) (.rel _ _)))
      (.and (.all (.bvar 2) (.or (.nrel _ _) (.rel _ _))) (.rel _ _))))))
    (.all (.bvar 1) (.or (.rel _ _) (.exs (.bvar 2) (.and
      (.all (.bvar 0) (.and (.rel _ _) (.nrel _ _)))
      (.and (.all (.bvar 2) (.or (.rel _ _) (.rel _ _))) (.rel _ _))))))))))

/-- `z` belongs to every member of the family `g` indexed by `a`, whose values lie in `U`. -/
def familyMemberFormula : SetTheorySemisentence 4 :=
  “z a U g. ∀ i ∈ a, ∃ y ∈ U, !boundedPairMemberFormula g i y ∧ z ∈ y”

theorem familyMemberFormula_bounded : IsBoundedSetFormula familyMemberFormula := by
  exact .all (.bvar 1) (.exs (.bvar 3)
    (.and (boundedPairMemberFormula_bounded.subst _) (.rel _ _)))

/-- The intersection inside `S` of any family of members of `U` indexed by `a` is in `U`.
Here `P` is the power set of `S` and `W` the power set of `a ×ˢ U`. -/
def boundedCompleteAtFormula : SetTheorySemisentence 5 :=
  “S P W a U. ∀ g ∈ W, !boundedFunctionFormula g a U →
    ∃ Z ∈ P, (∀ z ∈ Z, z ∈ S ∧ !familyMemberFormula z a U g) ∧
      (∀ z ∈ S, !familyMemberFormula z a U g → z ∈ Z) ∧ Z ∈ U”

theorem boundedCompleteAtFormula_bounded : IsBoundedSetFormula boundedCompleteAtFormula := by
  exact .all (.bvar 2) (.or (boundedFunctionFormula_bounded.subst _).neg
    (.exs (.bvar 2) (.and
      (.all (.bvar 0) (.and (.rel _ _) (familyMemberFormula_bounded.subst _)))
      (.and (.all (.bvar 2) (.or (familyMemberFormula_bounded.subst _).neg (.rel _ _)))
        (.rel _ _)))))

/-- Every ordinal in `l` belongs to a member of `U`. -/
def boundedFineFormula : SetTheorySemisentence 4 :=
  “S P l U. ∀ u ∈ l, ∃ Z ∈ P, (∀ z ∈ Z, z ∈ S ∧ u ∈ z) ∧ (∀ z ∈ S, u ∈ z → z ∈ Z) ∧ Z ∈ U”

theorem boundedFineFormula_bounded : IsBoundedSetFormula boundedFineFormula := by
  exact .all (.bvar 2) (.exs (.bvar 2) (.and
    (.all (.bvar 0) (.and (.rel _ _) (.rel _ _)))
    (.and (.all (.bvar 2) (.or (.nrel _ _) (.rel _ _))) (.rel _ _))))

/-- The function `f` with values in `l` is regressive at `z`. -/
def regressiveAtFormula : SetTheorySemisentence 3 :=
  “z l f. ∃ y ∈ l, !boundedPairMemberFormula f z y ∧ y ∈ z”

theorem regressiveAtFormula_bounded : IsBoundedSetFormula regressiveAtFormula := by
  exact .exs (.bvar 1) (.and (boundedPairMemberFormula_bounded.subst _) (.rel _ _))

/-- The set of members of `S` where `f` is regressive belongs to `U`. -/
def regressiveInFormula : SetTheorySemisentence 5 :=
  “S P l U f. ∃ R ∈ P, (∀ z ∈ R, z ∈ S ∧ !regressiveAtFormula z l f) ∧
    (∀ z ∈ S, !regressiveAtFormula z l f → z ∈ R) ∧ R ∈ U”

theorem regressiveInFormula_bounded : IsBoundedSetFormula regressiveInFormula := by
  exact .exs (.bvar 1) (.and
    (.all (.bvar 0) (.and (.rel _ _) (regressiveAtFormula_bounded.subst _)))
    (.and (.all (.bvar 1) (.or (regressiveAtFormula_bounded.subst _).neg (.rel _ _)))
      (.rel _ _)))

/-- A function on `S` with values in `l` that is regressive on a set of `U` is constant on a
set of `U`. Here `P` is the power set of `S` and `F` the power set of `S ×ˢ l`. -/
def boundedNormalFormula : SetTheorySemisentence 5 :=
  “S P F l U. ∀ f ∈ F, !boundedFunctionFormula f S l → !regressiveInFormula S P l U f →
    ∃ u ∈ l, ∃ C ∈ P, (∀ z ∈ C, z ∈ S ∧ !boundedPairMemberFormula f z u) ∧
      (∀ z ∈ S, !boundedPairMemberFormula f z u → z ∈ C) ∧ C ∈ U”

theorem boundedNormalFormula_bounded : IsBoundedSetFormula boundedNormalFormula := by
  exact .all (.bvar 2) (.or (boundedFunctionFormula_bounded.subst _).neg
    (.or (regressiveInFormula_bounded.subst _).neg
      (.exs (.bvar 4) (.exs (.bvar 3) (.and
        (.all (.bvar 0) (.and (.rel _ _) (boundedPairMemberFormula_bounded.subst _)))
        (.and (.all (.bvar 3)
          (.or (boundedPairMemberFormula_bounded.subst _).neg (.rel _ _))) (.rel _ _)))))))

/-- "U is a normal fine measure on P_k(l)", with the base set introduced by
`smallSubsetsBelowFormula`. -/
def normalFineMeasureFormula : SetTheorySemisentence 3 :=
  “k l U. ∀ S, !smallSubsetsBelowFormula S k l → ∀ P, !powerSetGuardFormula P S →
    ∀ F, !pairSetGuardFormula F S l →
      !boundedUltrafilterFormula S P U ∧
      (∀ a, a ∈ k → ∀ W, !pairSetGuardFormula W a U → !boundedCompleteAtFormula S P W a U) ∧
      !boundedFineFormula S P l U ∧
      !boundedNormalFormula S P F l U”

theorem comp_vec2 {α β : Type*} (f : α → β) (a b : α) : f ∘ ![a, b] = ![f a, f b] := by
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i

theorem comp_vec3 {α β : Type*} (f : α → β) (a b c : α) : f ∘ ![a, b, c] = ![f a, f b, f c] := by
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i

theorem comp_vec4 {α β : Type*} (f : α → β) (a b c d : α) :
    f ∘ ![a, b, c, d] = ![f a, f b, f c, f d] := by
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
    (fun l ↦ Fin.cases rfl (fun m ↦ Fin.elim0 m) l) k) j) i

theorem comp_vec5 {α β : Type*} (f : α → β) (a b c d e : α) :
    f ∘ ![a, b, c, d, e] = ![f a, f b, f c, f d, f e] := by
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
    (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun n ↦ Fin.elim0 n) m) l) k) j) i

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A set carved out of `S` by a property is in `U` exactly when some set carved out that way
is; the outer bound `B` plays no part. -/
theorem exists_spec_mem_iff {B S U T : V} {p : V → Prop} (hT : ∀ z, z ∈ T ↔ z ∈ S ∧ p z)
    (hTB : T ⊆ B) :
    (∃ Z, Z ⊆ B ∧ (∀ z ∈ Z, z ∈ S ∧ p z) ∧ (∀ z ∈ S, p z → z ∈ Z) ∧ Z ∈ U) ↔ T ∈ U := by
  constructor
  · rintro ⟨Z, -, h1, h2, hZU⟩
    have hZT : Z = T := mem_ext fun z ↦
      ⟨fun hz ↦ (hT z).mpr (h1 z hz),
       fun hz ↦ h2 z ((hT z).mp hz).1 ((hT z).mp hz).2⟩
    exact hZT ▸ hZU
  · intro hTU
    exact ⟨T, hTB, fun z hz ↦ (hT z).mp hz, fun z hz hp ↦ (hT z).mpr ⟨hz, hp⟩, hTU⟩

/-- Fineness on `P_κ lam` is fineness for the base set `P_κ lam`. -/
theorem isFineOn_iff (κ lam U : V) :
    IsFineOn κ lam U ↔ ∀ u ∈ lam, fineSetOn (smallSubsetsBelow κ lam) u ∈ U := Iff.rfl

/-- Normality on `P_κ lam` is normality for the base set `P_κ lam`. -/
theorem isNormalOn_iff (κ lam U : V) :
    IsNormalOn κ lam U ↔ IsNormalIn (smallSubsetsBelow κ lam) lam U := Iff.rfl

theorem eval_powerSetGuardFormula (P S : V) :
    powerSetGuardFormula.Evalb ![P, S] ↔ P = ℘ S := by
  simp only [powerSetGuardFormula]
  simp
  constructor
  · rintro ⟨h1, h2⟩
    exact mem_ext fun y ↦ ⟨fun hy ↦ mem_power_iff.mpr (h1 y hy), fun hy ↦ h2 y (mem_power_iff.mp hy)⟩
  · rintro rfl
    exact ⟨fun y hy ↦ mem_power_iff.mp hy, fun y hy ↦ mem_power_iff.mpr hy⟩

theorem eval_pairSubsetFormula (w A B : V) :
    pairSubsetFormula.Evalb ![w, A, B] ↔ w ⊆ A ×ˢ B := by
  simp only [pairSubsetFormula]
  simp
  constructor
  · intro h p hp
    obtain ⟨a, ha, b, hb, hab⟩ := h p hp
    exact hab ▸ kpair_mem_iff.mpr ⟨ha, hb⟩
  · intro h p hp
    obtain ⟨a, ha, b, hb, hab⟩ := mem_prod_iff.mp (h p hp)
    exact ⟨a, ha, b, hb, hab⟩

theorem eval_pairSetGuardFormula (W A B : V) :
    pairSetGuardFormula.Evalb ![W, A, B] ↔ W = ℘ (A ×ˢ B) := by
  simp only [pairSetGuardFormula]
  simp [eval_pairSubsetFormula]
  constructor
  · rintro ⟨h1, h2⟩
    exact mem_ext fun w ↦ ⟨fun hw ↦ mem_power_iff.mpr (h1 w hw), fun hw ↦ h2 w (mem_power_iff.mp hw)⟩
  · rintro rfl
    exact ⟨fun w hw ↦ mem_power_iff.mp hw, fun w hw ↦ mem_power_iff.mpr hw⟩

theorem eval_boundedUltrafilterFormula (S U : V) :
    boundedUltrafilterFormula.Evalb ![S, ℘ S, U] ↔ IsSetUltrafilter S U := by
  have hne : ∀ X : V, (∃ z, z ∈ X) ↔ X ≠ ∅ := by
    intro X
    constructor
    · rintro ⟨z, hz⟩ rfl
      exact not_mem_empty hz
    · intro h
      by_contra hc
      exact h (mem_ext fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hc, fun hz ↦ (not_mem_empty hz).elim⟩)
  simp only [boundedUltrafilterFormula]
  simp
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun X hX ↦ mem_power_iff.mpr (h1 X hX), h2, fun hE ↦ (hne ∅).mp (h3 ∅ hE) rfl,
      h4, fun X hX Y hY ↦ ?_, fun X hX ↦ (h6 X hX).imp id fun hc ↦ ?_⟩
    · exact (exists_spec_mem_iff (S := X) (B := S) (T := X ∩ Y) (p := fun z ↦ z ∈ Y)
        (fun z ↦ mem_inter_iff) (fun z hz ↦ h1 X hX z (mem_inter_iff.mp hz).1)).mp (h5 X hX Y hY)
    · exact (exists_spec_mem_iff (S := S) (B := S) (T := relativeComplement S X)
        (p := fun z ↦ z ∉ X) (fun z ↦ mem_relativeComplement_iff z S X)
        (fun z hz ↦ (mem_relativeComplement_iff z S X).mp hz |>.1)).mp hc
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun X hX ↦ mem_power_iff.mp (h1 X hX), h2, fun X hX ↦ (hne X).mpr ?_, h4,
      fun X hX Y hY ↦ ?_, fun X hX ↦ (h6 X hX).imp id fun hc ↦ ?_⟩
    · rintro rfl
      exact h3 hX
    · exact (exists_spec_mem_iff (S := X) (B := S) (T := X ∩ Y) (p := fun z ↦ z ∈ Y)
        (fun z ↦ mem_inter_iff)
        (fun z hz ↦ mem_power_iff.mp (h1 X hX) z (mem_inter_iff.mp hz).1)).mpr (h5 X hX Y hY)
    · exact (exists_spec_mem_iff (S := S) (B := S) (T := relativeComplement S X)
        (p := fun z ↦ z ∉ X) (fun z ↦ mem_relativeComplement_iff z S X)
        (fun z hz ↦ (mem_relativeComplement_iff z S X).mp hz |>.1)).mpr hc

theorem eval_familyMemberFormula {a U g : V} (hg : g ∈ U ^ a) (z : V) :
    familyMemberFormula.Evalb ![z, a, U, g] ↔ ∀ i ∈ a, z ∈ g ‘ i := by
  let := IsFunction.of_mem hg
  simp only [familyMemberFormula]
  simp
  constructor
  · intro h i hi
    obtain ⟨y, -, hp, hz⟩ := h i hi
    rw [value_eq_of_kpair_mem hp]
    exact hz
  · intro h i hi
    exact ⟨g ‘ i, function_value_mem hg hi,
      kpair_value_mem ((domain_eq_of_mem_function hg).symm ▸ hi), h i hi⟩

theorem eval_boundedCompleteAtFormula (S a U : V) :
    boundedCompleteAtFormula.Evalb ![S, ℘ S, ℘ (a ×ˢ U), a, U] ↔
      ∀ g ∈ U ^ a, indexedIntersection S a g ∈ U := by
  have hT : ∀ g ∈ U ^ a, ∀ z : V,
      z ∈ indexedIntersection S a g ↔ z ∈ S ∧ familyMemberFormula.Evalb ![z, a, U, g] := by
    intro g hg z
    rw [eval_familyMemberFormula hg z, mem_indexedIntersection_iff]
  have hsub : ∀ g : V, indexedIntersection S a g ⊆ S :=
    fun g z hz ↦ ((mem_indexedIntersection_iff z S a g).mp hz).1
  simp only [boundedCompleteAtFormula]
  simp
  constructor
  · intro h g hg
    exact (exists_spec_mem_iff (hT g hg) (hsub g)).mp (h g (subset_prod_of_mem_function hg) hg)
  · intro h g _ hg
    exact (exists_spec_mem_iff (hT g hg) (hsub g)).mpr (h g hg)

theorem eval_boundedFineFormula (S l U : V) :
    boundedFineFormula.Evalb ![S, ℘ S, l, U] ↔ ∀ u ∈ l, fineSetOn S u ∈ U := by
  simp only [boundedFineFormula]
  simp
  constructor
  · intro h u hu
    exact (exists_spec_mem_iff (S := S) (B := S) (T := fineSetOn S u) (p := fun z ↦ u ∈ z)
      (fun z ↦ by simp [fineSetOn]) (fun z hz ↦ (mem_sep_iff.mp hz).1)).mp (h u hu)
  · intro h u hu
    exact (exists_spec_mem_iff (S := S) (B := S) (T := fineSetOn S u) (p := fun z ↦ u ∈ z)
      (fun z ↦ by simp [fineSetOn]) (fun z hz ↦ (mem_sep_iff.mp hz).1)).mpr (h u hu)

theorem eval_regressiveAtFormula {S l f : V} (hf : f ∈ l ^ S) {z : V} (hz : z ∈ S) :
    regressiveAtFormula.Evalb ![z, l, f] ↔ f ‘ z ∈ z := by
  let := IsFunction.of_mem hf
  simp only [regressiveAtFormula]
  simp
  constructor
  · rintro ⟨y, -, hp, hy⟩
    rwa [value_eq_of_kpair_mem hp]
  · intro h
    exact ⟨f ‘ z, function_value_mem hf hz,
      kpair_value_mem ((domain_eq_of_mem_function hf).symm ▸ hz), h⟩

theorem eval_regressiveInFormula {S l U f : V} (hf : f ∈ l ^ S) :
    regressiveInFormula.Evalb ![S, ℘ S, l, U, f] ↔ regressiveSetOn S f ∈ U := by
  simp only [regressiveInFormula]
  simp
  exact exists_spec_mem_iff (S := S) (B := S) (T := regressiveSetOn S f)
    (p := fun z ↦ regressiveAtFormula.Evalb ![z, l, f])
    (fun z ↦ by
      simp only [regressiveSetOn, mem_sep_iff]
      exact ⟨fun hz ↦ ⟨hz.1, (eval_regressiveAtFormula hf hz.1).mpr hz.2⟩,
        fun hz ↦ ⟨hz.1, (eval_regressiveAtFormula hf hz.1).mp hz.2⟩⟩)
    (fun z hz ↦ (mem_sep_iff.mp hz).1)

theorem eval_boundedNormalFormula (S l U : V) :
    boundedNormalFormula.Evalb ![S, ℘ S, ℘ (S ×ˢ l), l, U] ↔ IsNormalIn S l U := by
  have hT : ∀ f ∈ l ^ S, ∀ u z : V,
      z ∈ constantSetOn S f u ↔ z ∈ S ∧ ⟨z, u⟩ₖ ∈ f := by
    intro f hf u z
    let := IsFunction.of_mem hf
    rw [constantSetOn, mem_sep_iff, kpair_mem_iff_value, domain_eq_of_mem_function hf]
    exact ⟨fun h ↦ ⟨h.1, h⟩, fun h ↦ h.2⟩
  have hsub : ∀ f u : V, constantSetOn S f u ⊆ S :=
    fun f u z hz ↦ (mem_sep_iff.mp hz).1
  simp only [boundedNormalFormula]
  simp [comp_vec5]
  constructor
  · intro h f hf hreg
    obtain ⟨u, hu, hc⟩ := h f (subset_prod_of_mem_function hf) hf
      ((eval_regressiveInFormula hf).mpr hreg)
    exact ⟨u, hu, (exists_spec_mem_iff (hT f hf u) (hsub f u)).mp hc⟩
  · intro h f _ hf hreg
    obtain ⟨u, hu, hc⟩ := h f hf ((eval_regressiveInFormula hf).mp hreg)
    exact ⟨u, hu, (exists_spec_mem_iff (hT f hf u) (hsub f u)).mpr hc⟩

theorem eval_normalFineMeasureFormula (κ lam U : V) :
    normalFineMeasureFormula.Evalb ![κ, lam, U] ↔ IsNormalFineMeasure κ lam U := by
  simp only [normalFineMeasureFormula]
  simp [comp_vec5]
  simp only [eval_smallSubsetsBelowFormula, eval_powerSetGuardFormula, eval_pairSetGuardFormula]
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := h _ rfl _ rfl _ rfl
    refine ⟨(eval_boundedUltrafilterFormula _ _).mp h1, fun a ha g hg ↦ ?_,
      (isFineOn_iff κ lam U).mpr ((eval_boundedFineFormula _ _ _).mp h3),
      (isNormalOn_iff κ lam U).mpr ((eval_boundedNormalFormula _ _ _).mp h4)⟩
    exact (eval_boundedCompleteAtFormula _ _ _).mp (h2 a ha _ rfl) g hg
  · rintro ⟨h1, h2, h3, h4⟩ S rfl P rfl F rfl
    refine ⟨(eval_boundedUltrafilterFormula _ _).mpr h1, fun a ha W hW ↦ ?_,
      (eval_boundedFineFormula _ _ _).mpr ((isFineOn_iff κ lam U).mp h3),
      (eval_boundedNormalFormula _ _ _).mpr ((isNormalOn_iff κ lam U).mp h4)⟩
    subst hW
    exact (eval_boundedCompleteAtFormula _ _ _).mpr (h2 a ha)

section Stage

variable {δ : V} [IsOrdinal δ]

/-- Inclusion in a rank stage is the real inclusion. -/
theorem stage_subset_iff {S : V} (hS : S ∈ hierarchy δ) (x : SetDomain (hierarchy δ)) :
    x ⊆ (⟨S, hS⟩ : SetDomain (hierarchy δ)) ↔ x.val ⊆ S :=
  setDomain_subset_iff (hierarchy_transitive δ) x ⟨S, hS⟩

theorem eval_powerSetGuardFormula_stage (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ) {P S : V}
    (hP : P ∈ hierarchy δ) (hS : S ∈ hierarchy δ) :
    powerSetGuardFormula.Evalb (![⟨P, hP⟩, ⟨S, hS⟩] : Fin 2 → SetDomain (hierarchy δ)) ↔
      P = ℘ S := by
  let := hierarchy_transitive δ
  simp only [powerSetGuardFormula]
  simp [stage_subset_iff hS]
  constructor
  · rintro ⟨h1, h2⟩
    refine mem_ext fun y ↦ ⟨fun hy ↦ mem_power_iff.mpr ?_, fun hy ↦ ?_⟩
    · exact h1 ⟨y, (hierarchy_transitive δ).mem_trans hy hP⟩ hy
    · exact h2 ⟨y, subset_mem_hierarchy_limit hδ hS (mem_power_iff.mp hy)⟩ (mem_power_iff.mp hy)
  · rintro rfl
    exact ⟨fun y hy ↦ mem_power_iff.mp hy, fun y hy ↦ mem_power_iff.mpr hy⟩

theorem eval_pairSubsetFormula_stage {A B : V} (hA : A ∈ hierarchy δ) (hB : B ∈ hierarchy δ)
    (w : SetDomain (hierarchy δ)) :
    pairSubsetFormula.Evalb (![w, ⟨A, hA⟩, ⟨B, hB⟩] : Fin 3 → SetDomain (hierarchy δ)) ↔
      w.val ⊆ A ×ˢ B := by
  let := hierarchy_transitive δ
  have hv : (fun i ↦ ((![w, ⟨A, hA⟩, ⟨B, hB⟩] : Fin 3 → SetDomain (hierarchy δ)) i).val)
      = ![w.val, A, B] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.elim0 l) k) j) i
  rw [bounded_formula_absolute (hierarchy δ) pairSubsetFormula_bounded, hv]
  exact eval_pairSubsetFormula _ _ _

theorem eval_pairSetGuardFormula_stage (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ) {W A B : V}
    (hW : W ∈ hierarchy δ) (hA : A ∈ hierarchy δ) (hB : B ∈ hierarchy δ) :
    pairSetGuardFormula.Evalb (![⟨W, hW⟩, ⟨A, hA⟩, ⟨B, hB⟩] : Fin 3 → SetDomain (hierarchy δ)) ↔
      W = ℘ (A ×ˢ B) := by
  let := hierarchy_transitive δ
  have hprod : A ×ˢ B ∈ hierarchy δ := prod_mem_hierarchy_limit hδ hA hB
  simp only [pairSetGuardFormula]
  simp [eval_pairSubsetFormula_stage hA hB]
  constructor
  · rintro ⟨h1, h2⟩
    refine mem_ext fun w ↦ ⟨fun hw ↦ mem_power_iff.mpr ?_, fun hw ↦ ?_⟩
    · exact h1 ⟨w, (hierarchy_transitive δ).mem_trans hw hW⟩ hw
    · exact h2 ⟨w, subset_mem_hierarchy_limit hδ hprod (mem_power_iff.mp hw)⟩ (mem_power_iff.mp hw)
  · rintro rfl
    exact ⟨fun w hw ↦ mem_power_iff.mp hw, fun w hw ↦ mem_power_iff.mpr hw⟩

theorem eval_boundedUltrafilterFormula_stage {S U : V} (hS : S ∈ hierarchy δ)
    (hP : ℘ S ∈ hierarchy δ) (hU : U ∈ hierarchy δ) :
    boundedUltrafilterFormula.Evalb
        (![⟨S, hS⟩, ⟨℘ S, hP⟩, ⟨U, hU⟩] : Fin 3 → SetDomain (hierarchy δ)) ↔
      IsSetUltrafilter S U := by
  let := hierarchy_transitive δ
  have hv : (fun i ↦ ((![⟨S, hS⟩, ⟨℘ S, hP⟩, ⟨U, hU⟩] : Fin 3 → SetDomain (hierarchy δ)) i).val)
      = ![S, ℘ S, U] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.elim0 l) k) j) i
  rw [bounded_formula_absolute (hierarchy δ) boundedUltrafilterFormula_bounded, hv]
  exact eval_boundedUltrafilterFormula _ _

theorem eval_boundedCompleteAtFormula_stage {S a U : V} (hS : S ∈ hierarchy δ)
    (hP : ℘ S ∈ hierarchy δ) (hW : ℘ (a ×ˢ U) ∈ hierarchy δ) (ha : a ∈ hierarchy δ)
    (hU : U ∈ hierarchy δ) :
    boundedCompleteAtFormula.Evalb
        (![⟨S, hS⟩, ⟨℘ S, hP⟩, ⟨℘ (a ×ˢ U), hW⟩, ⟨a, ha⟩, ⟨U, hU⟩] :
          Fin 5 → SetDomain (hierarchy δ)) ↔
      ∀ g ∈ U ^ a, indexedIntersection S a g ∈ U := by
  let := hierarchy_transitive δ
  have hv : (fun i ↦ ((![⟨S, hS⟩, ⟨℘ S, hP⟩, ⟨℘ (a ×ˢ U), hW⟩, ⟨a, ha⟩, ⟨U, hU⟩] :
      Fin 5 → SetDomain (hierarchy δ)) i).val) = ![S, ℘ S, ℘ (a ×ˢ U), a, U] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun n ↦ Fin.elim0 n) m) l) k) j) i
  rw [bounded_formula_absolute (hierarchy δ) boundedCompleteAtFormula_bounded, hv]
  exact eval_boundedCompleteAtFormula _ _ _

theorem eval_boundedFineFormula_stage {S l U : V} (hS : S ∈ hierarchy δ)
    (hP : ℘ S ∈ hierarchy δ) (hl : l ∈ hierarchy δ) (hU : U ∈ hierarchy δ) :
    boundedFineFormula.Evalb
        (![⟨S, hS⟩, ⟨℘ S, hP⟩, ⟨l, hl⟩, ⟨U, hU⟩] : Fin 4 → SetDomain (hierarchy δ)) ↔
      ∀ u ∈ l, fineSetOn S u ∈ U := by
  let := hierarchy_transitive δ
  have hv : (fun i ↦ ((![⟨S, hS⟩, ⟨℘ S, hP⟩, ⟨l, hl⟩, ⟨U, hU⟩] :
      Fin 4 → SetDomain (hierarchy δ)) i).val) = ![S, ℘ S, l, U] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.elim0 m) l) k) j) i
  rw [bounded_formula_absolute (hierarchy δ) boundedFineFormula_bounded, hv]
  exact eval_boundedFineFormula _ _ _

theorem eval_boundedNormalFormula_stage {S l U : V} (hS : S ∈ hierarchy δ)
    (hP : ℘ S ∈ hierarchy δ) (hF : ℘ (S ×ˢ l) ∈ hierarchy δ) (hl : l ∈ hierarchy δ)
    (hU : U ∈ hierarchy δ) :
    boundedNormalFormula.Evalb
        (![⟨S, hS⟩, ⟨℘ S, hP⟩, ⟨℘ (S ×ˢ l), hF⟩, ⟨l, hl⟩, ⟨U, hU⟩] :
          Fin 5 → SetDomain (hierarchy δ)) ↔
      IsNormalIn S l U := by
  let := hierarchy_transitive δ
  have hv : (fun i ↦ ((![⟨S, hS⟩, ⟨℘ S, hP⟩, ⟨℘ (S ×ˢ l), hF⟩, ⟨l, hl⟩, ⟨U, hU⟩] :
      Fin 5 → SetDomain (hierarchy δ)) i).val) = ![S, ℘ S, ℘ (S ×ˢ l), l, U] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun n ↦ Fin.elim0 n) m) l) k) j) i
  rw [bounded_formula_absolute (hierarchy δ) boundedNormalFormula_bounded, hv]
  exact eval_boundedNormalFormula _ _ _

/-- Read inside a rank stage closed under successor, the measure formula says what it says
outside. -/
theorem eval_normalFineMeasureFormula_stage (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ)
    {κ lam U : V} (hκ : κ ∈ hierarchy δ) (hlam : lam ∈ hierarchy δ) (hU : U ∈ hierarchy δ) :
    normalFineMeasureFormula.Evalb
        (![⟨κ, hκ⟩, ⟨lam, hlam⟩, ⟨U, hU⟩] : Fin 3 → SetDomain (hierarchy δ)) ↔
      IsNormalFineMeasure κ lam U := by
  let := hierarchy_transitive δ
  have hS : smallSubsetsBelow κ lam ∈ hierarchy δ := smallSubsetsBelow_mem_hierarchy hδ hκ hlam
  have hPS : ℘ (smallSubsetsBelow κ lam) ∈ hierarchy δ := power_mem_hierarchy_limit hδ hS
  have hFS : ℘ (smallSubsetsBelow κ lam ×ˢ lam) ∈ hierarchy δ :=
    power_mem_hierarchy_limit hδ (prod_mem_hierarchy_limit hδ hS hlam)
  simp only [normalFineMeasureFormula]
  simp [comp_vec5]
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := h ⟨_, hS⟩
      ((eval_smallSubsetsBelowFormula_stage hδ hS hκ hlam).mpr rfl) ⟨_, hPS⟩
      ((eval_powerSetGuardFormula_stage hδ hPS hS).mpr rfl) ⟨_, hFS⟩
      ((eval_pairSetGuardFormula_stage hδ hFS hS hlam).mpr rfl)
    have hnorm := (eval_boundedNormalFormula_stage hS hPS hFS hlam hU).mp h4
    refine ⟨(eval_boundedUltrafilterFormula_stage hS hPS hU).mp h1, ?_,
      (isFineOn_iff κ lam U).mpr ((eval_boundedFineFormula_stage hS hPS hlam hU).mp h3),
      (isNormalOn_iff κ lam U).mpr hnorm⟩
    intro a ha
    have haH : a ∈ hierarchy δ := (hierarchy_transitive δ).mem_trans ha hκ
    have hW : ℘ (a ×ˢ U) ∈ hierarchy δ :=
      power_mem_hierarchy_limit hδ (prod_mem_hierarchy_limit hδ haH hU)
    exact (eval_boundedCompleteAtFormula_stage hS hPS hW haH hU).mp
      (h2 ⟨a, haH⟩ ha ⟨_, hW⟩ ((eval_pairSetGuardFormula_stage hδ hW haH hU).mpr rfl))
  · rintro ⟨h1, h2, h3, h4⟩ ⟨S, hSm⟩ hSg ⟨P, hPm⟩ hPg ⟨F, hFm⟩ hFg
    rw [eval_smallSubsetsBelowFormula_stage hδ hSm hκ hlam] at hSg
    subst hSg
    rw [eval_powerSetGuardFormula_stage hδ hPm hSm] at hPg
    subst hPg
    rw [eval_pairSetGuardFormula_stage hδ hFm hSm hlam] at hFg
    subst hFg
    refine ⟨(eval_boundedUltrafilterFormula_stage hSm hPm hU).mpr h1, ?_,
      (eval_boundedFineFormula_stage hSm hPm hlam hU).mpr ((isFineOn_iff κ lam U).mp h3),
      (eval_boundedNormalFormula_stage hSm hPm hFm hlam hU).mpr ((isNormalOn_iff κ lam U).mp h4)⟩
    rintro ⟨a, haH⟩ ha ⟨W, hWm⟩ hWg
    rw [eval_pairSetGuardFormula_stage hδ hWm haH hU] at hWg
    subst hWg
    exact (eval_boundedCompleteAtFormula_stage hSm hPm hWm haH hU).mpr (h2 a ha)

/-- A bounded formula read inside a rank stage says what it says outside. -/
theorem bounded_stage_iff {n : ℕ} {φ : SetTheorySemisentence n} (hφ : IsBoundedSetFormula φ)
    {R : (Fin n → V) → Prop} [Defined R φ] (b : Fin n → SetDomain (hierarchy δ)) :
    φ.Evalb b ↔ R (fun i ↦ (b i).val) := by
  let := hierarchy_transitive δ
  rw [bounded_formula_absolute (hierarchy δ) hφ]
  exact Defined.eval_iff _

/-- Being an ordinal in a rank stage is being an ordinal. -/
theorem stage_ordinal_iff (x : SetDomain (hierarchy δ)) : IsOrdinal x ↔ IsOrdinal x.val := by
  have h : (IsOrdinal.dfn : SetTheorySemisentence 1).Evalb ![x] ↔ IsOrdinal x := by simp
  rw [← h]
  exact bounded_stage_iff isOrdinalFormula_bounded (R := fun v ↦ IsOrdinal (v 0)) ![x]

theorem eval_piOneInitialOrdinalFormula_stage (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ) {a : V}
    (ha : a ∈ hierarchy δ) :
    piOneInitialOrdinalFormula.Evalb (![⟨a, ha⟩] : Fin 1 → SetDomain (hierarchy δ)) ↔
      IsInitialOrdinal a := by
  let := hierarchy_transitive δ
  simp only [piOneInitialOrdinalFormula]
  simp
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(stage_ordinal_iff ⟨a, ha⟩).mp h1, fun α hα hle ↦ ?_⟩
    have hαH : α ∈ hierarchy δ := (hierarchy_transitive δ).mem_trans hα ha
    obtain ⟨g, hg⟩ := (exists_injection_stage hδ ⟨a, ha⟩ ⟨α, hαH⟩).mpr hle
    exact h2 ⟨α, hαH⟩ hα g hg
  · rintro ⟨h1, h2⟩
    refine ⟨(stage_ordinal_iff ⟨a, ha⟩).mpr h1, fun α hα g hg ↦ ?_⟩
    exact h2 α.val hα ((exists_injection_stage hδ ⟨a, ha⟩ α).mp ⟨g, hg⟩)

/-- "a is an initial ordinal above omega carrying a normal fine measure on `P_a(lam)` for every
ordinal `lam` at or above `a`". -/
def supercompactStageFormula : SetTheorySemisentence 1 :=
  “a. !piOneInitialOrdinalFormula a ∧ (∃ w, !boundedOmegaFormula w ∧ w ∈ a) ∧
    ∀ l, !IsOrdinal.dfn l → a ⊆ l → ∃ U, !normalFineMeasureFormula a l U”

/-- Inside a rank stage closed under successor and containing `ω`, the sentence says that `a`
is an initial ordinal above `ω` with a normal fine measure on `P_a(lam)` for every ordinal
`lam` of the stage at or above `a`. -/
theorem eval_supercompactStageFormula (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ) (hω : (ω : V) ∈ δ)
    {a : V} (ha : a ∈ hierarchy δ) :
    supercompactStageFormula.Evalb (![⟨a, ha⟩] : Fin 1 → SetDomain (hierarchy δ)) ↔
      (IsInitialOrdinal a ∧ (ω : V) ∈ a ∧
        ∀ lam ∈ δ, a ⊆ lam → ∃ U, IsNormalFineMeasure a lam U) := by
  let := hierarchy_transitive δ
  have hωH : (ω : V) ∈ hierarchy δ := ordinal_mem_hierarchy_iff.mpr hω
  have homega : ∀ w : SetDomain (hierarchy δ),
      boundedOmegaFormula.Evalb (![w] : Fin 1 → SetDomain (hierarchy δ)) ↔ w.val = (ω : V) :=
    fun w ↦ bounded_stage_iff boundedOmegaFormula_bounded (R := fun v ↦ v 0 = (ω : V)) ![w]
  simp only [supercompactStageFormula]
  simp [eval_piOneInitialOrdinalFormula_stage hδ ha, homega,
    setDomain_subset_iff (hierarchy_transitive δ) ⟨a, ha⟩]
  intro _
  constructor
  · rintro ⟨⟨w, hw, hwa⟩, h3⟩
    refine ⟨by rw [← hw]; exact hwa, fun lam hlam hsub ↦ ?_⟩
    have hlo : IsOrdinal lam := IsOrdinal.of_mem hlam
    have hlH : lam ∈ hierarchy δ := ordinal_mem_hierarchy_iff.mpr hlam
    obtain ⟨U, hU⟩ := h3 ⟨lam, hlH⟩ ((stage_ordinal_iff ⟨lam, hlH⟩).mpr hlo) hsub
    exact ⟨U.val, (eval_normalFineMeasureFormula_stage hδ ha hlH U.property).mp hU⟩
  · rintro ⟨h2, h3⟩
    refine ⟨⟨⟨(ω : V), hωH⟩, rfl, h2⟩, fun l hl hsub ↦ ?_⟩
    have hlo : IsOrdinal l.val := (stage_ordinal_iff l).mp hl
    have hlδ : l.val ∈ δ := ordinal_mem_hierarchy_iff.mp l.property
    obtain ⟨U, hU⟩ := h3 l.val hlδ hsub
    have hSm : smallSubsetsBelow a l.val ∈ hierarchy δ :=
      smallSubsetsBelow_mem_hierarchy hδ ha l.property
    have hUm : U ∈ hierarchy δ := subsets_mem_hierarchy hδ hSm hU.1.1
    exact ⟨⟨U, hUm⟩, (eval_normalFineMeasureFormula_stage hδ ha l.property hUm).mpr hU⟩

end Stage

end ZFVP
