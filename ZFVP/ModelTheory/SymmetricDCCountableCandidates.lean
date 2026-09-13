import ZFVP.ModelTheory.SymmetricModelGraph
import ZFVP.SetTheory.SymmetricSequenceNames
import ZFVP.SetTheory.ForcingClosure
import ZFVP.SetTheory.DependentChoice
import ZFVP.SetTheory.ForcingDependentChoicePaths
import ZFVP.SetTheory.EndExtensionCoding

/-! Karagila, Preserving dependent choice, Lemma 3.1 in the form used by the paper:
a symmetric extension by a forcing closed under descending omega-sequences, with a
filter closed under countable intersections, satisfies dependent choice whenever the
ground model does. The chain of conditions and hereditarily symmetric subnames is
built in the ground model by dependent choice; the sequence name of its subnames is
hereditarily symmetric, so its value is a dependent-choice sequence in the symmetric model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def symmetricDCMemberFormula : SetTheorySemisentence 2 := f“x A. x ∈ A”

def serialFormula : SetTheorySemisentence 2 := f“A B. ∀ x ∈ A, ∃ y ∈ A, !kpair.dfn x y ∈ B”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_symmetricDCMemberFormula (v : Fin 2 → V) : symmetricDCMemberFormula.Evalb v ↔ v 0 ∈ v 1 := by
  simp [symmetricDCMemberFormula]

theorem eval_serialFormula (v : Fin 2 → V) :
    serialFormula.Evalb v ↔ ∀ x ∈ v 0, ∃ y ∈ v 0, ⟨x, y⟩ₖ ∈ v 1 := by
  simp [serialFormula]

theorem eval_boundedNonemptyFormula_assignment (v : Fin 1 → V) :
    boundedNonemptyFormula.Evalb v ↔ IsNonempty (v 0) := by
  simp [boundedNonemptyFormula, isNonempty_def]

namespace SymmetricContext

variable (S : SymmetricContext V)

/-- The same symmetric system with another external generic. -/
noncomputable def withGeneric (H : Set V) (hH : IsExternalForcingGeneric S.P S.R H) :
    SymmetricContext V where
  P := S.P
  R := S.R
  one := S.one
  G := H
  order := S.order
  top := S.top
  generic := hH
  Γ := S.Γ
  F := S.F
  poset := S.poset
  group := S.group
  normal := S.normal

theorem subname_hereditarilySymmetric (τ : S.Name) {σ : V} (hσ : σ ∈ domain τ.val) :
    IsHereditarilySymmetricName S.P S.Γ S.F σ := by
  obtain ⟨p, hp⟩ := mem_domain_iff.mp hσ
  exact ((hereditarilySymmetric_iff _ _ _ _).mp τ.property).2 σ p hp

theorem tuple_val_one (σ : S.Name) :
    (fun i ↦ ((![σ] : Fin 1 → S.Name) i).val) = ![σ.val] := by
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i

theorem tuple_val_two (σ τ : S.Name) :
    (fun i ↦ ((![σ, τ] : Fin 2 → S.Name) i).val) = ![σ.val, τ.val] := by
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i

theorem tuple_val_four (σ τ υ ρ : S.Name) :
    (fun i ↦ ((![σ, τ, υ, ρ] : Fin 4 → S.Name) i).val) = ![σ.val, τ.val, υ.val, ρ.val] := by
  funext i
  refine Fin.cases rfl (fun j ↦ Fin.cases rfl (fun l ↦ Fin.cases rfl
    (fun t ↦ Fin.cases rfl (fun s ↦ Fin.elim0 s) t) l) j) i

/-- Candidates below `q`: a condition below `q` and a subname of `τA` forced into `τA`. -/
noncomputable def chainCandidates (τA q : V) : V :=
  {z ∈ S.P ×ˢ domain τA ; ⟨kpair.π₁ z, q⟩ₖ ∈ S.R ∧
    kpair.π₁ z ∈ symmetricForcingFormula S.P S.R S.Γ S.F symmetricDCMemberFormula
      (standardTuple ![kpair.π₂ z, τA])}

theorem pair_mem_chainCandidates (τA q r σ : V) :
    ⟨r, σ⟩ₖ ∈ S.chainCandidates τA q ↔ r ∈ S.P ∧ σ ∈ domain τA ∧ ⟨r, q⟩ₖ ∈ S.R ∧
      r ∈ symmetricForcingFormula S.P S.R S.Γ S.F symmetricDCMemberFormula (standardTuple ![σ, τA]) := by
  simp only [chainCandidates, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

theorem mem_chainCandidates {τA q z : V} (hz : z ∈ S.chainCandidates τA q) :
    kpair.π₁ z ∈ S.P ∧ kpair.π₂ z ∈ domain τA ∧ ⟨kpair.π₁ z, q⟩ₖ ∈ S.R ∧
      kpair.π₁ z ∈ symmetricForcingFormula S.P S.R S.Γ S.F symmetricDCMemberFormula
        (standardTuple ![kpair.π₂ z, τA]) := by
  obtain ⟨a, _, b, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using (S.pair_mem_chainCandidates τA q a b).mp hz

/-- One step of the chain: a stronger condition forcing the next subname into `τA` and
the pair into `τB`. -/
noncomputable def chainRelation (τA τB q : V) : V :=
  {w ∈ S.chainCandidates τA q ×ˢ S.chainCandidates τA q ;
    ⟨kpair.π₁ (kpair.π₂ w), kpair.π₁ (kpair.π₁ w)⟩ₖ ∈ S.R ∧
    kpair.π₁ (kpair.π₂ w) ∈ symmetricForcingFormula S.P S.R S.Γ S.F dependentChoiceNextFormula
      (standardTuple ![kpair.π₂ (kpair.π₁ w), kpair.π₂ (kpair.π₂ w), τA, τB])}

theorem pair_mem_chainRelation (τA τB q z w : V) :
    ⟨z, w⟩ₖ ∈ S.chainRelation τA τB q ↔
      z ∈ S.chainCandidates τA q ∧ w ∈ S.chainCandidates τA q ∧
      ⟨kpair.π₁ w, kpair.π₁ z⟩ₖ ∈ S.R ∧
      kpair.π₁ w ∈ symmetricForcingFormula S.P S.R S.Γ S.F dependentChoiceNextFormula
        (standardTuple ![kpair.π₂ z, kpair.π₂ w, τA, τB]) := by
  simp only [chainRelation, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

/-- Below every condition forcing nonemptiness there is a candidate. -/
theorem chainCandidates_nonempty_countable [Countable V] (τA : S.Name) {p q : V}
    (hne : p ∈ symmetricForcingFormula S.P S.R S.Γ S.F boundedNonemptyFormula
      (standardTuple ![τA.val]))
    (hq : q ∈ S.P) (hqp : ⟨q, p⟩ₖ ∈ S.R) : IsNonempty (S.chainCandidates τA.val q) := by
  obtain ⟨H, hH, hqH⟩ := exists_externalForcingGeneric S.order hq
  let T := S.withGeneric H hH
  have hpP : p ∈ S.P := (symmetricForcingFormula_regular S.order _ _ _ _).1 p hne
  have hpH : p ∈ H := hH.1.2.2.1 q hqH p hpP hqp
  have hAne : boundedNonemptyFormula.Evalb (fun i ↦ T.ofName (![τA] i)) := by
    apply (T.formula_truth boundedNonemptyFormula ![τA]).mpr
    show GenericMeets H (symmetricForcingFormula S.P S.R S.Γ S.F boundedNonemptyFormula
      (standardTuple (fun i ↦ ((![τA] : Fin 1 → S.Name) i).val)))
    rw [S.tuple_val_one]
    exact ⟨p, hpH, hne⟩
  obtain ⟨x, hx⟩ := (eval_boundedNonemptyFormula_assignment _).mp hAne
  obtain ⟨ν0, s, _, hνs, rfl⟩ := (T.mem_ofName_iff τA x).mp hx
  let ν : S.Name := ⟨ν0.val, ν0.property⟩
  have hνd : ν.val ∈ domain τA.val := mem_domain_of_kpair_mem hνs
  have hmem : symmetricDCMemberFormula.Evalb (fun i ↦ T.ofName (![ν, τA] i)) :=
    (eval_symmetricDCMemberFormula _).mpr hx
  obtain ⟨r', hr'H, hr'0⟩ := (T.formula_truth symmetricDCMemberFormula ![ν, τA]).mp hmem
  have hr' : r' ∈ symmetricForcingFormula S.P S.R S.Γ S.F symmetricDCMemberFormula
      (standardTuple (fun i ↦ ((![ν, τA] : Fin 2 → S.Name) i).val)) := hr'0
  rw [S.tuple_val_two] at hr'
  obtain ⟨r, hrH, hrr', hrq⟩ := hH.1.2.2.2 r' hr'H q hqH
  have hrP : r ∈ S.P := hH.1.1 r hrH
  refine ⟨⟨r, ν.val⟩ₖ, (S.pair_mem_chainCandidates _ _ _ _).mpr ⟨hrP, hνd, hrq, ?_⟩⟩
  exact (symmetricForcingFormula_regular S.order _ _ _ _).2.1 r' hr' r hrP hrr'

/-- Every candidate has a successor once seriality is forced. -/
theorem chainRelation_serial_countable [Countable V] (τA τB : S.Name) {p q : V}
    (hser : p ∈ symmetricForcingFormula S.P S.R S.Γ S.F serialFormula
      (standardTuple ![τA.val, τB.val]))
    (hq : q ∈ S.P) (hqp : ⟨q, p⟩ₖ ∈ S.R) :
    ∀ z ∈ S.chainCandidates τA.val q, ∃ w ∈ S.chainCandidates τA.val q,
      ⟨z, w⟩ₖ ∈ S.chainRelation τA.val τB.val q := by
  intro z hz
  obtain ⟨hq'P, hσd, hq'q, hq'mem⟩ := S.mem_chainCandidates hz
  obtain ⟨H, hH, hq'H⟩ := exists_externalForcingGeneric S.order hq'P
  let T := S.withGeneric H hH
  have hpP : p ∈ S.P := (symmetricForcingFormula_regular S.order _ _ _ _).1 p hser
  have hq'p : ⟨kpair.π₁ z, p⟩ₖ ∈ S.R := S.order.2.2 _ hq'P q hq p hpP hq'q hqp
  have hpH : p ∈ H := hH.1.2.2.1 _ hq'H p hpP hq'p
  let σn : S.Name := ⟨kpair.π₂ z, S.subname_hereditarilySymmetric τA hσd⟩
  have hσA : T.ofName σn ∈ T.ofName τA := by
    have h := (T.formula_truth symmetricDCMemberFormula ![σn, τA]).mpr (by
      show GenericMeets H (symmetricForcingFormula S.P S.R S.Γ S.F symmetricDCMemberFormula
        (standardTuple (fun i ↦ ((![σn, τA] : Fin 2 → S.Name) i).val)))
      rw [S.tuple_val_two]
      exact ⟨_, hq'H, hq'mem⟩)
    exact (eval_symmetricDCMemberFormula _).mp h
  have hserT : ∀ x ∈ T.ofName τA, ∃ y ∈ T.ofName τA, ⟨x, y⟩ₖ ∈ T.ofName τB := by
    have h := (T.formula_truth serialFormula ![τA, τB]).mpr (by
      show GenericMeets H (symmetricForcingFormula S.P S.R S.Γ S.F serialFormula
        (standardTuple (fun i ↦ ((![τA, τB] : Fin 2 → S.Name) i).val)))
      rw [S.tuple_val_two]
      exact ⟨p, hpH, hser⟩)
    exact (eval_serialFormula _).mp h
  obtain ⟨y, hyA, hxy⟩ := hserT _ hσA
  obtain ⟨ν0, s, _, hνs, rfl⟩ := (T.mem_ofName_iff τA y).mp hyA
  let ν : S.Name := ⟨ν0.val, ν0.property⟩
  have hνd : ν.val ∈ domain τA.val := mem_domain_of_kpair_mem hνs
  have hnext : dependentChoiceNextFormula.Evalb (fun i ↦ T.ofName (![σn, ν, τA, τB] i)) :=
    (eval_dependentChoiceNextFormula _).mpr ⟨hyA, hxy⟩
  obtain ⟨r₁, hr₁H, hr₁0⟩ :=
    (T.formula_truth dependentChoiceNextFormula ![σn, ν, τA, τB]).mp hnext
  have hr₁ : r₁ ∈ symmetricForcingFormula S.P S.R S.Γ S.F dependentChoiceNextFormula
      (standardTuple (fun i ↦ ((![σn, ν, τA, τB] : Fin 4 → S.Name) i).val)) := hr₁0
  rw [S.tuple_val_four] at hr₁
  have hmemν : symmetricDCMemberFormula.Evalb (fun i ↦ T.ofName (![ν, τA] i)) := (eval_symmetricDCMemberFormula _).mpr hyA
  obtain ⟨r₂, hr₂H, hr₂0⟩ := (T.formula_truth symmetricDCMemberFormula ![ν, τA]).mp hmemν
  have hr₂ : r₂ ∈ symmetricForcingFormula S.P S.R S.Γ S.F symmetricDCMemberFormula
      (standardTuple (fun i ↦ ((![ν, τA] : Fin 2 → S.Name) i).val)) := hr₂0
  rw [S.tuple_val_two] at hr₂
  obtain ⟨r₃, hr₃H, hr₃r₁, hr₃r₂⟩ := hH.1.2.2.2 r₁ hr₁H r₂ hr₂H
  obtain ⟨r, hrH, hrr₃, hrq'⟩ := hH.1.2.2.2 r₃ hr₃H _ hq'H
  have hrP : r ∈ S.P := hH.1.1 r hrH
  have hr₃P : r₃ ∈ S.P := hH.1.1 r₃ hr₃H
  have hrr₁ : ⟨r, r₁⟩ₖ ∈ S.R := S.order.2.2 r hrP r₃ hr₃P r₁ (hH.1.1 r₁ hr₁H) hrr₃ hr₃r₁
  have hrr₂ : ⟨r, r₂⟩ₖ ∈ S.R := S.order.2.2 r hrP r₃ hr₃P r₂ (hH.1.1 r₂ hr₂H) hrr₃ hr₃r₂
  have hrq : ⟨r, q⟩ₖ ∈ S.R := S.order.2.2 r hrP _ hq'P q hq hrq' hq'q
  have hw : ⟨r, ν.val⟩ₖ ∈ S.chainCandidates τA.val q :=
    (S.pair_mem_chainCandidates _ _ _ _).mpr ⟨hrP, hνd, hrq,
      (symmetricForcingFormula_regular S.order _ _ _ _).2.1 r₂ hr₂ r hrP hrr₂⟩
  refine ⟨⟨r, ν.val⟩ₖ, hw, (S.pair_mem_chainRelation _ _ _ _ _).mpr ⟨hz, hw, ?_, ?_⟩⟩
  · simpa only [kpair.π₁_kpair] using hrq'
  · simpa only [kpair.π₂_kpair, kpair.π₁_kpair] using
      (symmetricForcingFormula_regular S.order _ _ _ _).2.1 r₁ hr₁ r hrP hrr₁

end SymmetricContext
end ZFVP
