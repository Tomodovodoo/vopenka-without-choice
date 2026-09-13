import PalomarBridge.Vocabulary

/-! Explicit forcing and symmetric-extension data for Theorem A.
A standalone Challenge copies this file after the shared membership vocabulary.
All recursion graphs and all dense sets below are internal to the ground model. -/

namespace PalomarPreservationBridge
open PalomarBridge PalomarBridge.Coding
variable {M : Type u} (mem : M → M → Prop) [Nonempty M]

def Subset (A B : M) : Prop := ∀ x, mem x A → mem x B
noncomputable def intersection (A B : M) : M := setValue mem (fun x => mem x A ∧ mem x B)
noncomputable def identity (A : M) : M := setValue mem (fun p => ∃ x, mem x A ∧ p = pair mem x x)
noncomputable def inverse (f : M) : M := setValue mem (fun p =>
  ∃ x y, mem (pair mem x y) f ∧ p = pair mem y x)
def InjectiveGraph (f : M) : Prop :=
  ∀ x y z, mem (pair mem x z) f → mem (pair mem y z) f → x = y
/-- q ≤ p means that q is a stronger forcing condition. -/
def Stronger (R q p : M) : Prop := mem (pair mem q p) R
def Preorder (P R : M) : Prop :=
  (∀ p, mem p R → ∃ x, mem x P ∧ ∃ y, mem y P ∧ p = pair mem x y) ∧
  (∀ p, mem p P → Stronger mem R p p) ∧
  ∀ p, mem p P → ∀ q, mem q P → ∀ r, mem r P →
    Stronger mem R p q → Stronger mem R q r → Stronger mem R p r
def Poset (P R : M) : Prop := Preorder mem P R ∧
  ∀ p, mem p P → ∀ q, mem q P → Stronger mem R p q → Stronger mem R q p → p = q
def Top (P R one : M) : Prop := mem one P ∧ ∀ p, mem p P → Stronger mem R p one
def Automorphism (P R f : M) : Prop :=
  mem f (functions mem P P) ∧ InjectiveGraph mem f ∧ range mem f = P ∧
  ∀ p, mem p P → ∀ q, mem q P →
    (Stronger mem R p q ↔ Stronger mem R (value mem f p) (value mem f q))
def AutomorphismGroup (P R group : M) : Prop :=
  (∀ f, mem f group → Automorphism mem P R f) ∧ mem (identity mem P) group ∧
  (∀ f, mem f group → ∀ g, mem g group → mem (compose mem f g) group) ∧
  ∀ f, mem f group → mem (inverse mem f) group
def Subgroup (P group H : M) : Prop := Subset mem H group ∧ mem (identity mem P) H ∧
  (∀ f, mem f H → ∀ g, mem g H → mem (compose mem f g) H) ∧
  ∀ f, mem f H → mem (inverse mem f) H
noncomputable def conjugate (f H : M) : M := setValue mem (fun g =>
  ∃ h, mem h H ∧ g = compose mem (compose mem (inverse mem f) h) f)
def NormalFilter (P group filter : M) : Prop :=
  (∀ H, mem H filter → Subgroup mem P group H) ∧ mem group filter ∧
  (∀ H, mem H filter → ∀ K, Subgroup mem P group K → Subset mem H K → mem K filter) ∧
  (∀ H, mem H filter → ∀ K, mem K filter → mem (intersection mem H K) filter) ∧
  ∀ f, mem f group → ∀ H, mem H filter → mem (conjugate mem f H) filter
/-- An external generic meets every dense subset coded by a ground-model set. -/
def Generic (P R : M) (G : Set M) : Prop :=
  ((∀ p ∈ G, mem p P) ∧ G.Nonempty ∧
    (∀ p ∈ G, ∀ q, mem q P → Stronger mem R p q → q ∈ G) ∧
    ∀ p ∈ G, ∀ q ∈ G, ∃ r ∈ G, Stronger mem R r p ∧ Stronger mem R r q) ∧
  ∀ D, Subset mem D P → (∀ p, mem p P → ∃ q, mem q D ∧ Stronger mem R q p) →
    ∃ p ∈ G, mem p D

/-- Closure under taking the names appearing as first components. -/
def SubnameClosed (C : M) : Prop := ∀ t, mem t C → Subset mem (domain mem t) C
noncomputable def nameClosure (t : M) : M :=
  setValue mem (fun s => ∀ C, SubnameClosed mem C → mem t C → mem s C)
def Name (P t : M) : Prop := ∀ s, mem s (nameClosure mem t) →
  ∀ z, mem z s → ∃ t, ∃ p, mem p P ∧ z = pair mem t p
/-- A complete internal recursion graph on a subname-closed set. -/
def Recursion (C : M) (step : M → M → M) (f : M) : Prop :=
  IsFunction mem f ∧ domain mem f = C ∧
  ∀ t, mem t C → value mem f t = step t (restrict mem f (domain mem t))
noncomputable def recursion (step : M → M → M) (t : M) : M :=
  value mem (Classical.epsilon (Recursion mem (nameClosure mem t) step)) t
noncomputable def actionStep (f t g : M) : M := setValue mem (fun z =>
  ∃ w, mem w t ∧ z = pair mem (value mem g (first mem w)) (value mem f (second mem w)))
noncomputable def action (f t : M) : M := recursion mem (actionStep mem f) t
noncomputable def stabilizer (group t : M) : M :=
  setValue mem (fun f => mem f group ∧ action mem f t = t)
/-- Every name in the full internal subname closure has a stabilizer in the filter. -/
def HereditarilySymmetric (P group filter t : M) : Prop :=
  Name mem P t ∧ ∀ s, mem s (nameClosure mem t) → mem (stabilizer mem group s) filter

/-- The standard two density clauses defining forcing of equality. -/
def EqualityTest (P R : M) (E : M → M → M) (s t p : M) : Prop :=
  (∀ v a, mem (pair mem v a) s → ∀ q, mem q P →
    Stronger mem R q p → Stronger mem R q a →
    ∃ r, mem r P ∧ Stronger mem R r q ∧
      ∃ w b, mem (pair mem w b) t ∧ Stronger mem R r b ∧ mem r (E v w)) ∧
  (∀ w b, mem (pair mem w b) t → ∀ q, mem q P →
    Stronger mem R q p → Stronger mem R q b →
    ∃ r, mem r P ∧ Stronger mem R r q ∧
      ∃ v a, mem (pair mem v a) s ∧ Stronger mem R r a ∧ mem r (E v w))
noncomputable def equalityConditions (P R s t f : M) : M := setValue mem
  (fun p => mem p P ∧ EqualityTest mem P R (fun v w => value mem (value mem f v) w) s t p)
noncomputable def equalityRowStep (P R C s f : M) : M := setValue mem
  (fun z => ∃ t, mem t C ∧ z = pair mem t (equalityConditions mem P R s t f))
/-- Equality is computed by internal subname recursion, with a fixed set of
right-hand names. This works in externally ill-founded ground models. -/
noncomputable def equality (P R s t : M) : M :=
  value mem (recursion mem (equalityRowStep mem P R (nameClosure mem t)) s) t
noncomputable def membership (P R s t : M) : M := setValue mem (fun p =>
  mem p P ∧ ∀ q, mem q P → Stronger mem R q p →
    ∃ r, mem r P ∧ Stronger mem R r q ∧
      ∃ v a, mem (pair mem v a) t ∧ Stronger mem R r a ∧ mem r (equality mem P R s v))

/-- A poset with top, automorphism group, normal filter, and supplied generic. -/
structure SymmetricData where
  P : M
  R : M
  one : M
  group : M
  filter : M
  G : Set M
  poset : Poset mem P R
  top : Top mem P R one
  automorphisms : AutomorphismGroup mem P R group
  normal : NormalFilter mem P group filter
  generic : Generic mem P R G

/-- A presentation of the symmetric extension as precisely the quotient of
hereditarily symmetric names by generic-forced equality, with the membership
relation obtained from generic-forced membership. Surjectivity excludes extra
objects; both equivalences specify the quotient completely. -/
def Presentation (d : SymmetricData mem) (W : Type u) (wmem : W → W → Prop) : Prop :=
  ∃ val : {t : M // HereditarilySymmetric mem d.P d.group d.filter t} → W,
    Function.Surjective val ∧ ∀ s t,
      (val s = val t ↔ ∃ p ∈ d.G, mem p (equality mem d.P d.R s.val t.val)) ∧
      (wmem (val s) (val t) ↔ ∃ p ∈ d.G, mem p (membership mem d.P d.R s.val t.val))

/-- A membership structure satisfying ZF and the full VP scheme. Nonemptiness
is part of the conclusion, rather than an extra condition on a presentation. -/
def IsZFVPModel {W : Type u} (wmem : W → W → Prop) : Prop :=
  ∃ hne : Nonempty W, IsZF wmem ∧ @Coding.Vopenka W wmem hne

end PalomarPreservationBridge


