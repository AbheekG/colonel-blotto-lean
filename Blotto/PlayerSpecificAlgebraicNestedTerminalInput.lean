import Blotto.PlayerSpecificAlgebraicFourReflectedPath

/-! Native terminal nested inputs use exact fractional/zero tests on
the reached resource rows and compute the remaining mixture quotient. -/
namespace Blotto.PlayerSpecificAlgebraicNestedTerminalInput
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Input where
  budget : Data
  long : FixedArrayTable 3 Data
  short : FixedArrayTable 3 Data
  capacity : FixedArrayTable 3 Data
  resource : FixedArrayTable 3 Data

structure Values (a : Input) (i : TerminalResources) (x : ℝ) : Prop where
  budget : realEvaluate a.budget x=i.M
  long : ∀ j,realEvaluate (a.long.read j) x=i.long j
  short : ∀ j,realEvaluate (a.short.read j) x=i.short j
  capacity : ∀ j,realEvaluate (a.capacity.read j) x=i.capacity j
  resource : ∀ j,realEvaluate (a.resource.read j) x=i.resource j

def focus (model : RationalCostModel) (root : Candidate) (a : Input) : Fin 3 :=
  if PlayerSpecificAlgebraicActive.run model root (a.capacity.read 0) (a.resource.read 0) then 0
  else if PlayerSpecificAlgebraicActive.run model root (a.capacity.read 1) (a.resource.read 1) then 1 else 2

def endpoint (root : Candidate) (a : Input) (j : Fin 3) : Data :=
  if PlayerSpecificAlgebraicField.equal root.polynomial (a.resource.read j) [] then a.long.read j else a.short.read j

structure Prepared where
  input : PlayerSpecificAlgebraicNestedInput.Input
  permutation : Equiv.Perm (Fin 3)

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) : Prepared :=
  let f := focus model root a
  let p := Equiv.swap f 2
  ⟨⟨a.budget,endpoint root a (p 0),endpoint root a (p 1),a.long.read f,a.short.read f,
    PlayerSpecificAlgebraicField.divide root.polynomial (a.resource.read f) (a.capacity.read f)⟩,p⟩

theorem focus_value (model : RationalCostModel) (root : Candidate) (a : Input) (i : TerminalResources)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (ha : Values a i x) :
    focus model root a=i.focus := by
  have hc : ∀ j,PlayerSpecificAlgebraicActive.run model root (a.capacity.read j) (a.resource.read j)=true ↔
      Fractional i.capacity i.resource j := by
    intro j
    rw [PlayerSpecificAlgebraicActive.correct model root _ _ hm hirr hv x hx,ha.resource j,ha.capacity j]
    rfl
  unfold focus TerminalResources.focus
  by_cases h0 : Fractional i.capacity i.resource 0
  · rw [ite_eq_left ((hc 0).mpr h0),ite_eq_left h0]
  · rw [ite_eq_right (fun h => h0 ((hc 0).mp h)),ite_eq_right h0]
    by_cases h1 : Fractional i.capacity i.resource 1
    · rw [ite_eq_left ((hc 1).mpr h1),ite_eq_left h1]
    · rw [ite_eq_right (fun h => h1 ((hc 1).mp h)),ite_eq_right h1]

theorem endpoint_value (root : Candidate) (a : Input) (i : TerminalResources)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial)) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) (ha : Values a i x) (j : Fin 3) :
    realEvaluate (endpoint root a j) x=i.endpoint j := by
  have hz : realEvaluate [] x=0 := rfl
  have hc : PlayerSpecificAlgebraicField.equal root.polynomial (a.resource.read j) []=true ↔ i.resource j=0 := by
    rw [PlayerSpecificAlgebraicField.equal_value _ _ _ hm hirr x hx,ha.resource j,hz]
  by_cases h0 : i.resource j=0
  · rw [endpoint,ite_eq_left (hc.mpr h0),ha.long j,TerminalResources.endpoint,ite_eq_left h0]
  · rw [endpoint,ite_eq_right (fun h => h0 (hc.mp h)),ha.short j,TerminalResources.endpoint,ite_eq_right h0]

theorem values (model : RationalCostModel) (root : Candidate) (a : Input) (i : TerminalResources)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (ha : Values a i x)
    (hcap : ∀ j,Reduced root.polynomial (a.capacity.read j)) :
    PlayerSpecificAlgebraicNestedSpecInput.Values (prepare model root a).input i.input x ∧
      (prepare model root a).permutation=i.permutation := by
  have hf := focus_value model root a i hm hirr hv x hx ha
  constructor
  · constructor
    · exact ha.budget
    · change realEvaluate (endpoint root a ((Equiv.swap (focus model root a) 2) 0)) x=i.endpoint (i.permutation 0)
      rw [hf]
      exact endpoint_value root a i hm hirr x hx.1 ha _
    · change realEvaluate (endpoint root a ((Equiv.swap (focus model root a) 2) 1)) x=i.endpoint (i.permutation 1)
      rw [hf]
      exact endpoint_value root a i hm hirr x hx.1 ha _
    · change realEvaluate (a.long.read (focus model root a)) x=i.long i.focus
      rw [hf,ha.long]
    · change realEvaluate (a.short.read (focus model root a)) x=i.short i.focus
      rw [hf,ha.short]
    · change realEvaluate (PlayerSpecificAlgebraicField.divide root.polynomial
        (a.resource.read (focus model root a)) (a.capacity.read (focus model root a))) x=i.weight i.focus
      rw [PlayerSpecificAlgebraicField.divide_value _ _ _ hm hirr (hcap _) x hx.1,hf,ha.resource,ha.capacity]
      rfl
  · change Equiv.swap (focus model root a) 2=Equiv.swap i.focus 2
    rw [hf]

end Blotto.PlayerSpecificAlgebraicNestedTerminalInput
