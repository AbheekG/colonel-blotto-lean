import Blotto.PlayerSpecificTerminalCoreSelectedSourceCost

/-! Full terminal-core source price includes the selected continuation,
all six possible source rows, four returned rows and branch metadata. -/
namespace Blotto.PlayerSpecificTerminalCoreDrawSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicTerminalCoreInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frameHeight (T K : ℕ) : ℕ :=
  max T (PlayerSpecificAlgebraicTerminalCoreDrawBounds.height T K)+6

def work (T H K : ℕ) : ℕ :=
  PlayerSpecificTerminalCoreSelectedSourceCost.work T H K+
  (2206*PlayerSpecificResourceCostProfile.rationalCoefficient)*(frameHeight T K+1)^3+2

theorem environment_bounds (root : Candidate) (a : Input) (T : ℕ)
    (hm0 : root.polynomial ≠ [])
    (ha : PlayerSpecificAlgebraicTerminalCoreFits.Fits root a T) :
    ∀ j,Reduced root.polynomial ((PlayerSpecificTerminalCoreDrawExecution.environment a).read j) ∧
      HasHeight ((PlayerSpecificTerminalCoreDrawExecution.environment a).read j) T := by
  intro j
  fin_cases j
  · simpa [PlayerSpecificTerminalCoreDrawExecution.environment,FixedArrayTable.read_ofFn] using ha.budget
  · simpa [PlayerSpecificTerminalCoreDrawExecution.environment,FixedArrayTable.read_ofFn] using ha.lengths 0
  · simpa [PlayerSpecificTerminalCoreDrawExecution.environment,FixedArrayTable.read_ofFn] using ha.lengths 1
  · simpa [PlayerSpecificTerminalCoreDrawExecution.environment,FixedArrayTable.read_ofFn] using ha.lengths 2
  · cases hf : a.fractional with
    | none =>
      simp [PlayerSpecificTerminalCoreDrawExecution.environment,FixedArrayTable.read_ofFn,
        hf,Option.map_none,Option.getD_none]
      exact ⟨nil_reduced _ hm0,nil_height _⟩
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      simpa [PlayerSpecificTerminalCoreDrawExecution.environment,FixedArrayTable.read_ofFn,
        hf,Option.map_some,Option.getD_some,Prod.fst] using
        (ha.fractional ell probability hf).1
  · cases hf : a.fractional with
    | none =>
      simp [PlayerSpecificTerminalCoreDrawExecution.environment,FixedArrayTable.read_ofFn,
        hf,Option.map_none,Option.getD_none]
      exact ⟨nil_reduced _ hm0,nil_height _⟩
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      simpa [PlayerSpecificTerminalCoreDrawExecution.environment,FixedArrayTable.read_ofFn,
        hf,Option.map_some,Option.getD_some,Prod.snd] using
        (ha.fractional ell probability hf).2

theorem cost (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input)
    (x : ℝ) (T H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : Valid a x) (hfit : PlayerSpecificAlgebraicTerminalCoreFits.Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T)
    (he : HasHeight [r.root.interval.lo,r.root.interval.hi] T) (hT : 2 ≤ T) :
    (PlayerSpecificTerminalCoreDrawExecution.run r a H K bits).2 ≤ work T H K := by
  let model := RationalCostModel.schoolbook
  let S := frameHeight T K
  let W := PlayerSpecificAlgebraicComparisonExecution.width S
  let drawn := PlayerSpecificTerminalCoreDrawExecution.selected r a H K bits
  let result := drawn.1
  let input := PlayerSpecificTerminalCoreDrawExecution.environment a
  have hm0 : r.root.polynomial ≠ [] := by
    intro hz
    exact hirr.ne_zero (by rw [hz]; rfl)
  have hd := PlayerSpecificTerminalCoreSelectedSourceCost.cost r a x T H K bits
    hm hirr hv hx ha hfit hml hmT he hT
  have hinput : ∀ j,Reduced r.root.polynomial (input.read j) ∧ HasHeight (input.read j) T :=
    environment_bounds r.root a T hm0 hfit
  have hresult : ∀ j,Reduced r.root.polynomial (result.read j) ∧
      HasHeight (result.read j) (PlayerSpecificAlgebraicTerminalCoreDrawBounds.height T K) := by
    intro j
    change Reduced r.root.polynomial ((PlayerSpecificTerminalCoreDrawExecution.run r a H K bits).1.read j) ∧
      HasHeight ((PlayerSpecificTerminalCoreDrawExecution.run r a H K bits).1.read j)
        (PlayerSpecificAlgebraicTerminalCoreDrawBounds.height T K)
    rw [PlayerSpecificTerminalCoreDrawExecution.value]
    exact PlayerSpecificAlgebraicTerminalCoreDrawBounds.bounds r a hm hirr hv x hx ha T hfit hml hmT hT H K bits j
  have hTS : T ≤ S := by dsimp [S,frameHeight]; omega
  have hYS : PlayerSpecificAlgebraicTerminalCoreDrawBounds.height T K ≤ S := by
    dsimp [S,frameHeight]; omega
  have hf := PlayerSpecificExpressionVectorFrameCost.cost model r.root input result S
    (mono hmT hTS) hml (mono he hTS)
    (fun j => ⟨mono (hinput j).2 hTS,by have h := (hinput j).1.2; omega⟩)
    (fun j => ⟨mono (hresult j).2 hYS,by have h := (hresult j).1.2; omega⟩)
    (by dsimp [S,frameHeight]; omega) (by dsimp [S,frameHeight]; omega)
    (by dsimp [S,frameHeight]; omega)
  have hf' : price model (PlayerSpecificExpressionVectorExecution.frame r.root input result) ≤
      (2200*PlayerSpecificResourceCostProfile.rationalCoefficient)*(S+1)^3 :=
    hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 2200 S)
  let flag := if a.fractional.isSome then 1 else 0
  have hwords : ∀ word ∈ [a.count,flag], binaryWordWidth word ≤ W := by
    intro word hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    have hsize : word ≤ S := by
      rcases hw with h|h
      · rw [h]
        rcases ha.count with hc|hc <;> dsimp [S,frameHeight] <;> omega
      · rw [h]
        dsimp [flag,S,frameHeight]
        split <;> omega
    exact (control_width word).trans
      ((Nat.add_le_add_right hsize 1).trans
        (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
  have hc := PlayerSpecificAlgebraicCallerFrame.controls_cost model [a.count,flag] W hwords
    (by have h := (PlayerSpecificAlgebraicActiveListCost.width_large S).1; omega)
  have hc' : price model [Event.control a.count,Event.control flag] ≤
      (6*PlayerSpecificResourceCostProfile.rationalCoefficient)*(S+1)^3 := by
    change price model ([a.count,flag].map Event.control) ≤ _
    simpa only [List.length_cons,List.length_nil] using
      hc.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 6 S)
  change drawn.2+price model (PlayerSpecificTerminalCoreDrawExecution.frame r.root a result)+
    price model [.control 1] ≤ _
  rw [PlayerSpecificTerminalCoreDrawExecution.frame,price_append,
    show price model [.control 1]=2 by rfl]
  have hsum := Nat.add_le_add_right (Nat.add_le_add hd (Nat.add_le_add hf' hc')) 2
  apply hsum.trans_eq
  dsimp only [S]
  unfold work
  ring

theorem same_return_and_cost (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input)
    (x : ℝ) (T H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : Valid a x) (hfit : PlayerSpecificAlgebraicTerminalCoreFits.Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T)
    (he : HasHeight [r.root.interval.lo,r.root.interval.hi] T) (hT : 2 ≤ T) :
    (PlayerSpecificTerminalCoreDrawExecution.run r a H K bits).1 =
      PlayerSpecificAlgebraicTerminalCoreDraw.draw r a H K bits ∧
    (PlayerSpecificTerminalCoreDrawExecution.run r a H K bits).2 ≤ work T H K :=
  ⟨PlayerSpecificTerminalCoreDrawExecution.value r a H K bits,
    cost r a x T H K bits hm hirr hv hx ha hfit hml hmT he hT⟩

end Blotto.PlayerSpecificTerminalCoreDrawSourceCost
