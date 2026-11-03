import Blotto.GeneralPaperSourceOuterEndpointStorageReachedRates

/-! Actual retained endpoint-fraction constructor. Complete classifier and
returned raw fraction owners coexist with Q/one, reached addition scratch
and every native primitive/partial/branch/return field. No root, quotient,
classification or rational numerator/denominator query is repeated. -/
namespace Blotto.GeneralPaperEndpointFractionConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def richBranch (c : GeneralPaperProxyClassifier.Result) : Bool :=
  if c.choice.modify=none then false else
    match c.root with
    | some _ => false
    | none => decide (c.choice.modify=some .rich)
def addition (model : RationalCostModel) (c : GeneralPaperProxyClassifier.Result) : ℕ :=
  if richBranch c then GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) c.cell 1 else 0
def metadataCap (model : RationalCostModel) (W R : ℕ) : ℕ := 64*W+2*model.rat R+1
def controls (model : RationalCostModel) (W Q : ℕ) (hQ : 0<Q) (c : GeneralPaperProxyClassifier.Result) : List ℕ :=
  let result := GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ c
  [64*W,result.2,GeneralPaperFinalStaticLoopStorage.bit (decide (c.choice.modify=none)),
    GeneralPaperFinalStaticLoopStorage.bit c.root.isSome,GeneralPaperFinalStaticLoopStorage.bit (decide (c.choice.modify=some .rich))]++
    if richBranch c then
      let a := model.rat (max (GeneralPaperNaturalPrimitivePrice.word c.cell) (GeneralPaperNaturalPrimitivePrice.word 1))
      let b := model.rat (GeneralPaperNaturalPrimitivePrice.word (c.cell+1))
      [a,b,a+b,64*W+a,64*W+a+b]
    else []
def window (model : RationalCostModel) (W Q : ℕ) (hQ : 0<Q) (c : GeneralPaperProxyClassifier.Result) : ℕ :=
  GeneralPaperClassifierResultStorage.footprint W c+natBits Q+natBits 1+
    GeneralPaperSelectionStorage.fraction W (GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ c).1+
    addition model c+fields W (controls model W Q hQ c)+160*W
def profile (model : RationalCostModel) (W R Classifier : ℕ) : ℕ :=
  Classifier+4*R+2*model.rat R+10*(natBits (metadataCap model W R)+W)+320*W

theorem run_work (model : RationalCostModel) (W Q : ℕ) (hQ : 0<Q) (c : GeneralPaperProxyClassifier.Result) :
    (GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ c).2=64*W+addition model c := by
  unfold GeneralPaperRetainedEndpointFraction.run addition richBranch
  split
  · rfl
  · cases c.root with
    | some f => rfl
    | none => dsimp only; split <;> simp_all

theorem addition_bound (model : RationalCostModel) (B R : ℕ) (c : GeneralPaperProxyClassifier.Result)
    (hCell : c.cell+1≤B) (hR : natBits B≤R) : addition model c≤2*model.rat R := by
  have h := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b) c.cell 1 B
    (by omega) (by omega) hCell
  have hw := model.monotone hR
  unfold addition
  split
  · exact h.trans (Nat.mul_le_mul_left 2 hw)
  · omega

theorem result_caps (primitive : ℕ → ℕ) (W Q B : ℕ) (hQ : 0<Q) (c : GeneralPaperProxyClassifier.Result)
    (hCell : c.cell+1≤B) (hGrid : Q≤B)
    (hRoot : ∀ f,c.root=some f → f.num≤B ∧ f.den≤B) :
    let result := (GeneralPaperRetainedEndpointFraction.run primitive W Q hQ c).1
    result.num≤B ∧ result.den≤B := by
  unfold GeneralPaperRetainedEndpointFraction.run
  split
  · dsimp only; omega
  · cases hr : c.root with
    | some f => exact hRoot f hr
    | none => dsimp only; split <;> dsimp only <;> omega

theorem controls_length (model : RationalCostModel) (W Q : ℕ) (hQ : 0<Q) (c : GeneralPaperProxyClassifier.Result) :
    (controls model W Q hQ c).length≤10 := by
  unfold controls
  dsimp only
  split <;> norm_num only [List.length_append,List.length_cons,List.length_nil]

theorem bounded (model : RationalCostModel) (W Q B R Classifier : ℕ) (hQ : 0<Q) (c : GeneralPaperProxyClassifier.Result)
    (hClassifier : GeneralPaperClassifierResultStorage.footprint W c≤Classifier)
    (hCell : c.cell+1≤B) (hGrid : Q≤B) (hRoot : ∀ f,c.root=some f → f.num≤B ∧ f.den≤B)
    (hR : natBits B≤R) : window model W Q hQ c≤profile model W R Classifier := by
  have nat_bound (x : ℕ) (hx : x≤B) : natBits x≤R :=
    (Nat.add_le_add_left (binaryWordWidth_mono hx) 1).trans hR
  have hCellW := nat_bound c.cell (by omega)
  have hOneW := nat_bound 1 (by omega)
  have hGridW := nat_bound Q hGrid
  have hNextW := nat_bound (c.cell+1) hCell
  have hResult := result_caps model.rat W Q B hQ c hCell hGrid hRoot
  have hFraction := GeneralPaperSelectionStorage.fraction_bound W R _ (nat_bound _ hResult.1) (nat_bound _ hResult.2)
  have hAdd := addition_bound model B R c hCell hR
  have hWork : (GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ c).2≤64*W+2*model.rat R := by
    rw [run_work]
    omega
  have hA := model.monotone (max_le hCellW hOneW)
  have hB := model.monotone hNextW
  change model.rat (max (GeneralPaperNaturalPrimitivePrice.word c.cell) (GeneralPaperNaturalPrimitivePrice.word 1))≤model.rat R at hA
  change model.rat (GeneralPaperNaturalPrimitivePrice.word (c.cell+1))≤model.rat R at hB
  have hMod := GeneralPaperFinalStaticLoopStorage.bit_bound (decide (c.choice.modify=none))
  have hRootBit := GeneralPaperFinalStaticLoopStorage.bit_bound c.root.isSome
  have hRich := GeneralPaperFinalStaticLoopStorage.bit_bound (decide (c.choice.modify=some .rich))
  have hf := fields_bound W (natBits (metadataCap model W R)) (controls model W Q hQ c) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    unfold controls at hz
    dsimp only at hz
    unfold metadataCap
    rcases List.mem_append.mp hz with hz|hz
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega
    · split at hz
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega
      · simp only [List.not_mem_nil] at hz)
  have hFields := hf.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (controls_length model W Q hQ c)) _)
  unfold window profile
  omega

end Blotto.GeneralPaperEndpointFractionConstructionStorage
