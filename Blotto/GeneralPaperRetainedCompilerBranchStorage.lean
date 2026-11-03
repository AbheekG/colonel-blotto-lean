import Blotto.GeneralPaperSourceColumnCallerReachedRates

/-! Literal retained compiler branch parent. Full physical columns and
stored values, reached result tag/point, two constant-count primitive
scratch prices and native parent fields coexist. Strict-preparation and
endpoint child owners remain in the preceding additive contracts. The
returned label closure borrows exactly the original physical columns. -/
namespace Blotto.GeneralPaperRetainedCompilerBranchStorage
open GeneralPaperEncodedScalarStorage GeneralPaperSourceEndpointBranch
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384

def choiceFoot {d : ℕ} (W : ℕ) : Choice d → ℕ
  | .zero => 1
  | .endpoint gamma point => 1+rationalWordWidth gamma+GeneralPaperEncodedBasisStorage.arrayFootprint W rationalWordWidth point+32*W
def resultFoot {T m K : ℕ} (W : ℕ) : Option (Result T m K) → ℕ
  | none => 1
  | some r => 1+choiceFoot W r.choice+32*W

def child {T m K S : ℕ} (model : RationalCostModel) (W H p q : ℕ) (reciprocal : Bool)
    (endpoint : Farey.Fraction) (value : ℚ) (retained : GeneralPaperRetainedTransferPreparation.Output T m K S×ℕ) :=
  if retained.1.prepared.threshold=retained.1.maximum then (none,0) else
    GeneralPaperRetainedBasisEndpointBits.run model W H p q reciprocal retained.1.prepared retained.1.matrix endpoint value

def tag {d : ℕ} (model : RationalCostModel) (W : ℕ) (reciprocal : Bool) (value : ℚ)
    (point : Option (GeneralPaperBasisRationalSolve.RatVector d)) : ℕ :=
  if point.isSome then GeneralPaperRetainedCompilerBranchBits.tagPrice model W reciprocal value else 0

def price (W P X E G : ℕ) : ℕ := P+X+E+G+80*W
def metadataCap (W T m K depth S H N P X E G : ℕ) : ℕ :=
  T+m+K+depth+S+H+2*N+price W P X E G+1

def controls {T m K : ℕ} (model : RationalCostModel) (W depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) : List ℕ :=
  let retained := GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing
  let test := GeneralPaperRetainedCompilerBranchBits.thresholdPrice model W retained.1.prepared.threshold retained.1.maximum
  let reached := child model W H p q reciprocal endpoint value retained
  let g := tag model W reciprocal value reached.1
  let result := GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value
  [T,m,K,depth,S,H,p,q,retained.1.prepared.threshold,retained.1.maximum,retained.2,test,reached.2,g,result.2,
    retained.2+test,retained.2+test+reached.2,retained.2+test+reached.2+g,
    GeneralPaperFinalStaticLoopStorage.bit reciprocal,
    GeneralPaperFinalStaticLoopStorage.bit (decide (retained.1.prepared.threshold=retained.1.maximum)),
    GeneralPaperFinalStaticLoopStorage.bit reached.1.isSome,GeneralPaperFinalStaticLoopStorage.bit result.1.isSome]

def window {T m K : ℕ} (model : RationalCostModel) (W depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) : ℕ :=
  let retained := GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing
  let reached := child model W H p q reciprocal endpoint value retained
  let result := GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value
  GeneralPaperEnclosingSourceOwners.columnsFoot W columns+GeneralPaperEncodedRationalRows.rowFootprint W values.values+
    rationalWordWidth own+rationalWordWidth opposing+resultFoot W result.1+
    GeneralPaperRetainedCompilerBranchBits.thresholdPrice model W retained.1.prepared.threshold retained.1.maximum+
    tag model W reciprocal value reached.1+
    fields W (controls model W depth S H p q hK columns values own opposing reciprocal endpoint value)+160*W

def profile (W T m K depth S H N R V Point Gamma P X E G : ℕ) : ℕ :=
  GeneralPaperEnclosingSourceOwners.columnsProfile W T m K R+GeneralPaperEncodedRationalRows.rowProfile W m V+
    2*R+Point+Gamma+64*W+2+X+G+
    22*(natBits (metadataCap W T m K depth S H N P X E G)+W)+192*W

theorem tag_bound {d : ℕ} (model : RationalCostModel) (W : ℕ) (reciprocal : Bool) (value : ℚ)
    (point : Option (GeneralPaperBasisRationalSolve.RatVector d)) :
    tag model W reciprocal value point≤GeneralPaperRetainedCompilerBranchBits.tagPrice model W reciprocal value := by
  unfold tag
  split <;> omega

theorem result_bound {T m K : ℕ} (model : RationalCostModel) (W depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) :
    let retained := GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing
    resultFoot W (GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value).1≤
      GeneralPaperRawEndpointReturnStorage.optionFoot W (child model W H p q reciprocal endpoint value retained).1+
        rationalWordWidth (if reciprocal then 1/value else value)+64*W+2 := by
  dsimp only
  unfold GeneralPaperRetainedCompilerBranchBits.run child
  dsimp only
  split
  · simp only [resultFoot,choiceFoot,GeneralPaperRawEndpointReturnStorage.optionFoot]
    omega
  · cases (GeneralPaperRetainedBasisEndpointBits.run model W H p q reciprocal
      (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.prepared
      (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.matrix endpoint value).1 <;>
      simp only [Option.map_none,Option.map_some,resultFoot,choiceFoot,GeneralPaperRawEndpointReturnStorage.optionFoot] <;> omega

theorem work_shape {T m K : ℕ} (model : RationalCostModel) (W depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) :
    let retained := GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing
    let reached := child model W H p q reciprocal endpoint value retained
    let test := GeneralPaperRetainedCompilerBranchBits.thresholdPrice model W retained.1.prepared.threshold retained.1.maximum
    (GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value).2≤
      retained.2+test+reached.2+tag model W reciprocal value reached.1+80*W := by
  dsimp only
  unfold GeneralPaperRetainedCompilerBranchBits.run child
  dsimp only
  split
  · simp only [tag,Option.isSome_none,Bool.false_eq_true,ite_false]
    omega
  · simp only [tag]
    omega

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W depth S H p q N R V Point Gamma P X E G : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ)
    (hColumns : GeneralPaperEnclosingSourceOwners.columnsFoot W columns≤GeneralPaperEnclosingSourceOwners.columnsProfile W T m K R)
    (hValues : ∀ j,RationalHeight (values.values.read j) V)
    (hOwn : rationalWordWidth own≤R) (hOpposing : rationalWordWidth opposing≤R) (hp : p≤N) (hq : q≤N)
    (hThreshold : (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.prepared.threshold≤S)
    (hMaximum : (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.maximum≤S)
    (hP : (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).2≤P)
    (hX : GeneralPaperRetainedCompilerBranchBits.thresholdPrice model W
      (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.prepared.threshold
      (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.maximum≤X)
    (hE : (child model W H p q reciprocal endpoint value
      (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing)).2≤E)
    (hG : GeneralPaperRetainedCompilerBranchBits.tagPrice model W reciprocal value≤G)
    (hPoint : GeneralPaperRawEndpointReturnStorage.optionFoot W (child model W H p q reciprocal endpoint value
      (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing)).1≤Point)
    (hGamma : rationalWordWidth (if reciprocal then 1/value else value)≤Gamma) :
    window model W depth S H p q hK columns values own opposing reciprocal endpoint value≤
      profile W T m K depth S H N R V Point Gamma P X E G ∧
    (GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value).2≤price W P X E G := by
  let retained := GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing
  let test := GeneralPaperRetainedCompilerBranchBits.thresholdPrice model W retained.1.prepared.threshold retained.1.maximum
  let reached := child model W H p q reciprocal endpoint value retained
  let g := tag model W reciprocal value reached.1
  let result := GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values own opposing reciprocal endpoint value
  have hV := GeneralPaperEncodedRationalRows.row_bound W V values.values hValues
  have hResult := (result_bound model W depth S H p q hK columns values own opposing reciprocal endpoint value).trans
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hPoint hGamma) _) _)
  change resultFoot W result.1≤Point+Gamma+64*W+2 at hResult
  have hTag := (tag_bound model W reciprocal value reached.1).trans hG
  change g≤G at hTag
  change retained.2≤P at hP
  change test≤X at hX
  change reached.2≤E at hE
  change retained.1.prepared.threshold≤S at hThreshold
  change retained.1.maximum≤S at hMaximum
  have hShape := work_shape model W depth S H p q hK columns values own opposing reciprocal endpoint value
  change result.2≤retained.2+test+reached.2+g+80*W at hShape
  have hWork : result.2≤price W P X E G := by unfold price;omega
  have hR := GeneralPaperFinalStaticLoopStorage.bit_bound reciprocal
  have hT := GeneralPaperFinalStaticLoopStorage.bit_bound (decide (retained.1.prepared.threshold=retained.1.maximum))
  have hC := GeneralPaperFinalStaticLoopStorage.bit_bound reached.1.isSome
  have hB := GeneralPaperFinalStaticLoopStorage.bit_bound result.1.isSome
  have hf := fields_bound W (natBits (metadataCap W T m K depth S H N P X E G))
    (controls model W depth S H p q hK columns values own opposing reciprocal endpoint value) (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      change z∈[T,m,K,depth,S,H,p,q,retained.1.prepared.threshold,retained.1.maximum,retained.2,test,reached.2,g,result.2,
        retained.2+test,retained.2+test+reached.2,retained.2+test+reached.2+g,
        GeneralPaperFinalStaticLoopStorage.bit reciprocal,
        GeneralPaperFinalStaticLoopStorage.bit (decide (retained.1.prepared.threshold=retained.1.maximum)),
        GeneralPaperFinalStaticLoopStorage.bit reached.1.isSome,GeneralPaperFinalStaticLoopStorage.bit result.1.isSome] at hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap price;omega)
  change fields W _≤22*(natBits (metadataCap W T m K depth S H N P X E G)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  unfold window profile
  change GeneralPaperEnclosingSourceOwners.columnsFoot W columns+GeneralPaperEncodedRationalRows.rowFootprint W values.values+
    rationalWordWidth own+rationalWordWidth opposing+resultFoot W result.1+test+g+
    fields W (controls model W depth S H p q hK columns values own opposing reciprocal endpoint value)+160*W≤_
  omega

end Blotto.GeneralPaperRetainedCompilerBranchStorage
