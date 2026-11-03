import Blotto.GeneralPaperStoredDictionaryRows
import Blotto.GeneralPaperSourceRowsSharpContract

/-! Actual retained full source rows feed native quantization and unit
normalization once. Physical columns equal the unchanged defender's exact
source dictionary; unit-row extraction reads those retained arrays. These
are local preparation joins, not a completed modified-compiler driver. -/
namespace Blotto.GeneralPaperNativeUnitSourceJoin
open GeneralPaperSourceWordGrowth GeneralPaperInitializerPreparedPoint
set_option autoImplicit false
set_option maxHeartbeats 3200000

def run {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (budget : ℚ) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) :
    FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)×ℕ :=
  let quantized := GeneralPaperNativeDivisibleColumns.run price index A hT hK hDiv rows
  let normalized := GeneralPaperNativeDictionaryNormalize.run price index A budget quantized.1
  (normalized.1,quantized.2+normalized.2+64*A)

theorem data {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (budget : ℚ) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) :
    GeneralPaperRowQuantizer.dictionary (run price index A hT hK hDiv budget rows).1=
      GeneralPaperDictionary.normalize (GeneralPaperRowQuantizer.buildDivisible hT hK hDiv rows) budget := by
  dsimp only [run]
  rw [GeneralPaperNativeDictionaryNormalize.data,GeneralPaperNativeDivisibleColumns.data]

theorem dictionary_models {T m K : ℕ} (price price' index index' : ℕ → ℕ) (A A' : ℕ)
    (hT : 0<T) (hK : 0<K) (hDiv : K∣T) (budget : ℚ) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) :
    GeneralPaperRowQuantizer.dictionary (run price index A hT hK hDiv budget rows).1=
      GeneralPaperRowQuantizer.dictionary (run price' index' A' hT hK hDiv budget rows).1 := by rw [data,data]

theorem quantized_height {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (H : ℕ)
    (h : ∀ i j,RationalHeight ((rows.read i).read j) H) (j : Fin m) (l : Fin K) :
    RationalHeight (((GeneralPaperNativeDivisibleColumns.run price index A hT hK hDiv rows).1.read j).anchors.read l) H := by
  change RationalHeight ((GeneralPaperRowQuantizer.dictionary
    (GeneralPaperNativeDivisibleColumns.run price index A hT hK hDiv rows).1).anchor j l) H
  rw [GeneralPaperNativeDivisibleColumns.data]
  exact GeneralPaperQuantizedHeight.divisible_height hT hK hDiv rows H h j l

theorem height {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (budget : ℚ) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (C H : ℕ) (hc : RationalHeight budget C)
    (h : ∀ i j,RationalHeight ((rows.read i).read j) H) (j : Fin m) (l : Fin K) :
    RationalHeight (((run price index A hT hK hDiv budget rows).1.read j).anchors.read l) (C+H) :=
  GeneralPaperNativeDictionaryNormalize.height price index A budget _ C H hc
    (quantized_height price index A hT hK hDiv rows H h) j l

def profile (price : ℕ → ℕ) (A C H T m K B : ℕ) : ℕ :=
  512*(binaryWordWidth ((T+1)*K)+1)*(A+price (GeneralPaperNativeBlockLabel.width ((T+1)*K) K))+
    m*(GeneralPaperNativeQuantizedMatrix.fieldProfile K B A (price (1+2*H))
      (price (GeneralPaperNativeBlockLabel.width (K*B) B)) (price (1+binaryWordWidth (K*B+B+1)))+64*A)+44*(m+1)*A+64*A+
    (m*(K*(2*price (1+2*(C+H))+64*A)+44*(K+1)*A+96*A)+44*(m+1)*A+2*price (1+2*C)+32*A)+64*A

theorem work {T m K : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A C H : ℕ) (hA : 1≤A)
    (hT : 0<T) (hK : 0<K) (hDiv : K∣T) (budget : ℚ) (hc : RationalHeight budget C)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (h : ∀ i j,RationalHeight ((rows.read i).read j) H)
    (hIndex : ∀ i≤2*T+K+m,index (binaryWordWidth (i+1))≤A) :
    (run price index A hT hK hDiv budget rows).2≤
      profile price A C H T m K (GeneralPaperNativeDivisibleColumns.blocks price A T K hK).1.val := by
  have hq := GeneralPaperNativeDivisibleColumns.work price index hMono A (1+2*H) hA hT hK hDiv rows
    (fun i j => rationalWordWidth_of_height (h i j)) hIndex
  have hn := GeneralPaperNativeDictionaryNormalize.work price index hMono A C H hA budget
    (GeneralPaperNativeDivisibleColumns.run price index A hT hK hDiv rows).1 hc
    (quantized_height price index A hT hK hDiv rows H h) (fun i hi => hIndex i (by omega))
  unfold run profile
  dsimp only at hq ⊢
  omega

theorem source_rows {bits : Bool} (model : RationalCostModel) (W : ℕ) (x : Input) :
    (GeneralPaperSourceRowsSharpContract.preparedRun bits model W x).1.1=
      GeneralPaperSourceInitializer.sourceRows x.k x.Qv x.weights (x.b:ℝ) x.reciprocal := by
  unfold GeneralPaperSourceRowsSharpContract.preparedRun
  dsimp only
  rw [GeneralPaperSourceRowsDriver.rational_data bits model W x.k x.Qv (GeneralPaperProxyParameters.prepare x.m x.k).qbar]
  rfl

theorem source_data {bits : Bool} (model : RationalCostModel) (W : ℕ) (x : Input) (price index : ℕ → ℕ) (A : ℕ) :
    GeneralPaperRowQuantizer.dictionary (run price index A
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet x).lambda x.k)
      (GeneralPaperScoreScaleParameters.labels_positive x.m x.k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows x.m (alphabet x).lambda x.k)
      (ownBudget x.m x.k (x.b:ℝ) x.reciprocal)
      (GeneralPaperSourceRowsSharpContract.preparedRun bits model W x).1.1).1=
        GeneralPaperSourceUnchangedDictionary.run x.k x.Qv x.weights (x.b:ℝ) x.reciprocal := by
  rw [data,source_rows]
  rfl

theorem source_unit {bits : Bool} (model : RationalCostModel) (W : ℕ) (x : Input) (price index : ℕ → ℕ) (A : ℕ)
    (hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j) :
    GeneralPaperTransferPreparation.UnitDictionary (GeneralPaperRowQuantizer.dictionary (run price index A
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet x).lambda x.k)
      (GeneralPaperScoreScaleParameters.labels_positive x.m x.k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows x.m (alphabet x).lambda x.k)
      (ownBudget x.m x.k (x.b:ℝ) x.reciprocal)
      (GeneralPaperSourceRowsSharpContract.preparedRun bits model W x).1.1).1)
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet x).lambda x.k)
      (GeneralPaperScoreScaleParameters.labels_positive x.m x.k) := by
  rw [source_data]
  exact GeneralPaperSourceUnchangedDictionary.unit x.k x.Qv hm hQv x.weights hp x.weight_sum (x.b:ℝ)
    (by exact_mod_cast x.hb) x.reciprocal

end Blotto.GeneralPaperNativeUnitSourceJoin
