import Blotto.PaperPRGRecordCalibration
import Blotto.PaperPRGRealInput
import Blotto.FairBitProductLaw

/-! Paper-facing PRG contracts. Costs are for the declared rational/word
source model. The data procedures execute no cost or real-logarithm oracle.
Game and accuracy are separate inputs, preserving the appendix's L0/E split.
The finite laws are laws of whole returned rows, with independent player seeds.
-/
namespace Blotto.PaperPRGContract
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 512

def runSeparated (rich : Bool) (game accuracy seed : List Bool) : Option (List Bool) :=
  (PRGPaperSplitPreparationCost.prepare game accuracy).bind (fun prepared =>
    (RationalPRGBinaryRequest.seedTable (RationalLottoResourceSystem.sampleBitBudget prepared.1 prepared.2.precision) seed).map
      (fun table => PaperPRGDataSampler.output prepared.2 rich table.read))

theorem runSeparated_encoded {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (rich : Bool) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n a.precision) → Bool) :
    runSeparated rich (RationalPRGBinaryInput.encode i) (BinaryAccuracyFrame.encode a) (List.ofFn bits)=
      some (PaperPRGDataSampler.output (NativePRGPreparedSampler.ofInput i a.precision) rich bits) := by
  have hRead : (FixedArrayTable.ofFn bits).read=bits := funext (FixedArrayTable.read_ofFn bits)
  simp only [runSeparated,PRGPaperSplitPreparationCost.prepare_encoded,Option.bind_some,
    NativePRGPreparedSampler.ofInput,RationalPRGBinaryRequest.seedTable_ofFn,Option.map_some,hRead]

theorem input_protocol {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (rich : Bool) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n a.precision) → Bool) :
    runSeparated rich (RationalPRGBinaryInput.encode i) (BinaryAccuracyFrame.encode a) (List.ofFn bits)=
      PaperPRGDataSampler.run rich (RationalPRGBinaryRequest.encode i a) (List.ofFn bits) := by
  have hRead : (FixedArrayTable.ofFn bits).read=bits := funext (FixedArrayTable.read_ofFn bits)
  rw [runSeparated_encoded]
  simp only [PaperPRGDataSampler.run,NativePRGRequestPreparation.prepare_encode,Option.bind_some,
    NativePRGPreparedSampler.ofInput,RationalPRGBinaryRequest.seedTable_ofFn,Option.map_some,hRead]

def drawBound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c k h : ℕ) : ℕ :=
  let V := PRGPaperDrawCost.accuracyWidth i k
  3*h+2^304*(c+1)*((n+1)*model.withWordTraffic.rat V+(n+k+6)*V)

theorem bound_accuracy {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (c K k h : ℕ) (hK : K ≤ k+5) :
    PaperPRGControllerRecords.bound i model c K h ≤ drawBound i model c k h := by
  have hW : PRGPaperDrawCost.width i K ≤ PRGPaperDrawCost.accuracyWidth i k := by
    unfold PRGPaperDrawCost.width RationalPRGLinearFramingWork.uniformWidth PRGPaperDrawCost.accuracyWidth
    exact Nat.mul_le_mul_left (2^90) (by omega)
  have hRat := Nat.mul_le_mul_left (n+1) (model.withWordTraffic.monotone hW)
  have hWords := Nat.mul_le_mul (show n+K+1 ≤ n+k+6 by omega) hW
  exact Nat.add_le_add_left (Nat.mul_le_mul_left (2^304*(c+1))
    (Nat.add_le_add hRat hWords)) (3*h)

theorem draw_work {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w,primitive w ≤ c*w) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n a.precision) → Bool) :
    PaperPRGControllerRecords.work (NativePRGPreparedSampler.ofInput i a.precision) model primitive c rich bits ≤
      drawBound i model c ⌈Real.logb 2 (1/a.real)⌉₊ (NativePRGPreparedSampler.header n).length := by
  have hK : a.precision ≤ ⌈Real.logb 2 (1/a.real)⌉₊+5 := by
    simpa only [a.logExponent_eq_ceil] using a.precision_log_bounds.2
  exact (PaperPRGControllerRecords.work_bound (NativePRGPreparedSampler.ofInput i a.precision)
    model primitive c hPrimitive rich bits).trans (bound_accuracy i model c _ _ _ hK)

theorem fast_draw {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (C d : ℕ)
    (hFast : ∀ w, model.rat w ≤ C*(w+1)*(binaryWordWidth (w+2)+1)^d) (c k h : ℕ) :
    drawBound i model c k h ≤
      3*h+2^304*(c+1)*(C+2)*(n+k+6)*(PRGPaperDrawCost.accuracyWidth i k+1)*
        (binaryWordWidth (PRGPaperDrawCost.accuracyWidth i k+2)+1)^(d+1) := by
  have hh := Nat.mul_le_mul_left (2^304*(c+1))
    (PRGPaperSharpDrawCost.sharp_envelope_profile model C d hFast n (n+k+6)
      (PRGPaperDrawCost.accuracyWidth i k) (by omega))
  unfold drawBound
  nlinarith only [hh]

theorem count_positive {n : ℕ} (i : RationalPRGOriginalInput n) : 0<n := by
  cases n with
  | zero => have h := i.normalized; simp at h
  | succ m => omega

theorem game_length {n : ℕ} (i : RationalPRGOriginalInput n) :
    (RationalPRGBinaryInput.encode i).length ≤ 5*i.originalInputWordWidth+5 := by
  have h := RationalPRGLinearFramingWork.count_le_inputWidth i
  have hLog := Nat.log2_le_self n
  rw [RationalPRGBinaryInput.encode_length]
  unfold binaryWordWidth
  omega

def preparationWidth {n : ℕ} (i : RationalPRGOriginalInput n) : ℕ := 8192*(i.originalInputWordWidth+2)

def preparationBound {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (c : ℕ) : ℕ :=
  2000000*(c+1)*(n+1)*model.withWordTraffic.rat (preparationWidth i)+
    1024*(c+1)*((BinaryAccuracyFrame.encode a).length+1)

theorem preparation_work {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) :
    PRGPaperSplitPreparationCost.work model primitive (RationalPRGBinaryInput.encode i) (BinaryAccuracyFrame.encode a) ≤
      preparationBound i a model c := by
  have hWidth : PRGPaperPreparationCost.width (RationalPRGBinaryInput.encode i).length ≤ preparationWidth i := by
    have h := game_length i
    unfold PRGPaperPreparationCost.width preparationWidth
    omega
  exact (PRGPaperSplitPreparationCost.encoded_work_bound i a model primitive c hPrimitive).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left (2000000*(c+1)*(n+1))
      (model.withWordTraffic.monotone hWidth)) _)

theorem fast_preparation {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (C d : ℕ)
    (hFast : ∀ w,model.rat w ≤ C*(w+1)*(binaryWordWidth (w+2)+1)^d) (c : ℕ) :
    preparationBound i a model c ≤
      2000000*(c+1)*(n+1)*(C+1)*(preparationWidth i+1)*
        (binaryWordWidth (preparationWidth i+2)+1)^(d+1)+
      1024*(c+1)*((BinaryAccuracyFrame.encode a).length+1) := by
  have h := Nat.mul_le_mul_left (2000000*(c+1)*(n+1))
    (model.withWordTraffic_fast C d hFast (preparationWidth i))
  unfold preparationBound
  nlinarith only [h]

theorem output_size {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n a.precision) → Bool) :
    (PaperPRGDataSampler.output (NativePRGPreparedSampler.ofInput i a.precision) rich bits).length ≤
      8*n*PRGPaperDrawCost.accuracyWidth i ⌈Real.logb 2 (1/a.real)⌉₊ := by
  let V := PRGPaperDrawCost.accuracyWidth i ⌈Real.logb 2 (1/a.real)⌉₊
  have hn := count_positive i
  have hK : a.precision ≤ ⌈Real.logb 2 (1/a.real)⌉₊+5 := by
    simpa only [a.logExponent_eq_ceil] using a.precision_log_bounds.2
  have hW : PRGPaperDrawCost.width i a.precision ≤ V := by
    unfold PRGPaperDrawCost.width RationalPRGLinearFramingWork.uniformWidth V PRGPaperDrawCost.accuracyWidth
    exact Nat.mul_le_mul_left (2^90) (by omega)
  have hf := PRGPaperDrawCost.width_facts i a.precision
  have hOut : PRGPaperDrawCost.outputWidth i a.precision ≤ V := by omega
  have hV : 1 ≤ V := by omega
  have hNV := Nat.mul_le_mul_left n hV
  have hSize := PaperPRGDataSampler.output_length (NativePRGPreparedSampler.ofInput i a.precision) rich bits
  have hLog := Nat.log2_le_self n
  have hMove := Nat.mul_le_mul_left (2*n) hOut
  change _ ≤ (NativePRGPreparedSampler.header n).length+2*n*PRGPaperDrawCost.outputWidth i a.precision+n at hSize
  rw [NativePRGPreparedSampler.header_length] at hSize
  unfold binaryWordWidth at hSize
  change _ ≤ 8*n*V
  nlinarith only [hSize,hLog,hMove,hNV,hn]

theorem finite_contract {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) :
    let p := NativePRGPreparedSampler.ofInput i a.precision
    a.precision=⌈Real.logb 2 (32/a.real)⌉₊ ∧
    regret i.realValues (i.a:ℝ) (PaperPRGDataSampler.law p true) (PaperPRGDataSampler.law p false)<a.real ∧
    regret i.realValues (i.b:ℝ) (PaperPRGDataSampler.law p false) (PaperPRGDataSampler.law p true)<a.real ∧
    RationalLottoResourceSystem.sampleBitBudget n a.precision ≤ 3*n+5*⌈Real.logb 2 (1/a.real)⌉₊+3025 ∧
    PRGPaperSplitPreparationCost.prepare (RationalPRGBinaryInput.encode i) (BinaryAccuracyFrame.encode a)=some ⟨n,p⟩ ∧
    PRGPaperSplitPreparationCost.work model primitive (RationalPRGBinaryInput.encode i) (BinaryAccuracyFrame.encode a) ≤
      preparationBound i a model c ∧
    ∀ rich (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n a.precision) → Bool),
      RationalPRGBinaryRequest.ReturnedBudget n (if rich then i.a else i.b) (PaperPRGDataSampler.output p rich bits) ∧
      (PaperPRGDataSampler.output p rich bits).length ≤ 8*n*PRGPaperDrawCost.accuracyWidth i ⌈Real.logb 2 (1/a.real)⌉₊ ∧
      PaperPRGControllerRecords.work p model primitive c rich bits ≤
        drawBound i model c ⌈Real.logb 2 (1/a.real)⌉₊ (NativePRGPreparedSampler.header n).length := by
  have hr := PaperPRGDataSampler.accuracy_regrets i a
  refine ⟨a.precision_eq_paper_ceil,hr.1,hr.2,a.sampleBitBudget_ceil_bound n,
    PRGPaperSplitPreparationCost.prepare_encoded i a,preparation_work i a model primitive c hPrimitive,?_⟩
  intro rich bits
  exact ⟨PaperPRGDataSampler.output_budget (NativePRGPreparedSampler.ofInput i a.precision) rich bits,output_size i a rich bits,
    draw_work i a model primitive c hPrimitive rich bits⟩

theorem independent_laws {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) :
    let R := RationalLottoResourceSystem.sampleBitBudget n p.precision
    MeasureTheory.Measure.map (fun bits =>
      ((PaperPRGDataSampler.sample p true (firstBitBlock R R bits)).realAllocation,
        (PaperPRGDataSampler.sample p false (secondBitBlock R R bits)).realAllocation))
      (fairBitLaw (R+R) : MeasureTheory.Measure (Fin (R+R) → Bool)) =
      (PaperPRGDataSampler.law p true : MeasureTheory.Measure (Allocation n)).prod
        (PaperPRGDataSampler.law p false : MeasureTheory.Measure (Allocation n)) := by
  dsimp only
  exact fairBitBlocks_map_product
    (RationalLottoResourceSystem.sampleBitBudget n p.precision)
    (RationalLottoResourceSystem.sampleBitBudget n p.precision)
    (fun bits => (PaperPRGDataSampler.sample p true bits).realAllocation)
    (fun bits => (PaperPRGDataSampler.sample p false bits).realAllocation)

theorem schoolbook_with_traffic (W : ℕ) (hW : 1 ≤ W) :
    RationalCostModel.schoolbook.withWordTraffic.rat W ≤ 7*W*W := by
  have hLog := Nat.log2_le_self (W+2)
  have hMul := Nat.mul_le_mul_left W (show binaryWordWidth (W+2)+1 ≤ W+4 by
    unfold binaryWordWidth; omega)
  have hSquare := Nat.mul_le_mul_left W hW
  unfold RationalCostModel.withWordTraffic RationalCostModel.schoolbook
  dsimp only
  nlinarith only [hMul,hSquare]

end Blotto.PaperPRGContract
