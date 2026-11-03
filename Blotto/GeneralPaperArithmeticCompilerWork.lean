import Blotto.GeneralPaperArithmeticUnitSourceWork

/-! Complete arithmetic work of the existing selected strict compiler.
The native retained matrix supplies the basis call; final affine checks
and physical endpoint anchors are included, with no cost/height oracle. -/
namespace Blotto.GeneralPaperArithmeticCompilerWork
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def inputWord (m k : ℕ) : ℕ := binaryWordWidth (4*m*(prepare m k).H*(prepare m k).qbar*(prepare m k).qbar)
def inputPrice (m k : ℕ) : ℕ :=
  12*inputWord m k+128*(m+1)*((prepare m k).K+1)*(inputWord m k+2)+
    1024*(m*((prepare m k).K-1)+m+1)+274

theorem input_bound (m k p q : ℕ) (reciprocal : Bool) (hp : p≤(prepare m k).qbar) (hq : q≤(prepare m k).qbar) :
    GeneralPaperRetainedBasisInputsPrice.arithmeticProfile m (prepare m k).K (prepare m k).H p q reciprocal≤ inputPrice m k := by
  have hw : binaryWordWidth (4*m*(prepare m k).H*p*q)≤ inputWord m k :=
    binaryWordWidth_mono (Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) hq)
  have hd := GeneralPaperConstructedWordGrowth.ceiling_depth_bound (4*m*(prepare m k).H*p*q)
  have ht : (GeneralPaperInitializerParameters.prepare m (prepare m k).H p q reciprocal).depth+1≤ inputWord m k+2 := by
    change (GeneralPaperPowerCeiling.ceiling (4*m*(prepare m k).H*p*q)).doublings+1+1≤_
    omega
  unfold GeneralPaperRetainedBasisInputsPrice.arithmeticProfile inputPrice
  gcongr

def checkPrice (T m K S : ℕ) : ℕ :=
  256*(m*(K-1)+1)+1024*(m*(K-1)+m*T+m+1)+2048*(m+1)*(K+1)*(S+1)+48
def basisPrice (T m K S : ℕ) : ℕ :=
  8192*(m*(K-1)+3)^3+(m*(K-1))*GeneralPaperEndpointPriceControl.profile T m K S 1 1
def endpointPrice (m k : ℕ) : ℕ :=
  inputPrice m k+basisPrice (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S+
    512*(m*((prepare m k).K-1)+1)^2+
    checkPrice (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S+80

theorem endpoint_of_bounds {T m K S : ℕ} (model : RationalCostModel) (H p q A B : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (endpoint : Farey.Fraction) (value : ℚ) (hm : 0<m)
    (hA : (GeneralPaperRetainedBasisInputs.run false model 1 H p q reciprocal prep matrix).2≤A)
    (hB : (GeneralPaperSharedBasisWork.run prep (GeneralPaperRetainedBasisInputs.run false model 1 H p q reciprocal prep matrix).1).2≤B) :
    (GeneralPaperRetainedBasisEndpoint.run model H p q reciprocal prep matrix endpoint value).2≤
      A+B+512*(m*(K-1)+1)^2+checkPrice T m K S+80 := by
  rw [GeneralPaperRetainedBasisEndpoint.run]
  split
  · dsimp only
    omega
  · dsimp only
    cases hr : (GeneralPaperSharedBasisWork.run prep (GeneralPaperRetainedBasisInputs.run false model 1 H p q reciprocal prep matrix).1).1 with
    | none => dsimp only;omega
    | some state =>
      have ha := GeneralPaperBasisAffineData.work state
      have hc := GeneralPaperRawAffineEndpoint.arithmetic_work model hm prep.dictionary.label
        (GeneralPaperRetainedBasisInputs.run false model 1 H p q reciprocal prep matrix).1.matrix S prep.threshold
        (GeneralPaperRetainedBasisInputs.run false model 1 H p q reciprocal prep matrix).1.controls.auxiliary
        (if reciprocal then 1/value else value)
        (GeneralPaperRetainedBasisInputs.run false model 1 H p q reciprocal prep matrix).1.betaN
        (GeneralPaperRetainedBasisEndpoint.numerator endpoint reciprocal)
        (GeneralPaperRetainedBasisInputs.run false model 1 H p q reciprocal prep matrix).1.controls.N
        (GeneralPaperRetainedBasisEndpoint.denominator endpoint reciprocal) (GeneralPaperBasisAffineData.prepare state)
      dsimp only
      change _≤checkPrice T m K S at hc
      omega

theorem endpoint_work {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field (prepare m k).K))
    (hMatrix : matrix=(GeneralPaperScoreMatrixWork.matrixRun (GeneralPaperScoreScaleParameters.prepare m k).depth
      (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal).dictionary
      (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S).1)
    (endpoint : Farey.Fraction) (value : ℚ) :
    (GeneralPaperRetainedBasisEndpoint.run model (prepare m k).H
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal
      (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal) matrix endpoint value).2≤endpointPrice m k := by
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hi := GeneralPaperRetainedBasisInputs.actual_data false model 1 k f.num f.den reciprocal prep
    (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) matrix hMatrix hm hf.1 f.den_pos
  have hA := (GeneralPaperRetainedBasisInputsPrice.arithmetic_work model (prepare m k).H f.num f.den reciprocal prep matrix).trans
    (input_bound m k f.num f.den reciprocal (hf.2.1.le.trans hf.2.2) hf.2.2)
  have hB : (GeneralPaperSharedBasisWork.run prep
      (GeneralPaperRetainedBasisInputs.run false model 1 (prepare m k).H f.num f.den reciprocal prep matrix).1).2≤
        basisPrice (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S := by
    rw [hi]
    exact GeneralPaperSharedBasisWork.actual_paper_bound k Qv hm hQv weights hp hs b hb reciprocal
  exact endpoint_of_bounds model (prepare m k).H f.num f.den _ _ reciprocal prep matrix endpoint value hm hA hB

def strictPrice (m k : ℕ) : ℕ := GeneralPaperRetainedTransferPrice.arithmeticProfile m (prepare m k).K (prepare m k).S
  (GeneralPaperScoreScaleParameters.prepare m k).depth
def branchPrice (m k : ℕ) : ℕ := strictPrice m k+endpointPrice m k+80
def columnsPrice (m K : ℕ) : ℕ := m*(K*137+44*(K+1)+64)+44*(m+1)+64
def modifiedPrice (m k : ℕ) : ℕ := branchPrice m k+columnsPrice m (prepare m k).K
def price (m k : ℕ) : ℕ := modifiedPrice m k+130

theorem branch_work {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
    (endpoint : Farey.Fraction) (value : ℚ) :
    (GeneralPaperRetainedCompilerBranch.run model (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den
      (GeneralPaperScoreScaleParameters.labels_positive m k) columns values (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
      reciprocal endpoint value).2≤branchPrice m k := by
  let retained := GeneralPaperRetainedTransferPreparation.run false model 1 (GeneralPaperScoreScaleParameters.prepare m k).depth
    (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) columns values (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
  have hpData := GeneralPaperRetainedCompilerSource.prepared model k Qv hQv weights hp hs b reciprocal columns values hColumns hValues
  have hmData := GeneralPaperRetainedCompilerBranch.matrix model (GeneralPaperScoreScaleParameters.prepare m k).depth
    (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) (GeneralPaperScoreScaleParameters.score_cap m k)
  dsimp only at hmData
  erw [hpData,hValues] at hmData
  have he := endpoint_work model k Qv hm hQv weights hp hs b hb reciprocal retained.1.matrix hmData endpoint value
  rw [←hpData] at he
  have ht := GeneralPaperRetainedTransferPrice.arithmetic_work model (GeneralPaperScoreScaleParameters.prepare m k).depth
    (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) columns values (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
  change retained.2≤strictPrice m k at ht
  change (GeneralPaperRetainedBasisEndpoint.run model (prepare m k).H
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den
    reciprocal retained.1.prepared retained.1.matrix endpoint value).2≤endpointPrice m k at he
  dsimp only [retained] at ht he
  dsimp only [GeneralPaperRetainedCompilerBranch.run]
  split <;> dsimp only <;> unfold branchPrice <;> omega

theorem modified_work {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
    (endpoint : Farey.Fraction) (value : ℚ) :
    (GeneralPaperRetainedModifiedColumns.run model (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den
      (GeneralPaperScoreScaleParameters.labels_positive m k) columns values (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
      reciprocal endpoint value).2≤modifiedPrice m k := by
  have hw := GeneralPaperRetainedModifiedColumns.arithmetic_work model (GeneralPaperScoreScaleParameters.prepare m k).depth
    (prepare m k).S (prepare m k).H (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) reciprocal endpoint value
  have hc := branch_work model k Qv hm hQv weights hp hs b hb reciprocal columns values hColumns hValues endpoint value
  change _≤ _+m*((prepare m k).K*137+44*((prepare m k).K+1)+64)+44*(m+1)+64 at hw
  unfold modifiedPrice columnsPrice
  omega

theorem pair_work {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1)
    (columns : GeneralPaperOriginalDrawEquilibrium.Columns
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K)
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hRich : GeneralPaperRowQuantizer.dictionary columns.rich=GeneralPaperSourceUnchangedDictionary.run k Qv weights b false)
    (hPoor : GeneralPaperRowQuantizer.dictionary columns.poor=GeneralPaperSourceUnchangedDictionary.run k Qv weights b true)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) :
    (GeneralPaperRetainedCompilerPair.run model (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H
      (prepare m k).Qg (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperProxyClassifier.classify m k b) (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value values columns).2≤price m k := by
  have h := GeneralPaperRetainedCompilerPair.arithmetic_work model (GeneralPaperScoreScaleParameters.prepare m k).depth
    (prepare m k).S (prepare m k).H (prepare m k).Qg (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperProxyClassifier.classify m k b) (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value values columns
  cases hc : (GeneralPaperProxyClassifier.classify m k b).choice.modify with
  | none => simp only [hc] at h;unfold price;omega
  | some side =>
    cases side with
    | rich =>
      have hr := modified_work model k Qv hm hQv weights hp hs b hb false columns.rich values hRich hValues
        (GeneralPaperRetainedEndpointFraction.run (fun _ => 1) 1 (prepare m k).Qg (grid_positive m k) (GeneralPaperProxyClassifier.classify m k b)).1
        (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
      simp only [hc] at h
      exact h.trans (Nat.add_le_add_right hr 130)
    | poor =>
      have hr := modified_work model k Qv hm hQv weights hp hs b hb true columns.poor values hPoor hValues
        (GeneralPaperRetainedEndpointFraction.run (fun _ => 1) 1 (prepare m k).Qg (grid_positive m k) (GeneralPaperProxyClassifier.classify m k b)).1
        (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
      simp only [hc] at h
      exact h.trans (Nat.add_le_add_right hr 130)

end Blotto.GeneralPaperArithmeticCompilerWork
