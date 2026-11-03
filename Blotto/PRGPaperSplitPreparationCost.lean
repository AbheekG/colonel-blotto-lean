import Blotto.PRGPaperDrawCost

/-! The paper receives the game and the accuracy as separate binary inputs.
Read/check the game on its own input, then read the accuracy; no game rational
operation is charged at the accuracy input's length. Word traffic can be
included in the chosen nondecreasing superadditive rational majorant. This
choice preserves a soft-linear arithmetic profile and asserts no native rate.
-/

namespace Blotto.RationalCostModel
set_option autoImplicit false

def withWordTraffic (model : RationalCostModel) : RationalCostModel where
  rat := fun w => model.rat w+w*(binaryWordWidth (w+2)+1)
  monotone := by
    intro a b hab
    exact Nat.add_le_add (model.monotone hab)
      (Nat.mul_le_mul hab (Nat.add_le_add_right (binaryWordWidth_mono (Nat.add_le_add_right hab 2)) 1))
  word_le := fun w => (model.word_le w).trans (Nat.le_add_right _ _)
  superadditive := by
    intro a b
    have ha := Nat.mul_le_mul_left a (Nat.add_le_add_right
      (binaryWordWidth_mono (show a+2 ≤ a+b+2 by omega)) 1)
    have hb := Nat.mul_le_mul_left b (Nat.add_le_add_right
      (binaryWordWidth_mono (show b+2 ≤ a+b+2 by omega)) 1)
    have hRat := model.superadditive a b
    nlinarith only [ha,hb,hRat]

theorem withWordTraffic_rat (model : RationalCostModel) (w : ℕ) :
    model.withWordTraffic.rat w = model.rat w+w*(binaryWordWidth (w+2)+1) := rfl

theorem withWordTraffic_fast (model : RationalCostModel) (C d : ℕ)
    (hFast : ∀ w, model.rat w ≤ C*(w+1)*(binaryWordWidth (w+2)+1)^d) (w : ℕ) :
    model.withWordTraffic.rat w ≤ (C+1)*(w+1)*(binaryWordWidth (w+2)+1)^(d+1) := by
  have h := PRGPaperDrawCost.envelope_at_profile model C d hFast 0 1 w (by omega)
  simpa only [Nat.zero_add,Nat.one_mul,Nat.mul_one,withWordTraffic_rat] using h

end Blotto.RationalCostModel

namespace Blotto.PRGPaperSplitPreparationCost
set_option autoImplicit false
set_option maxHeartbeats 2000000

def prepare (game accuracy : List Bool) : Option (Σ n,NativePRGPreparedSampler.Prepared n) :=
  (BinaryReferenceCheckedPreparation.checked game).bind (fun parsed =>
    if parsed.2 = [] then
      (BinaryAccuracyWords.read accuracy).bind (fun words =>
        if words.2 = [] then some ⟨parsed.1.1,NativePRGPreparedSampler.ofInput parsed.1.2 words.1.precision⟩
        else none)
    else none)

def work (model : RationalCostModel) (primitive : ℕ → ℕ) (game accuracy : List Bool) : ℕ :=
  BinaryReferenceCheckedPreparation.work model primitive game+
    BinaryAccuracyWords.readPrecisionBitWork primitive accuracy+4+
      match prepare game accuracy with
      | none => 2
      | some prepared => NativePRGPreparedSampler.headerWork primitive prepared.1+
          PRGPaperPreparationCost.wrappingWork primitive (game.length+accuracy.length)
            prepared.1 prepared.2.precision

def execute (model : RationalCostModel) (primitive : ℕ → ℕ) (game accuracy : List Bool) :
    Option (Σ n,NativePRGPreparedSampler.Prepared n) × ℕ :=
  (prepare game accuracy,work model primitive game accuracy)

theorem prepare_encoded {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput) :
    prepare (RationalPRGBinaryInput.encode i) (BinaryAccuracyFrame.encode a) =
      some ⟨n,NativePRGPreparedSampler.ofInput i a.precision⟩ := by
  have hGame : BinaryReferenceCheckedPreparation.checked (RationalPRGBinaryInput.encode i) =
      some (⟨n,i⟩,[]) := by
    simpa only [BinaryReferenceCheckedPreparation.checked_refines,BinarySequentialGameFrame.checked_refines,
      List.append_nil] using RationalPRGBinaryInput.readChecked_encode_append i []
  obtain ⟨words,hRead,hNumeric⟩ := BinaryAccuracyWords.read_encode_append a []
  have hK : words.precision = a.precision := by rw [words.precision_eq,hNumeric]
  simp only [List.append_nil] at hRead
  simp only [prepare,hGame,Option.bind_some,ite_true,hRead,hK]

theorem preparation_envelope (model : RationalCostModel) (c count length : ℕ) :
    PRGPaperPreparationCost.bound model c count length ≤
      1000000*(c+1)*(count+1)*model.withWordTraffic.rat (PRGPaperPreparationCost.width length) := by
  have hW : length+2 ≤ PRGPaperPreparationCost.width length := by
    unfold PRGPaperPreparationCost.width
    omega
  have hLog : PRGPaperPreparationCost.logFactor length ≤
      binaryWordWidth (PRGPaperPreparationCost.width length+2)+1 := by
    apply Nat.add_le_add_right
    apply binaryWordWidth_mono
    unfold PRGPaperPreparationCost.width
    omega
  have hh := Nat.mul_le_mul hW hLog
  unfold PRGPaperPreparationCost.bound RationalCostModel.withWordTraffic
  dsimp only
  exact Nat.mul_le_mul_left (1000000*(c+1)*(count+1)) (Nat.add_le_add_left hh _)

def bound (model : RationalCostModel) (c count gameLength accuracyLength : ℕ) : ℕ :=
  2000000*(c+1)*(count+1)*model.withWordTraffic.rat (PRGPaperPreparationCost.width gameLength)+
    1024*(c+1)*(accuracyLength+1)

theorem encoded_work_bound {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) :
    work model primitive (RationalPRGBinaryInput.encode i) (BinaryAccuracyFrame.encode a) ≤
      bound model c n (RationalPRGBinaryInput.encode i).length (BinaryAccuracyFrame.encode a).length := by
  let F := (RationalPRGBinaryInput.encode i).length
  let E := (BinaryAccuracyFrame.encode a).length
  let P := model.withWordTraffic.rat (PRGPaperPreparationCost.width F)
  have hInput := PRGPaperPreparationCost.encoded_bounds i a
  have hn : n ≤ F := by
    have hg := RationalPRGBinaryInput.encode_length i
    omega
  have hGame := (BinaryReferenceCheckedPreparation.encoded_contract i model primitive c hPrimitive []).2
  simp only [List.append_nil] at hGame
  have hHeader := NativePRGPreparedSampler.header_work_bound primitive c hPrimitive n
  have hComponent : BinaryReferenceCheckedPreparation.work model primitive (RationalPRGBinaryInput.encode i)+
      NativePRGPreparedSampler.headerWork primitive n ≤
        NativePRGRequestPreparation.componentBound model c n F 0 := by
    unfold NativePRGRequestPreparation.componentBound
    dsimp only [F]
    omega
  have hPrepared := (hComponent.trans (PRGPaperPreparationCost.component_bound model c n F 0 hn (Nat.zero_le _))).trans
    (preparation_envelope model c n F)
  have hAccuracy := BinaryAccuracyWords.readPrecisionBitWork_bound primitive c hPrimitive (BinaryAccuracyFrame.encode a)
  have hPrecision := (PRGPaperPreparationCost.prepared_bounds (RationalPRGBinaryRequest.encode i a)
    ⟨n,NativePRGPreparedSampler.ofInput i a.precision⟩ (NativePRGRequestPreparation.prepare_encode i a)).2
  change a.precision ≤ (RationalPRGBinaryRequest.encode i a).length+6 at hPrecision
  simp only [RationalPRGBinaryRequest.encode,List.length_append] at hPrecision
  have hWrapper := PRGPaperPreparationCost.wrapping_work_bound primitive c hPrimitive (F+E) n a.precision
    (by omega) hPrecision
  have hP : F+10 ≤ P := by
    apply le_trans (b := PRGPaperPreparationCost.width F)
    · unfold PRGPaperPreparationCost.width; omega
    · exact model.withWordTraffic.word_le _
  have hNP : F+10 ≤ (n+1)*P :=
    hP.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right P (show 1 ≤ n+1 by omega))
  have hExtra := Nat.mul_le_mul_left (64*(c+1)) hNP
  unfold work
  rw [prepare_encoded]
  dsimp only [NativePRGPreparedSampler.ofInput]
  unfold bound
  change _ ≤ 2000000*(c+1)*(n+1)*P+1024*(c+1)*(E+1)
  change BinaryAccuracyWords.readPrecisionBitWork primitive (BinaryAccuracyFrame.encode a) ≤
    (127+48*c)*E+634+240*c at hAccuracy
  change _ ≤ 1000000*(c+1)*(n+1)*P at hPrepared
  nlinarith only [hPrepared,hAccuracy,hWrapper,hExtra]

theorem encoded_contract {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) :
    (execute model primitive (RationalPRGBinaryInput.encode i) (BinaryAccuracyFrame.encode a)).1 =
      some ⟨n,NativePRGPreparedSampler.ofInput i a.precision⟩ ∧
    (execute model primitive (RationalPRGBinaryInput.encode i) (BinaryAccuracyFrame.encode a)).2 ≤
      bound model c n (RationalPRGBinaryInput.encode i).length (BinaryAccuracyFrame.encode a).length :=
  ⟨prepare_encoded i a,encoded_work_bound i a model primitive c hPrimitive⟩

end Blotto.PRGPaperSplitPreparationCost
