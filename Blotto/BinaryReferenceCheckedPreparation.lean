import Blotto.ReferenceArrayBuilder
import Blotto.BinarySequentialGameFrame

/-! Reference-only table construction is joined to the actual sequential
checked game reader. The decoded count is paid by consumed input bits, so
even full-prefix reference copies have the required n*inputLength price. -/

namespace Blotto.BinaryReferenceCheckedPreparation
set_option autoImplicit false
set_option maxHeartbeats 2000000

def table (data : BinaryGameWords) (hCount : data.values.length = data.count) : FixedArrayTable data.count ℚ :=
  ⟨ReferenceArrayBuilder.array data.values,by rw [ReferenceArrayBuilder.array_data]; simpa using hCount⟩

theorem table_eq (data : BinaryGameWords) (hCount : data.values.length = data.count) :
    table data hCount = data.valueTable hCount := by
  unfold table BinaryGameWords.valueTable
  simp only [ReferenceArrayBuilder.array_data]

def checked (bits : List Bool) : Option ((Σ n,RationalPRGOriginalInput n) × List Bool) :=
  (BinarySequentialGameFrame.game bits).bind (fun parsed =>
    if h : parsed.1.values.length = parsed.1.count then
      (checkRationalPRG (table parsed.1 h).read parsed.1.a parsed.1.b).map
        (fun i => (⟨parsed.1.count,i⟩,parsed.2))
    else none)

theorem checked_refines (bits : List Bool) : checked bits = BinarySequentialGameFrame.checked bits := by
  simp only [checked,BinarySequentialGameFrame.checked,table_eq]

def tableWork (primitive : ℕ → ℕ) (bits : List Bool) : ℕ :=
  match BinarySequentialGameFrame.game bits with
  | none => 0
  | some parsed =>
      if parsed.1.values.length = parsed.1.count then
        ReferenceArrayBuilder.work primitive (StoredArrayReferenceList.poolAddressWidth parsed.1.count (9*bits.length))
          parsed.1.values 0
      else 0

def tableBound (c count frameLength : ℕ) : ℕ :=
  (4*c+20)*(count+1)*(frameLength+1)*(binaryWordWidth (9*frameLength+1)+1)+1

theorem tableBound_count_mono (c frameLength : ℕ) : Monotone (fun count => tableBound c count frameLength) := by
  intro a b hab
  unfold tableBound
  dsimp only
  gcongr

theorem table_work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (bits : List Bool) (data : BinaryGameWords) (suffix : List Bool)
    (hGame : BinarySequentialGameFrame.game bits = some (data,suffix)) :
    tableWork primitive bits ≤ tableBound c data.count bits.length := by
  have hOld : RationalPRGBinaryInput.read bits = some (data,suffix) := by
    rwa [BinarySequentialGameFrame.game_refines] at hGame
  have hSizes := RationalPRGBinaryInput.read_wordWidths bits data suffix hOld
  have hCount : data.values.length = data.count := hSizes.2.1
  have hN : data.count ≤ bits.length := hSizes.1
  let A := StoredArrayReferenceList.poolAddressWidth data.count (9*bits.length)
  let M := binaryWordWidth (9*bits.length+1)
  have hSmall : data.count+1 ≤ 9*bits.length+1 := by omega
  have hw : binaryWordWidth (data.count+1) ≤ M := binaryWordWidth_mono hSmall
  have ha := StoredArrayReferenceList.poolAddressWidth_log_bound data.count (9*bits.length)
  change A ≤ binaryWordWidth (data.count+1)+M at ha
  have hp := Nat.mul_le_mul_left (4*c) (Nat.add_le_add_right hw 1)
  have hFactor : 4*A+4*c*(binaryWordWidth (data.count+1)+1)+12 ≤ (4*c+20)*(M+1) := by
    nlinarith only [ha,hw,hp]
  have hSize : data.count*(data.count+1) ≤ (data.count+1)*(bits.length+1) := by
    simpa only [Nat.succ_eq_add_one,Nat.mul_comm] using Nat.mul_le_mul_right (data.count+1) (hN.trans (Nat.le_succ _))
  have hMul := Nat.mul_le_mul hSize hFactor
  have hWork := ReferenceArrayBuilder.work_bound primitive c hPrimitive A data.count data.values 0
    (by simpa only [Nat.zero_add,hCount] using (Nat.le_refl data.count))
  simp only [hCount] at hWork
  simp only [tableWork,hGame,ite_eq_left hCount]
  change ReferenceArrayBuilder.work primitive A data.values 0 ≤ _
  unfold tableBound
  change _ ≤ (4*c+20)*(data.count+1)*(bits.length+1)*(M+1)+1
  have hPrice : data.count*(data.count+1)*(4*A+4*c*(binaryWordWidth (data.count+1)+1)+12) ≤
      (4*c+20)*(data.count+1)*(bits.length+1)*(M+1) := by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hMul
  exact hWork.trans (Nat.add_le_add_right hPrice 1)

def work (model : RationalCostModel) (primitive : ℕ → ℕ) (bits : List Bool) : ℕ :=
  BinarySequentialGameFrame.checkedWork model primitive bits+tableWork primitive bits

theorem work_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (bits : List Bool) (data : BinaryGameWords) (suffix : List Bool)
    (hGame : BinarySequentialGameFrame.game bits = some (data,suffix)) :
    work model primitive bits ≤ BinarySequentialGameFrame.checkedPrice model c data.count bits.length+
      tableBound c data.count bits.length :=
  Nat.add_le_add (BinarySequentialGameFrame.checked_work_bound model primitive c hPrimitive bits data suffix hGame)
    (table_work_bound primitive c hPrimitive bits data suffix hGame)

theorem table_prefix_space_bound (bits : List Bool) (data : BinaryGameWords) (suffix : List Bool)
    (hGame : BinarySequentialGameFrame.game bits = some (data,suffix)) (used : ℕ) :
    let A := StoredArrayReferenceList.poolAddressWidth data.count (9*bits.length)
    rationalWordWidth data.a+rationalWordWidth data.b+RationalAggregateRecognitionCost.totalWidth data.values+
      A*(2*data.values.length+2*((ReferenceArrayBuilder.advance used (data.values,#[])).2.size+1)) ≤
        9*bits.length+A*(4*data.count+2) := by
  have hOld : RationalPRGBinaryInput.read bits = some (data,suffix) := by
    rwa [BinarySequentialGameFrame.game_refines] at hGame
  have hCount := (RationalPRGBinaryInput.read_wordWidths bits data suffix hOld).2.1
  have hWidth : rationalWordWidth data.a+rationalWordWidth data.b+
      RationalAggregateRecognitionCost.totalWidth data.values ≤ 9*bits.length := by
    have h := (BinaryDecodedAggregateSize.game_width_consumed bits data suffix hOld).1
    omega
  have hp := ReferenceArrayBuilder.every_prefix_with_input_list used
    (StoredArrayReferenceList.poolAddressWidth data.count (9*bits.length))
    (rationalWordWidth data.a+rationalWordWidth data.b+RationalAggregateRecognitionCost.totalWidth data.values) data.values
  simp only [hCount] at hp ⊢
  exact hp.trans (Nat.add_le_add_right hWidth _)

theorem table_work_frame_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (bits : List Bool) : tableWork primitive bits ≤ tableBound c bits.length bits.length := by
  cases hGame : BinarySequentialGameFrame.game bits with
  | none => simp only [tableWork,hGame]; exact Nat.zero_le _
  | some parsed =>
    rcases parsed with ⟨data,suffix⟩
    have hOld : RationalPRGBinaryInput.read bits = some (data,suffix) := by
      rwa [BinarySequentialGameFrame.game_refines] at hGame
    have hCount := (RationalPRGBinaryInput.read_wordWidths bits data suffix hOld).1
    exact (table_work_bound primitive c hPrimitive bits data suffix hGame).trans
      (tableBound_count_mono c bits.length hCount)

theorem work_frame_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (bits : List Bool) :
    work model primitive bits ≤ BinarySequentialGameFrame.frameCheckedPrice model c bits.length+
      tableBound c bits.length bits.length :=
  Nat.add_le_add (BinarySequentialGameFrame.checked_work_frame_bound model primitive c hPrimitive bits)
    (table_work_frame_bound primitive c hPrimitive bits)

theorem encoded_contract {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (suffix : List Bool) :
    let frame := RationalPRGBinaryInput.encode i++suffix
    checked frame = some (⟨n,i⟩,suffix) ∧ work model primitive frame ≤
      BinarySequentialGameFrame.checkedPrice model c n frame.length+tableBound c n frame.length := by
  have hGame : BinarySequentialGameFrame.game (RationalPRGBinaryInput.encode i++suffix) =
      some (⟨n,i.a,i.b,List.ofFn i.values⟩,suffix) := by
    rw [BinarySequentialGameFrame.game_refines]
    exact RationalPRGBinaryInput.read_encode_append i suffix
  constructor
  · exact (checked_refines _).trans (BinarySequentialGameFrame.encoded_contract i model primitive c hPrimitive suffix).1
  · exact work_bound model primitive c hPrimitive (RationalPRGBinaryInput.encode i++suffix)
      ⟨n,i.a,i.b,List.ofFn i.values⟩ suffix hGame

end Blotto.BinaryReferenceCheckedPreparation
