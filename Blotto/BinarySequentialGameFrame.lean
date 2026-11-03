import Blotto.BinarySequentialRationalFrame
import Blotto.BinaryListLengthWork

/-! The actual sequential natural/rational readers reach list, game and checked
game parsing. Complete parsed results equal the old interfaces on every input.
The source profiles include recursive count/control prices and reached checks.
Value-table materialization, further metadata and native representation are
separate; the checker price is its existing arithmetic-model ledger. -/
namespace Blotto.BinarySequentialGameFrame
set_option autoImplicit false

def list : ℕ → List Bool → Option (List ℚ × List Bool)
  | 0,bits => some ([],bits)
  | count+1,bits =>
      (BinarySequentialRationalFrame.read bits).bind (fun first =>
        (list count first.2).map (fun rest => (first.1::rest.1,rest.2)))

theorem list_refines (count : ℕ) (bits : List Bool) : list count bits = BinaryRatListFrame.read count bits := by
  induction count generalizing bits with
  | zero => rfl
  | succ count ih => simp only [list,BinaryRatListFrame.read,BinarySequentialRationalFrame.read_refines,ih]

def game (bits : List Bool) : Option (BinaryGameWords × List Bool) :=
  (BinarySequentialPayloadDecoder.read bits).bind (fun dim =>
    (BinarySequentialRationalFrame.read dim.2).bind (fun first =>
      (BinarySequentialRationalFrame.read first.2).bind (fun second =>
        (list dim.1 second.2).map (fun row => (⟨dim.1,first.1,second.1,row.1⟩,row.2)))))

theorem game_refines (bits : List Bool) : game bits = RationalPRGBinaryInput.read bits := by
  simp only [game,RationalPRGBinaryInput.read,BinarySequentialPayloadDecoder.read_refines,
    BinarySequentialRationalFrame.read_refines,list_refines]

def checked (bits : List Bool) : Option ((Σ n,RationalPRGOriginalInput n) × List Bool) :=
  (game bits).bind (fun parsed =>
    if h : parsed.1.values.length = parsed.1.count then
      (checkRationalPRG (parsed.1.valueTable h).read parsed.1.a parsed.1.b).map
        (fun i => (⟨parsed.1.count,i⟩,parsed.2))
    else none)

theorem checked_refines (bits : List Bool) : checked bits = RationalPRGBinaryInput.readChecked bits := by
  simp only [checked,RationalPRGBinaryInput.readChecked,game_refines]

def listWork (model : RationalCostModel) (primitive : ℕ → ℕ) : ℕ → List Bool → ℕ
  | 0,_ => BinarySequentialPayloadCost.scalarPrice primitive 0+1
  | count+1,bits =>
      BinarySequentialPayloadCost.scalarPrice primitive (count+1)+BinarySequentialRationalFrame.work model primitive bits+
        match BinarySequentialRationalFrame.read bits with
        | none => 0
        | some first => listWork model primitive count first.2+8

def listPrice (model : RationalCostModel) (c count length : ℕ) : ℕ :=
  (count+1)*(BinarySequentialRationalFrame.price model c length+BinarySequentialPayloadCost.scalarBound c count+9)

theorem list_work_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (count : ℕ) (bits : List Bool) :
    listWork model primitive count bits ≤ listPrice model c count bits.length := by
  induction count generalizing bits with
  | zero =>
      have hs := BinarySequentialPayloadCost.scalar_price_bound primitive c hPrimitive 0
      simp only [listWork,listPrice,Nat.zero_add,Nat.one_mul]
      omega
  | succ count ih =>
      have hs := BinarySequentialPayloadCost.scalar_price_bound primitive c hPrimitive (count+1)
      have hr := BinarySequentialRationalFrame.work_bound model primitive c hPrimitive bits
      rw [listWork]
      cases hRead : BinarySequentialRationalFrame.read bits with
      | none =>
          simp only
          unfold listPrice
          nlinarith only [hs,hr]
      | some first =>
          rcases first with ⟨q,tail⟩
          have hTail : tail.length ≤ bits.length := by
            have hh := BinarySequentialRationalFrame.read_width_consumed bits q tail hRead
            omega
          have hRest := ih tail
          have hp := Nat.add_le_add_right
            (Nat.add_le_add (BinarySequentialRationalFrame.price_mono model c hTail)
              (BinarySequentialPayloadCost.scalarBound_mono c (show count ≤ count+1 by omega))) 9
          have hm := Nat.mul_le_mul_left (count+1) hp
          unfold listPrice at hRest ⊢
          simp only
          nlinarith only [hs,hr,hRest,hm]

theorem list_work_frame_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (count capacity : ℕ) (hCount : count ≤ capacity) (bits : List Bool) :
    listWork model primitive count bits ≤
      (bits.length+1)*(BinarySequentialRationalFrame.price model c bits.length+
        BinarySequentialPayloadCost.scalarBound c capacity+9) := by
  induction count generalizing bits with
  | zero =>
      have hs := (BinarySequentialPayloadCost.scalar_price_bound primitive c hPrimitive 0).trans
        (BinarySequentialPayloadCost.scalarBound_mono c (Nat.zero_le capacity))
      simp only [listWork]
      nlinarith only [hs]
  | succ count ih =>
      have hs := (BinarySequentialPayloadCost.scalar_price_bound primitive c hPrimitive (count+1)).trans
        (BinarySequentialPayloadCost.scalarBound_mono c hCount)
      have hr := BinarySequentialRationalFrame.work_bound model primitive c hPrimitive bits
      rw [listWork]
      cases hRead : BinarySequentialRationalFrame.read bits with
      | none => simp only; nlinarith only [hs,hr]
      | some first =>
          rcases first with ⟨q,tail⟩
          have hOld : BinaryRatFrame.read bits = some (q,tail) := by
            rwa [BinarySequentialRationalFrame.read_refines] at hRead
          have hTail := BinaryRatFrame.read_suffix_lt bits q tail hOld
          have hi := ih (by omega : count ≤ capacity) tail
          have hm := Nat.mul_le_mul (show tail.length+1 ≤ bits.length by omega)
            (Nat.add_le_add_right (Nat.add_le_add_right
              (BinarySequentialRationalFrame.price_mono model c hTail.le)
              (BinarySequentialPayloadCost.scalarBound c capacity)) 9)
          simp only
          nlinarith only [hs,hr,hi,hm]

def gameWork (model : RationalCostModel) (primitive : ℕ → ℕ) (bits : List Bool) : ℕ :=
  BinarySequentialNatReadCost.work primitive bits+16+
    match BinarySequentialPayloadDecoder.read bits with
    | none => 0
    | some dim =>
        BinarySequentialRationalFrame.work model primitive dim.2+
          match BinarySequentialRationalFrame.read dim.2 with
          | none => 0
          | some first =>
              BinarySequentialRationalFrame.work model primitive first.2+
                match BinarySequentialRationalFrame.read first.2 with
                | none => 0
                | some second => listWork model primitive dim.1 second.2

def gamePrice (model : RationalCostModel) (c count length : ℕ) : ℕ :=
  BinarySequentialNatReadCost.price c length+
    (count+3)*(BinarySequentialRationalFrame.price model c length+BinarySequentialPayloadCost.scalarBound c count+9)+16

theorem game_work_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (bits : List Bool) (count : ℕ) (tail : List Bool)
    (hDim : BinarySequentialPayloadDecoder.read bits = some (count,tail)) :
    gameWork model primitive bits ≤ gamePrice model c count bits.length := by
  let P := BinarySequentialRationalFrame.price model c bits.length
  let S := BinarySequentialPayloadCost.scalarBound c count
  have hn := BinarySequentialNatReadCost.work_bound primitive c hPrimitive bits
  have ht : tail.length ≤ bits.length := by
    have hh := BinarySequentialNatReadCost.read_width_consumed bits count tail hDim
    omega
  have ha : BinarySequentialRationalFrame.work model primitive tail ≤ P :=
    (BinarySequentialRationalFrame.work_bound model primitive c hPrimitive tail).trans
      (BinarySequentialRationalFrame.price_mono model c ht)
  unfold gameWork
  rw [hDim]
  dsimp only
  cases hA : BinarySequentialRationalFrame.read tail with
  | none =>
      simp only
      unfold gamePrice
      change _ ≤ BinarySequentialNatReadCost.price c bits.length+(count+3)*(P+S+9)+16
      nlinarith only [hn,ha]
  | some first =>
      rcases first with ⟨a,rest⟩
      have hr : rest.length ≤ bits.length := by
        have hh := BinarySequentialRationalFrame.read_width_consumed tail a rest hA
        omega
      have hb : BinarySequentialRationalFrame.work model primitive rest ≤ P :=
        (BinarySequentialRationalFrame.work_bound model primitive c hPrimitive rest).trans
          (BinarySequentialRationalFrame.price_mono model c hr)
      simp only
      cases hB : BinarySequentialRationalFrame.read rest with
      | none =>
          simp only
          unfold gamePrice
          change _ ≤ BinarySequentialNatReadCost.price c bits.length+(count+3)*(P+S+9)+16
          nlinarith only [hn,ha,hb]
      | some second =>
          rcases second with ⟨b,remaining⟩
          have hs : remaining.length ≤ bits.length := by
            have hh := BinarySequentialRationalFrame.read_width_consumed rest b remaining hB
            omega
          have hl := (list_work_bound model primitive c hPrimitive count remaining).trans
            (Nat.mul_le_mul_left (count+1) (Nat.add_le_add_right
              (Nat.add_le_add_right (BinarySequentialRationalFrame.price_mono model c hs) S) 9))
          simp only
          unfold gamePrice
          change _ ≤ BinarySequentialNatReadCost.price c bits.length+(count+3)*(P+S+9)+16
          change listWork model primitive count remaining ≤ (count+1)*(P+S+9) at hl
          nlinarith only [hn,ha,hb,hl]

def countGateWork (primitive : ℕ → ℕ) (data : BinaryGameWords) : ℕ :=
  listLengthBitWork primitive 0 data.values+binaryWordWidth data.values.length+binaryWordWidth data.count+
    primitive (max (binaryWordWidth data.values.length) (binaryWordWidth data.count))+1

def checkedWork (model : RationalCostModel) (primitive : ℕ → ℕ) (bits : List Bool) : ℕ :=
  gameWork model primitive bits+16+
    match game bits with
    | none => 0
    | some parsed =>
        countGateWork primitive parsed.1+
          if h : parsed.1.values.length = parsed.1.count then
            RationalPRGCheckCode.selectedBitWork model (parsed.1.valueTable h).read parsed.1.a parsed.1.b
          else 0

def countGatePrice (c count : ℕ) : ℕ :=
  (count+1)*((c+2)*binaryWordWidth (count+1)+1)+(c+2)*binaryWordWidth count+1

theorem countGatePrice_mono (c : ℕ) : Monotone (countGatePrice c) := by
  intro a b hab
  exact Nat.add_le_add_right (Nat.add_le_add
    (Nat.mul_le_mul (Nat.add_le_add_right hab 1)
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ (binaryWordWidth_mono (Nat.add_le_add_right hab 1))) 1))
    (Nat.mul_le_mul_left _ (binaryWordWidth_mono hab))) 1

theorem count_gate_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (data : BinaryGameWords) (hCount : data.values.length = data.count) :
    countGateWork primitive data ≤ countGatePrice c data.count := by
  have hl := listLengthBitWork_bound primitive c hPrimitive 0 data.values
  simp only [Nat.zero_add,hCount] at hl
  have hp := hPrimitive (binaryWordWidth data.count)
  simp only [countGateWork,hCount,max_self,countGatePrice]
  nlinarith only [hl,hp]

def checkedPrice (model : RationalCostModel) (c count length : ℕ) : ℕ :=
  gamePrice model c count length+(19*count+23)*model.rat (32*(9*length+3))+countGatePrice c count+16

theorem checked_work_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (bits : List Bool) (data : BinaryGameWords) (suffix : List Bool)
    (hGame : game bits = some (data,suffix)) : checkedWork model primitive bits ≤ checkedPrice model c data.count bits.length := by
  have hOld : RationalPRGBinaryInput.read bits = some (data,suffix) := by rwa [game_refines] at hGame
  obtain ⟨tail,hHeader⟩ := (BinaryDecodedAggregateSize.game_width_consumed bits data suffix hOld).2
  have hDim : BinarySequentialPayloadDecoder.read bits = some (data.count,tail) := by
    rw [BinarySequentialPayloadDecoder.read_refines]
    exact hHeader
  have hg := game_work_bound model primitive c hPrimitive bits data.count tail hDim
  have hCount := (RationalPRGBinaryInput.read_wordWidths bits data suffix hOld).2.1
  have hc := BinaryDecodedAggregateSize.parsed_check_bound model bits data suffix hOld hCount
  have hGate := count_gate_bound primitive c hPrimitive data hCount
  simpa only [checkedWork,hGame,dite_eq_left hCount,checkedPrice,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
    using Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hg hGate) hc) 16

theorem count_width_add_two (count : ℕ) : binaryWordWidth (count+2) ≤ binaryWordWidth count+2 := by
  apply binaryWordWidth_le_of_lt_pow (by omega : 0 < binaryWordWidth count+2)
  have hc := lt_pow_binaryWordWidth count
  have hp := Nat.two_pow_pos (binaryWordWidth count)
  rw [pow_add]
  norm_num only [Nat.reducePow]
  nlinarith only [hc,hp]

def frameGamePrice (model : RationalCostModel) (c length : ℕ) : ℕ :=
  BinarySequentialNatReadCost.price c length+
    (length+3)*(BinarySequentialRationalFrame.price model c length+(12+4*c)*(length+2)+16+9)+16

theorem game_work_frame_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (bits : List Bool) :
    gameWork model primitive bits ≤ frameGamePrice model c bits.length := by
  let P := BinarySequentialRationalFrame.price model c bits.length
  let S := (12+4*c)*(bits.length+2)+16
  have hn := BinarySequentialNatReadCost.work_bound primitive c hPrimitive bits
  unfold gameWork
  cases hDim : BinarySequentialPayloadDecoder.read bits with
  | none =>
      dsimp only
      unfold frameGamePrice
      omega
  | some dim =>
      rcases dim with ⟨count,tail⟩
      have hSize := BinarySequentialNatReadCost.read_width_consumed bits count tail hDim
      have ht : tail.length ≤ bits.length := by omega
      have hScalar : BinarySequentialPayloadCost.scalarBound c count ≤ S := by
        have hw := count_width_add_two count
        have hm := Nat.mul_le_mul_left (12+4*c) (show binaryWordWidth (count+2) ≤ bits.length+2 by omega)
        unfold BinarySequentialPayloadCost.scalarBound
        dsimp [S]
        omega
      have ha : BinarySequentialRationalFrame.work model primitive tail ≤ P :=
        (BinarySequentialRationalFrame.work_bound model primitive c hPrimitive tail).trans
          (BinarySequentialRationalFrame.price_mono model c ht)
      dsimp only
      cases hA : BinarySequentialRationalFrame.read tail with
      | none =>
          simp only
          unfold frameGamePrice
          change _ ≤ BinarySequentialNatReadCost.price c bits.length+(bits.length+3)*(P+S+9)+16
          nlinarith only [hn,ha]
      | some first =>
          rcases first with ⟨a,rest⟩
          have hr : rest.length ≤ bits.length := by
            have hh := BinarySequentialRationalFrame.read_width_consumed tail a rest hA
            omega
          have hb : BinarySequentialRationalFrame.work model primitive rest ≤ P :=
            (BinarySequentialRationalFrame.work_bound model primitive c hPrimitive rest).trans
              (BinarySequentialRationalFrame.price_mono model c hr)
          simp only
          cases hB : BinarySequentialRationalFrame.read rest with
          | none =>
              simp only
              unfold frameGamePrice
              change _ ≤ BinarySequentialNatReadCost.price c bits.length+(bits.length+3)*(P+S+9)+16
              nlinarith only [hn,ha,hb]
          | some second =>
              rcases second with ⟨b,remaining⟩
              have hs : remaining.length ≤ bits.length := by
                have hh := BinarySequentialRationalFrame.read_width_consumed rest b remaining hB
                omega
              have hl := list_work_frame_bound model primitive c hPrimitive count count (Nat.le_refl _) remaining
              have hm := Nat.mul_le_mul (Nat.add_le_add_right hs 1)
                (Nat.add_le_add_right (Nat.add_le_add (BinarySequentialRationalFrame.price_mono model c hs) hScalar) 9)
              simp only
              unfold frameGamePrice
              change _ ≤ BinarySequentialNatReadCost.price c bits.length+(bits.length+3)*(P+S+9)+16
              change (remaining.length+1)*(BinarySequentialRationalFrame.price model c remaining.length+
                BinarySequentialPayloadCost.scalarBound c count+9) ≤ (bits.length+1)*(P+S+9) at hm
              nlinarith only [hn,ha,hb,hl,hm]

def frameCheckedPrice (model : RationalCostModel) (c length : ℕ) : ℕ :=
  frameGamePrice model c length+(19*length+23)*model.rat (32*(9*length+3))+countGatePrice c length+16

theorem checked_work_frame_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (bits : List Bool) :
    checkedWork model primitive bits ≤ frameCheckedPrice model c bits.length := by
  have hg := game_work_frame_bound model primitive c hPrimitive bits
  unfold checkedWork
  cases hGame : game bits with
  | none => dsimp only; unfold frameCheckedPrice; omega
  | some parsed =>
      rcases parsed with ⟨data,suffix⟩
      have hOld : RationalPRGBinaryInput.read bits = some (data,suffix) := by rwa [game_refines] at hGame
      have hSizes := RationalPRGBinaryInput.read_wordWidths bits data suffix hOld
      have hc := BinaryDecodedAggregateSize.parsed_check_bound model bits data suffix hOld hSizes.2.1
      have hm := Nat.mul_le_mul_right (model.rat (32*(9*bits.length+3)))
        (show 19*data.count+23 ≤ 19*bits.length+23 by omega)
      have hGate := count_gate_bound primitive c hPrimitive data hSizes.2.1
      have hGate' := hGate.trans (countGatePrice_mono c hSizes.1)
      simp only [dite_eq_left hSizes.2.1]
      unfold frameCheckedPrice
      omega

theorem encoded_contract {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (suffix : List Bool) :
    let frame := RationalPRGBinaryInput.encode i++suffix
    checked frame = some (⟨n,i⟩,suffix) ∧ checkedWork model primitive frame ≤ checkedPrice model c n frame.length := by
  have hGame : game (RationalPRGBinaryInput.encode i++suffix) = some (⟨n,i.a,i.b,List.ofFn i.values⟩,suffix) := by
    rw [game_refines]
    exact RationalPRGBinaryInput.read_encode_append i suffix
  have hc := checked_work_bound model primitive c hPrimitive _ _ suffix hGame
  exact ⟨by rw [checked_refines]; exact RationalPRGBinaryInput.readChecked_encode_append i suffix,hc⟩

end Blotto.BinarySequentialGameFrame
