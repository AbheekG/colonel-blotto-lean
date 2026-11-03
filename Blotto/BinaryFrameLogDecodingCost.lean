import Blotto.RationalPRGInputDecodingCost

/-! Sharper bounds for the existing numeric frame-reader source ledger.
The scanned counters have logarithmic width and the balanced decoder pays
one payload-length sum per level. All malformed branches remain covered.
Payload-to-array copying and other metadata/native costs remain separate. -/
namespace Blotto.BinaryFrameLogDecodingCost
set_option autoImplicit false

theorem scan_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (count : ℕ) (frame : List Bool) (capacity : ℕ) (hCap : count+frame.length+1 ≤ capacity) :
    BinaryNatFrame.scanBitWork primitive count frame ≤
      (frame.length+1)*((2+c)*binaryWordWidth capacity+1) := by
  induction frame generalizing count with
  | nil => simp only [BinaryNatFrame.scanBitWork,List.length_nil,Nat.zero_add,Nat.one_mul]; omega
  | cons bit rest ih =>
      cases bit with
      | false =>
          have hc := binaryWordWidth_mono (show count ≤ capacity by simp only [List.length_cons] at hCap; omega)
          have hn := binaryWordWidth_mono (show count+1 ≤ capacity by simp only [List.length_cons] at hCap; omega)
          have hp := (hPrimitive (binaryWordWidth (count+1))).trans (Nat.mul_le_mul_left c hn)
          have hr := ih (count+1) (by simp only [List.length_cons] at hCap; omega)
          simp only [BinaryNatFrame.scanBitWork,List.length_cons]
          nlinarith only [hc,hn,hp,hr]
      | true =>
          simp only [BinaryNatFrame.scanBitWork,List.length_cons]
          exact Nat.succ_le_iff.mpr (Nat.mul_pos (by omega) (by omega))

def natPrice (c length : ℕ) : ℕ := (4*c+16)*(length+2)*binaryWordWidth (length+2)

theorem natPrice_mono (c : ℕ) : Monotone (natPrice c) := by
  intro a b hab
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right hab 2))
    (binaryWordWidth_mono (Nat.add_le_add_right hab 2))

theorem nat_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (frame : List Bool) :
    BinaryNatFrame.decodingBitWork primitive frame ≤ natPrice c frame.length := by
  let L := frame.length+2
  let W := binaryWordWidth L
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hW : 1 ≤ W := binaryWordWidth_pos L
  have hLW : L ≤ L*W := by nlinarith only [hW]
  have hs := scan_bound primitive c hPrimitive 0 frame L (by dsimp [L]; omega)
  have hs' : BinaryNatFrame.scanBitWork primitive 0 frame ≤ (c+3)*L*W := by
    have hh := Nat.mul_le_mul (show frame.length+1 ≤ L by dsimp [L]; omega)
      (show (2+c)*W+1 ≤ (c+3)*W by nlinarith only [hW])
    nlinarith only [hs,hh]
  unfold BinaryNatFrame.decodingBitWork
  cases hRead : BinaryNatFrame.scanWidth 0 frame with
  | none =>
      simp only [Nat.add_zero]
      change _ ≤ (4*c+16)*L*W
      nlinarith only [hs']
  | some parsed =>
      rcases parsed with ⟨width,rest⟩
      have hLen := BinaryNatFrame.scanWidth_length 0 frame width rest hRead
      have hWidth : width ≤ L := by dsimp [L]; omega
      have hRest : rest.length ≤ L := by dsimp [L]; omega
      have hWords : max (binaryWordWidth width) (binaryWordWidth rest.length) ≤ W :=
        max_le (binaryWordWidth_mono hWidth) (binaryWordWidth_mono hRest)
      have hp := (hPrimitive _).trans (Nat.mul_le_mul_left c hWords)
      have hp' : primitive (max (binaryWordWidth width) (binaryWordWidth rest.length)) ≤ c*L*W := by
        have hh := Nat.mul_le_mul_left (c*W) hL
        nlinarith only [hp,hh]
      have hd := BinaryPayload.balancedBitWork_word_bound primitive c hPrimitive (rest.take width).toArray 0 width
      have hm := Nat.mul_le_mul_left (4+2*c) (Nat.mul_le_mul hWidth (binaryWordWidth_mono hWidth))
      have hd' : BinaryPayload.balancedBitWork primitive (rest.take width).toArray 0 width ≤ L+(4+2*c)*L*W := by
        nlinarith only [hd,hm,hWidth]
      dsimp only
      split
      · change _ ≤ (4*c+16)*L*W
        nlinarith only [hs',hRest,hWidth,hp',hd',hLW]
      · change _ ≤ (4*c+16)*L*W
        nlinarith only [hs',hRest,hp',hLW]

def ratPrice (model : RationalCostModel) (c length : ℕ) : ℕ :=
  (10*c+40)*(length+2)*binaryWordWidth (length+2)+5*model.rat (4*length+13)

theorem ratPrice_mono (model : RationalCostModel) (c : ℕ) : Monotone (ratPrice model c) := by
  intro a b hab
  unfold ratPrice
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right hab 2))
      (binaryWordWidth_mono (Nat.add_le_add_right hab 2)))
    (Nat.mul_le_mul_left 5 (model.monotone (by omega)))

theorem rat_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (frame : List Bool) :
    BinaryRatFrame.decodingBitWork model primitive frame ≤ ratPrice model c frame.length := by
  cases frame with
  | nil =>
      have hw := binaryWordWidth_pos 2
      simp only [BinaryRatFrame.decodingBitWork,List.length_nil,ratPrice]
      nlinarith
  | cons negative bits =>
      let F := (negative::bits).length
      let Q := natPrice c F
      let P := model.rat (4*F+13)
      have hFirst : BinaryNatFrame.decodingBitWork primitive bits ≤ Q :=
        (nat_bound primitive c hPrimitive bits).trans (natPrice_mono c (by dsimp [F]; simp))
      have hExtra : 1+c*(F+1) ≤ (c+1)*(F+2)*binaryWordWidth (F+2) := by
        have hh := Nat.mul_le_mul_left ((c+1)*(F+2)) (show 1 ≤ binaryWordWidth (F+2) from binaryWordWidth_pos _)
        nlinarith only [hh]
      have hMajor : 2*Q+(c+1)*(F+2)*binaryWordWidth (F+2) ≤
          (10*c+40)*(F+2)*binaryWordWidth (F+2) := by dsimp [Q,natPrice]; nlinarith
      simp only [BinaryRatFrame.decodingBitWork]
      cases hOne : BinaryNatFrame.read bits with
      | none =>
          simp only
          change _ ≤ (10*c+40)*(F+2)*binaryWordWidth (F+2)+5*P
          omega
      | some first =>
          rcases first with ⟨magnitude,tail⟩
          have hTail := BinaryNatFrame.read_suffix_length bits magnitude tail hOne
          have hM := BinaryNatFrame.read_value_wordWidth bits magnitude tail hOne
          have hSecond : BinaryNatFrame.decodingBitWork primitive tail ≤ Q :=
            (nat_bound primitive c hPrimitive tail).trans (natPrice_mono c (by dsimp [F]; omega))
          simp only
          cases hTwo : BinaryNatFrame.read tail with
          | none =>
              simp only
              change _ ≤ (10*c+40)*(F+2)*binaryWordWidth (F+2)+5*P
              omega
          | some second =>
              rcases second with ⟨denominator,suffix⟩
              have hD := BinaryNatFrame.read_value_wordWidth tail denominator suffix hTwo
              have hZero := (hPrimitive (binaryWordWidth denominator)).trans
                (Nat.mul_le_mul_left c (show binaryWordWidth denominator ≤ F+1 by dsimp [F]; omega))
              have hSigned : rationalWordWidth (BinaryRatFrame.signedValue negative magnitude) ≤ F+3 := by
                rw [BinaryRatFrame.signedValue_wordWidth]
                dsimp [F]
                omega
              have hDen : rationalWordWidth (denominator : ℚ) ≤ F+3 := by
                have hh := BinaryRatFrame.signedValue_wordWidth false denominator
                simp only [BinaryRatFrame.signedValue,Bool.false_eq_true,ite_false] at hh
                rw [hh]
                dsimp [F]
                omega
              have hRat := model.monotone (show RationalExpression.pairWidth
                  (BinaryRatFrame.signedValue negative magnitude) (denominator : ℚ) ≤ 4*F+13 by
                    unfold RationalExpression.pairWidth
                    omega)
              have hValue := rationalWordWidth_of_height
                ((rationalHeight_of_wordWidth (BinaryRatFrame.signedValue negative magnitude)).div
                  (rationalHeight_of_wordWidth (denominator : ℚ)))
              have hOut : rationalWordWidth (BinaryRatFrame.signedValue negative magnitude / denominator) ≤ P :=
                (hValue.trans (by omega)).trans (model.word_le _)
              simp only
              change _ ≤ (10*c+40)*(F+2)*binaryWordWidth (F+2)+5*P
              change model.rat (RationalExpression.pairWidth _ _) ≤ P at hRat
              split <;> omega

theorem list_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (count : ℕ) (frame : List Bool) :
    BinaryRatListFrame.decodingBitWork model primitive count frame ≤
      (count+1)*(ratPrice model c frame.length+1) := by
  induction count generalizing frame with
  | zero => simp only [BinaryRatListFrame.decodingBitWork,Nat.zero_add,Nat.one_mul]; omega
  | succ count ih =>
      have hh := rat_bound model primitive c hPrimitive frame
      unfold BinaryRatListFrame.decodingBitWork
      cases hRead : BinaryRatFrame.read frame with
      | none => simp only; nlinarith
      | some parsed =>
          rcases parsed with ⟨q,tail⟩
          have hTail := BinaryRatFrame.read_suffix_length frame q tail hRead
          have hr := (ih tail).trans (Nat.mul_le_mul_left (count+1)
            (Nat.add_le_add_right (ratPrice_mono model c hTail) 1))
          simp only
          nlinarith

def gamePrice (model : RationalCostModel) (c count length : ℕ) : ℕ :=
  natPrice c length+(count+3)*(ratPrice model c length+1)

theorem game_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (frame : List Bool) (count : ℕ) (tail : List Bool)
    (hRead : BinaryNatFrame.read frame = some (count,tail)) :
    RationalPRGBinaryInput.decodingBitWork model primitive frame ≤ gamePrice model c count frame.length := by
  let P := ratPrice model c frame.length
  have hn := nat_bound primitive c hPrimitive frame
  have ht := BinaryNatFrame.read_suffix_length frame count tail hRead
  have ha : BinaryRatFrame.decodingBitWork model primitive tail ≤ P :=
    (rat_bound model primitive c hPrimitive tail).trans (ratPrice_mono model c ht)
  unfold RationalPRGBinaryInput.decodingBitWork
  rw [hRead]
  dsimp only
  cases hFirst : BinaryRatFrame.read tail with
  | none =>
      simp only
      unfold gamePrice
      change _ ≤ natPrice c frame.length+(count+3)*(P+1)
      nlinarith only [hn,ha]
  | some first =>
      rcases first with ⟨a,rest⟩
      have hr := (BinaryRatFrame.read_suffix_length tail a rest hFirst).trans ht
      have hb : BinaryRatFrame.decodingBitWork model primitive rest ≤ P :=
        (rat_bound model primitive c hPrimitive rest).trans (ratPrice_mono model c hr)
      simp only
      cases hSecond : BinaryRatFrame.read rest with
      | none =>
          simp only
          unfold gamePrice
          change _ ≤ natPrice c frame.length+(count+3)*(P+1)
          nlinarith only [hn,ha,hb]
      | some second =>
          rcases second with ⟨b,remaining⟩
          have hs := (BinaryRatFrame.read_suffix_length rest b remaining hSecond).trans hr
          have hl := (list_bound model primitive c hPrimitive count remaining).trans
            (Nat.mul_le_mul_left (count+1) (Nat.add_le_add_right (ratPrice_mono model c hs) 1))
          simp only
          unfold gamePrice
          change _ ≤ natPrice c frame.length+(count+3)*(P+1)
          change BinaryRatListFrame.decodingBitWork model primitive count remaining ≤ (count+1)*(P+1) at hl
          nlinarith only [hn,ha,hb,hl]

theorem game_header_failure (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (frame : List Bool) (hRead : BinaryNatFrame.read frame = none) :
    RationalPRGBinaryInput.decodingBitWork model primitive frame ≤ natPrice c frame.length := by
  simpa only [RationalPRGBinaryInput.decodingBitWork,hRead,Nat.add_zero] using nat_bound primitive c hPrimitive frame

end Blotto.BinaryFrameLogDecodingCost
