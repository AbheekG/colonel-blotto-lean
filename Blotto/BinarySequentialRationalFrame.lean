import Blotto.BinarySequentialNatReadCost

/-! Actual rational-frame parsing uses the sequential natural reader twice,
passing the first returned tail to the second call. The sign, zero-denominator
gate, reduced rational and suffix equal the old full parsed result.
Arithmetic prices remain relative to the declared Rat profile; this is not a
cost theorem for Lean's rational library or native memory management. -/
namespace Blotto.BinarySequentialRationalFrame
set_option autoImplicit false

def read : List Bool → Option (ℚ × List Bool)
  | [] => none
  | negative::bits =>
      (BinarySequentialPayloadDecoder.read bits).bind (fun first =>
        (BinarySequentialPayloadDecoder.read first.2).bind (fun second =>
          if second.1 = 0 then none else some (BinaryRatFrame.signedValue negative first.1/second.1,second.2)))

theorem read_refines (frame : List Bool) : read frame = BinaryRatFrame.read frame := by
  cases frame <;> simp only [read,BinaryRatFrame.read,BinarySequentialPayloadDecoder.read_refines]

def work (model : RationalCostModel) (primitive : ℕ → ℕ) : List Bool → ℕ
  | [] => 1
  | negative::bits =>
      1+BinarySequentialNatReadCost.work primitive bits+
        match BinarySequentialPayloadDecoder.read bits with
        | none => 0
        | some first =>
            BinarySequentialNatReadCost.work primitive first.2+
              match BinarySequentialPayloadDecoder.read first.2 with
              | none => 0
              | some second =>
                  primitive (binaryWordWidth second.1)+if second.1 = 0 then 0 else
                    4*model.rat (RationalExpression.pairWidth (BinaryRatFrame.signedValue negative first.1) (second.1 : ℚ))+
                      rationalWordWidth (BinaryRatFrame.signedValue negative first.1/second.1)

def price (model : RationalCostModel) (c length : ℕ) : ℕ :=
  (256+64*c)*(length+2)*binaryWordWidth (length+2)+5*model.rat (4*length+13)

theorem price_mono (model : RationalCostModel) (c : ℕ) : Monotone (price model c) := by
  intro a b hab
  unfold price
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right hab 2))
      (binaryWordWidth_mono (Nat.add_le_add_right hab 2)))
    (Nat.mul_le_mul_left 5 (model.monotone (by omega)))

theorem work_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (frame : List Bool) : work model primitive frame ≤ price model c frame.length := by
  cases frame with
  | nil =>
      have hw := binaryWordWidth_pos 2
      simp only [work,List.length_nil,price]
      nlinarith
  | cons negative bits =>
      let F := (negative::bits).length
      let Q := BinarySequentialNatReadCost.price c F
      let P := model.rat (4*F+13)
      have hFirst : BinarySequentialNatReadCost.work primitive bits ≤ Q :=
        (BinarySequentialNatReadCost.work_bound primitive c hPrimitive bits).trans
          (BinarySequentialNatReadCost.price_mono c (by dsimp [F]; simp))
      have hExtra : 1+c*(F+1) ≤ (c+1)*(F+2)*binaryWordWidth (F+2) := by
        have hh := Nat.mul_le_mul_left ((c+1)*(F+2)) (show 1 ≤ binaryWordWidth (F+2) from binaryWordWidth_pos _)
        nlinarith only [hh]
      have hMajor : 2*Q+(c+1)*(F+2)*binaryWordWidth (F+2) ≤
          (256+64*c)*(F+2)*binaryWordWidth (F+2) := by dsimp [Q,BinarySequentialNatReadCost.price]; nlinarith
      simp only [work]
      cases hOne : BinarySequentialPayloadDecoder.read bits with
      | none =>
          simp only
          change _ ≤ (256+64*c)*(F+2)*binaryWordWidth (F+2)+5*P
          omega
      | some first =>
          rcases first with ⟨magnitude,tail⟩
          have hM := BinarySequentialNatReadCost.read_width_consumed bits magnitude tail hOne
          have hTail : tail.length ≤ bits.length := by omega
          have hSecond : BinarySequentialNatReadCost.work primitive tail ≤ Q :=
            (BinarySequentialNatReadCost.work_bound primitive c hPrimitive tail).trans
              (BinarySequentialNatReadCost.price_mono c (by dsimp [F]; omega))
          simp only
          cases hTwo : BinarySequentialPayloadDecoder.read tail with
          | none =>
              simp only
              change _ ≤ (256+64*c)*(F+2)*binaryWordWidth (F+2)+5*P
              omega
          | some second =>
              rcases second with ⟨denominator,suffix⟩
              have hD := BinarySequentialNatReadCost.read_width_consumed tail denominator suffix hTwo
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
              have hOut : rationalWordWidth (BinaryRatFrame.signedValue negative magnitude/denominator) ≤ P :=
                (hValue.trans (by omega)).trans (model.word_le _)
              simp only
              change _ ≤ (256+64*c)*(F+2)*binaryWordWidth (F+2)+5*P
              change model.rat (RationalExpression.pairWidth _ _) ≤ P at hRat
              split <;> omega

theorem read_contract (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (frame : List Bool) :
    read frame = BinaryRatFrame.read frame ∧ work model primitive frame ≤ price model c frame.length :=
  ⟨read_refines frame,work_bound model primitive c hPrimitive frame⟩

theorem read_width_consumed (frame : List Bool) (q : ℚ) (suffix : List Bool)
    (h : read frame = some (q,suffix)) : rationalWordWidth q+9*suffix.length ≤ 9*frame.length := by
  rw [read_refines] at h
  exact BinaryDecodedAggregateSize.rat_width_consumed frame q suffix h

theorem read_encode (q : ℚ) (suffix : List Bool) : read (BinaryRatFrame.encode q++suffix) = some (q,suffix) := by
  rw [read_refines,BinaryRatFrame.read_encode_append]

end Blotto.BinarySequentialRationalFrame
