import Blotto.BinaryFrameLogDecodingCost
import Blotto.RationalAggregateRecognitionCost
import Blotto.RationalPRGParsedCheckCost

/-! Successful parsing charges aggregate decoded word widths to consumed
frame bits, including nonminimal widths and signed zero. This joins the
logarithmic parser price to actual promise checking without an n-fold
inflation of the input width. Metadata and payload-buffer costs stay separate. -/
namespace Blotto.BinaryDecodedAggregateSize
open RationalAggregateRecognitionCost
open scoped BigOperators
set_option autoImplicit false

theorem nat_width_consumed (frame : List Bool) (n : ℕ) (suffix : List Bool)
    (h : BinaryNatFrame.read frame = some (n,suffix)) :
    binaryWordWidth n+suffix.length ≤ frame.length := by
  unfold BinaryNatFrame.read at h
  cases hs : BinaryNatFrame.scanWidth 0 frame with
  | none => rw [hs,Option.bind_none] at h; cases h
  | some pair =>
      rcases pair with ⟨width,rest⟩
      rw [hs,Option.bind_some] at h
      split at h
      · cases Option.some.inj h
        have hLength := BinaryNatFrame.scanWidth_length 0 frame width rest hs
        have hb := BinaryPayload.balancedValue_bounds (rest.take width).toArray 0 (rest.take width).length
        have hw : binaryWordWidth (BinaryPayload.decode (rest.take width)) ≤ width+1 := by
          apply binaryWordWidth_le_of_lt_pow (by omega : 0 < width+1)
          exact hb.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by
            simp only [List.length_take]
            omega))
        simp only [List.length_drop] at *
        omega
      · cases h

theorem rat_width_consumed (frame : List Bool) (q : ℚ) (suffix : List Bool)
    (h : BinaryRatFrame.read frame = some (q,suffix)) :
    rationalWordWidth q+9*suffix.length ≤ 9*frame.length := by
  cases frame with
  | nil => cases h
  | cons negative bits =>
      simp only [BinaryRatFrame.read] at h
      cases hOne : BinaryNatFrame.read bits with
      | none => rw [hOne,Option.bind_none] at h; cases h
      | some first =>
          rcases first with ⟨magnitude,tail⟩
          rw [hOne,Option.bind_some] at h
          cases hTwo : BinaryNatFrame.read tail with
          | none => rw [hTwo,Option.bind_none] at h; cases h
          | some second =>
              rcases second with ⟨denominator,rest⟩
              rw [hTwo,Option.bind_some] at h
              split at h
              · cases h
              · cases Option.some.inj h
                have hm := nat_width_consumed bits magnitude tail hOne
                have hd := nat_width_consumed tail denominator rest hTwo
                have hOut := rationalWordWidth_of_height
                  ((rationalHeight_of_wordWidth (BinaryRatFrame.signedValue negative magnitude)).div
                    (rationalHeight_of_wordWidth (denominator : ℚ)))
                have hDen := BinaryRatFrame.signedValue_wordWidth false denominator
                simp only [BinaryRatFrame.signedValue,Bool.false_eq_true,ite_false] at hDen
                rw [BinaryRatFrame.signedValue_wordWidth,hDen] at hOut
                simp only [List.length_cons]
                omega

theorem list_width_consumed (count : ℕ) (frame : List Bool) (values : List ℚ) (suffix : List Bool)
    (h : BinaryRatListFrame.read count frame = some (values,suffix)) :
    totalWidth values+9*suffix.length ≤ 9*frame.length := by
  induction count generalizing frame values suffix with
  | zero =>
      cases Option.some.inj h
      simp only [totalWidth,List.map_nil,List.sum_nil,Nat.zero_add,le_refl]
  | succ count ih =>
      simp only [BinaryRatListFrame.read] at h
      cases hFirst : BinaryRatFrame.read frame with
      | none => rw [hFirst,Option.bind_none] at h; cases h
      | some first =>
          rcases first with ⟨q,tail⟩
          rw [hFirst,Option.bind_some] at h
          cases hRest : BinaryRatListFrame.read count tail with
          | none => rw [hRest,Option.map_none] at h; cases h
          | some rest =>
              rcases rest with ⟨row,remaining⟩
              rw [hRest,Option.map_some] at h
              cases Option.some.inj h
              have hh := rat_width_consumed frame q tail hFirst
              have ht := ih tail row remaining hRest
              simp only [totalWidth,List.map_cons,List.sum_cons] at *
              omega

theorem game_width_consumed (frame : List Bool) (data : BinaryGameWords) (suffix : List Bool)
    (h : RationalPRGBinaryInput.read frame = some (data,suffix)) :
    rationalWordWidth data.a+rationalWordWidth data.b+totalWidth data.values+9*suffix.length ≤ 9*frame.length ∧
      ∃ tail, BinaryNatFrame.read frame = some (data.count,tail) := by
  unfold RationalPRGBinaryInput.read at h
  cases hDim : BinaryNatFrame.read frame with
  | none => rw [hDim,Option.bind_none] at h; cases h
  | some dim =>
      rcases dim with ⟨count,tail⟩
      rw [hDim,Option.bind_some] at h
      cases hA : BinaryRatFrame.read tail with
      | none => rw [hA,Option.bind_none] at h; cases h
      | some first =>
          rcases first with ⟨a,rest⟩
          rw [hA,Option.bind_some] at h
          cases hB : BinaryRatFrame.read rest with
          | none => rw [hB,Option.bind_none] at h; cases h
          | some second =>
              rcases second with ⟨b,remaining⟩
              rw [hB,Option.bind_some] at h
              cases hRow : BinaryRatListFrame.read count remaining with
              | none => rw [hRow,Option.map_none] at h; cases h
              | some row =>
                  rcases row with ⟨values,last⟩
                  rw [hRow,Option.map_some] at h
                  cases Option.some.inj h
                  have ht := BinaryNatFrame.read_suffix_length frame count tail hDim
                  have ha := rat_width_consumed tail a rest hA
                  have hb := rat_width_consumed rest b remaining hB
                  have hv := list_width_consumed count remaining values last hRow
                  exact ⟨by dsimp only; omega,⟨tail,rfl⟩⟩

theorem table_list (data : BinaryGameWords) (hCount : data.values.length = data.count) :
    List.ofFn (data.valueTable hCount).read = data.values := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,hCount]
  · intro j hj hk
    simp only [List.getElem_ofFn,BinaryGameWords.valueTable,FixedArrayTable.read,List.getElem_toArray]

theorem parsed_input_width (frame : List Bool) (data : BinaryGameWords) (suffix : List Bool)
    (h : RationalPRGBinaryInput.read frame = some (data,suffix)) (hCount : data.values.length = data.count) :
    RationalPRGCheckCode.inputWordWidth (data.valueTable hCount).read data.a data.b ≤ 9*frame.length := by
  have hw := (game_width_consumed frame data suffix h).1
  have hv : (∑ j, rationalWordWidth ((data.valueTable hCount).read j)) = totalWidth data.values := by
    rw [← table_list data hCount]
    simp only [totalWidth,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  unfold RationalPRGCheckCode.inputWordWidth
  omega

theorem parsed_check_bound (model : RationalCostModel) (frame : List Bool) (data : BinaryGameWords)
    (suffix : List Bool) (h : RationalPRGBinaryInput.read frame = some (data,suffix))
    (hCount : data.values.length = data.count) :
    RationalPRGCheckCode.selectedBitWork model (data.valueTable hCount).read data.a data.b ≤
      (19*data.count+23)*model.rat (32*(9*frame.length+3)) :=
  (selected_bound model (data.valueTable hCount).read data.a data.b).trans
    (Nat.mul_le_mul_left _ (model.monotone (by have hw := parsed_input_width frame data suffix h hCount; omega)))

theorem checked_decoding_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (frame : List Bool) (data : BinaryGameWords) (suffix : List Bool)
    (h : RationalPRGBinaryInput.read frame = some (data,suffix)) :
    RationalPRGBinaryInput.checkedDecodingBitWork model primitive frame ≤
      BinaryFrameLogDecodingCost.gamePrice model c data.count frame.length+
        (19*data.count+23)*model.rat (32*(9*frame.length+3)) := by
  obtain ⟨tail,hHeader⟩ := (game_width_consumed frame data suffix h).2
  have hCount := (RationalPRGBinaryInput.read_wordWidths frame data suffix h).2.1
  have hd := BinaryFrameLogDecodingCost.game_bound model primitive c hPrimitive frame data.count tail hHeader
  have hc := parsed_check_bound model frame data suffix h hCount
  simpa only [RationalPRGBinaryInput.checkedDecodingBitWork,h,dite_eq_left hCount] using Nat.add_le_add hd hc

theorem encoded_checked_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (suffix : List Bool) :
    let F := (RationalPRGBinaryInput.encode i++suffix).length
    RationalPRGBinaryInput.checkedDecodingBitWork model primitive (RationalPRGBinaryInput.encode i++suffix) ≤
      BinaryFrameLogDecodingCost.gamePrice model c n F+(19*n+23)*model.rat (32*(9*F+3)) :=
  checked_decoding_bound model primitive c hPrimitive _ _ suffix
    (RationalPRGBinaryInput.read_encode_append i suffix)

theorem encoded_checked_contract {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (suffix : List Bool) :
    let F := (RationalPRGBinaryInput.encode i++suffix).length
    RationalPRGBinaryInput.readChecked (RationalPRGBinaryInput.encode i++suffix) = some (⟨n,i⟩,suffix) ∧
      RationalPRGBinaryInput.checkedDecodingBitWork model primitive (RationalPRGBinaryInput.encode i++suffix) ≤
        BinaryFrameLogDecodingCost.gamePrice model c n F+(19*n+23)*model.rat (32*(9*F+3)) :=
  ⟨RationalPRGBinaryInput.readChecked_encode_append i suffix,encoded_checked_bound i model primitive c hPrimitive suffix⟩

end Blotto.BinaryDecodedAggregateSize
