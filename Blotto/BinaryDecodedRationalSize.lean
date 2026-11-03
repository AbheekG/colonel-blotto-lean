import Blotto.BinaryRatListDecodingCost
import Blotto.RationalPRGBinaryInput

/-! Reduced rational words parsed from arbitrary frames cannot exceed a
linear input-bit bound. The sequence and game bounds include nonminimal and
signed-zero encodings; successful reads retain their original suffix. -/

namespace Blotto.BinaryRatFrame

theorem read_wordWidth (frame : List Bool) (q : ℚ) (suffix : List Bool)
    (h : read frame = some (q, suffix)) : rationalWordWidth q ≤ 4 * frame.length + 13 := by
  cases frame with
  | nil => cases h
  | cons negative bits =>
    simp only [read] at h
    cases hOne : BinaryNatFrame.read bits with
    | none => rw [hOne, Option.bind_none] at h; cases h
    | some first =>
      rcases first with ⟨magnitude, tail⟩
      rw [hOne, Option.bind_some] at h
      cases hTwo : BinaryNatFrame.read tail with
      | none => rw [hTwo, Option.bind_none] at h; cases h
      | some second =>
        rcases second with ⟨denominator, rest⟩
        rw [hTwo, Option.bind_some] at h
        split at h
        · cases h
        · cases Option.some.inj h
          have hTail := BinaryNatFrame.read_suffix_length bits magnitude tail hOne
          have hM := BinaryNatFrame.read_value_wordWidth bits magnitude tail hOne
          have hD := BinaryNatFrame.read_value_wordWidth tail denominator rest hTwo
          have hSigned := signedValue_wordWidth negative magnitude
          have hDen := signedValue_wordWidth false denominator
          simp only [signedValue, Bool.false_eq_true, ite_false] at hDen
          have hOut := rationalWordWidth_of_height
            ((rationalHeight_of_wordWidth (signedValue negative magnitude)).div
              (rationalHeight_of_wordWidth (denominator : ℚ)))
          simp only [List.length_cons]
          omega

end Blotto.BinaryRatFrame
namespace Blotto.BinaryRatListFrame

theorem read_wordWidths (count : ℕ) (frame : List Bool) (values : List ℚ) (suffix : List Bool)
    (h : read count frame = some (values, suffix)) :
    ∀ q ∈ values, rationalWordWidth q ≤ 4 * frame.length + 13 := by
  induction count generalizing frame values suffix with
  | zero => cases Option.some.inj h; simp
  | succ count ih =>
    simp only [read] at h
    cases hFirst : BinaryRatFrame.read frame with
    | none => rw [hFirst, Option.bind_none] at h; cases h
    | some first =>
      rcases first with ⟨q, tail⟩
      rw [hFirst, Option.bind_some] at h
      cases hRest : read count tail with
      | none => rw [hRest, Option.map_none] at h; cases h
      | some rest =>
        rcases rest with ⟨row, remaining⟩
        rw [hRest, Option.map_some] at h
        cases Option.some.inj h
        have hQ := BinaryRatFrame.read_wordWidth frame q tail hFirst
        have hRow := ih tail row remaining hRest
        have hTail := BinaryRatFrame.read_suffix_length frame q tail hFirst
        intro x hx
        rcases List.mem_cons.mp hx with hHead | hRest
        · subst x; exact hQ
        · exact (hRow x hRest).trans (by omega)

end Blotto.BinaryRatListFrame
namespace Blotto.RationalPRGBinaryInput

theorem read_wordWidths (frame : List Bool) (data : BinaryGameWords) (suffix : List Bool)
    (h : read frame = some (data, suffix)) :
    data.count ≤ frame.length ∧ data.values.length = data.count ∧
      rationalWordWidth data.a ≤ 4 * frame.length + 13 ∧
        rationalWordWidth data.b ≤ 4 * frame.length + 13 ∧
          ∀ q ∈ data.values, rationalWordWidth q ≤ 4 * frame.length + 13 := by
  unfold read at h
  cases hDim : BinaryNatFrame.read frame with
  | none => rw [hDim, Option.bind_none] at h; cases h
  | some dim =>
    rcases dim with ⟨count, tail⟩
    rw [hDim, Option.bind_some] at h
    cases hA : BinaryRatFrame.read tail with
    | none => rw [hA, Option.bind_none] at h; cases h
    | some first =>
      rcases first with ⟨a, rest⟩
      rw [hA, Option.bind_some] at h
      cases hB : BinaryRatFrame.read rest with
      | none => rw [hB, Option.bind_none] at h; cases h
      | some second =>
        rcases second with ⟨b, remaining⟩
        rw [hB, Option.bind_some] at h
        cases hRow : BinaryRatListFrame.read count remaining with
        | none => rw [hRow, Option.map_none] at h; cases h
        | some row =>
          rcases row with ⟨values, last⟩
          rw [hRow, Option.map_some] at h
          cases Option.some.inj h
          have hTail := BinaryNatFrame.read_suffix_length frame count tail hDim
          have hRest := (BinaryRatFrame.read_suffix_length tail a rest hA).trans hTail
          have hRemaining := (BinaryRatFrame.read_suffix_length rest b remaining hB).trans hRest
          have hCount := BinaryRatListFrame.read_count_and_consumption count remaining values last hRow
          have hAW := BinaryRatFrame.read_wordWidth tail a rest hA
          have hBW := BinaryRatFrame.read_wordWidth rest b remaining hB
          have hVW := BinaryRatListFrame.read_wordWidths count remaining values last hRow
          dsimp only
          refine ⟨by omega, hCount.1, hAW.trans (by omega), hBW.trans (by omega), ?_⟩
          intro q hq
          exact (hVW q hq).trans (by omega)

end Blotto.RationalPRGBinaryInput
