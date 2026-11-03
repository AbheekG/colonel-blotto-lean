import Blotto.RationalFourGluingInputs
import Blotto.RationalOverlapDescriptor
import Blotto.RationalOverlapCompiler

/-! The four-variable native gluing descriptor is exactly the maintained
real 81-slot descriptor, with its safe inactive endpoints and original law. -/

namespace Blotto
open MeasureTheory

theorem OverlapGluing.eq_of_data {k h : ℕ} (G H : OverlapGluing k h)
    (hf : G.first = H.first) (hs : G.second = H.second) (hfp : G.firstProbe = H.firstProbe)
    (hsp : G.secondProbe = H.secondProbe) (hd : G.d = H.d) : G = H := by
  cases G
  cases H
  cases hf
  cases hs
  cases hfp
  cases hsp
  cases hd
  rfl

namespace RationalFourInput

def overlapData (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : RationalOverlapGluing 9 9 where
  first := (i.gluingFirstSpec hcase).segmentLottery
  second := (i.gluingSecondSpec hcase).segmentLottery
  d := i.auxLength
  d_pos := i.auxLength_pos
  first_uniform := by
    rw [RationalThreeSpec.segmentLottery_real, i.gluingFirstSpec_real, i.auxLength_real]
    exact (i.real.overlapData (i.gluingCase_real hcase)).first_uniform
  second_uniform := by
    rw [RationalThreeSpec.segmentLottery_real, i.gluingSecondSpec_real, i.auxLength_real]
    exact (i.real.overlapData (i.gluingCase_real hcase)).second_uniform
  first_P_range := by
    intro slot
    rw [i.gluingFirstSpec_refines]
    have h : (0 : ℝ) ≤ (i.gluingFirstSpecReference hcase).segmentLottery.P slot 2 ∧
        ((i.gluingFirstSpecReference hcase).segmentLottery.P slot 2 : ℝ) ≤ (i.auxLength : ℝ) := by
      change (0 : ℝ) ≤ (i.gluingFirstSpecReference hcase).segmentLottery.real.P slot 2 ∧
        (i.gluingFirstSpecReference hcase).segmentLottery.real.P slot 2 ≤ (i.auxLength : ℝ)
      rw [RationalThreeSpec.segmentLottery_real]
      exact (i.gluingFirstSpecReference hcase).real.segmentLottery_box.1 slot 2
    exact_mod_cast h
  first_Q_range := by
    intro slot
    rw [i.gluingFirstSpec_refines]
    have h : (0 : ℝ) ≤ (i.gluingFirstSpecReference hcase).segmentLottery.Q slot 2 ∧
        ((i.gluingFirstSpecReference hcase).segmentLottery.Q slot 2 : ℝ) ≤ (i.auxLength : ℝ) := by
      change (0 : ℝ) ≤ (i.gluingFirstSpecReference hcase).segmentLottery.real.Q slot 2 ∧
        (i.gluingFirstSpecReference hcase).segmentLottery.real.Q slot 2 ≤ (i.auxLength : ℝ)
      rw [RationalThreeSpec.segmentLottery_real]
      exact (i.gluingFirstSpecReference hcase).real.segmentLottery_box.2 slot 2
    exact_mod_cast h

theorem overlapData_real (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    (i.overlapData hcase).real = i.real.overlapData (i.gluingCase_real hcase) := by
  apply OverlapGluing.eq_of_data
  · exact (i.gluingFirstSpec hcase).segmentLottery_real |>.trans (congrArg ThreeSpec.segmentLottery (i.gluingFirstSpec_real hcase))
  · exact (i.gluingSecondSpec hcase).segmentLottery_real |>.trans (congrArg ThreeSpec.segmentLottery (i.gluingSecondSpec_real hcase))
  · rfl
  · change AffineProbe.reflectedCoordinate (i.auxLength : ℝ) (0 : Fin 3) = AffineProbe.reflectedCoordinate i.real.auxLength 0
    rw [i.auxLength_real]
  · exact i.auxLength_real

def gluingDescriptor (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : RationalSegmentLottery 4 81 :=
  RationalOverlapFormula.descriptor (i.overlapData hcase) i.B

theorem gluingDescriptor_refines (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    i.gluingDescriptor hcase = (i.overlapData hcase).descriptor i.B :=
  RationalOverlapFormula.descriptor_eq _ _

theorem gluingDescriptor_real (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    (i.gluingDescriptor hcase).real = i.real.gluingDescriptor (i.gluingCase_real hcase) := by
  rw [i.gluingDescriptor_refines, RationalOverlapGluing.descriptor_real, i.overlapData_real]
  rfl

theorem gluingDescriptor_law (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    (i.gluingDescriptor hcase).real.law = i.real.gluingCaseLaw (i.gluingCase_real hcase) := by
  rw [i.gluingDescriptor_real]
  exact ProbabilityMeasure.toMeasure_injective (i.real.gluingDescriptor_law (i.gluingCase_real hcase))

theorem gluingDescriptor_endpoints (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (slot : Fin 81) :
    FullBudget (i.B : ℝ) ((i.gluingDescriptor hcase).real.P slot) ∧
      FullBudget (i.B : ℝ) ((i.gluingDescriptor hcase).real.Q slot) := by
  rw [i.gluingDescriptor_real]
  exact ⟨(i.real.gluingDescriptor_endpoints (i.gluingCase_real hcase)).1 slot,
    (i.real.gluingDescriptor_endpoints (i.gluingCase_real hcase)).2 slot⟩

theorem gluingDescriptor_paper_bound (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    (i.gluingDescriptor hcase).real.positiveSlots.card ≤ 735 := by
  rw [i.gluingDescriptor_real]
  exact i.real.gluingDescriptor_paper_bound (i.gluingCase_real hcase)

end RationalFourInput
end Blotto
