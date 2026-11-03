import Blotto.RealFourFactory
import Blotto.RealOverlapDescriptorCompiler
import Blotto.RealThreeInputCompiler
import Blotto.RationalFourGluingDescriptor

/-! Parent descriptors and common interval length come from one counted
scalar table. Exact data refinement keeps the existing overlap law. -/

namespace Blotto.RealFourParameterTable

noncomputable def overlapData {i : FourInput} (p : RealFourParameterTable i)
    (hcase : (1 - i.p) * i.ell ≤ i.w) : OverlapGluing 9 9 where
  first := (p.gluingFirstSpec hcase).compiledRealLottery
  second := (p.gluingSecondSpec hcase).compiledRealLottery
  firstProbe := AffineProbe.coordinate 2
  secondProbe := AffineProbe.reflectedCoordinate p.auxLength 0
  d := p.auxLength
  d_pos := by rw [p.auxLength_eq]; exact i.auxLength_pos
  first_uniform := by
    rw [p.gluingFirstSpec_eq, ThreeSpec.compiledRealLottery_eq, p.auxLength_eq]
    exact (i.overlapData hcase).first_uniform
  second_uniform := by
    rw [p.gluingSecondSpec_eq, ThreeSpec.compiledRealLottery_eq, p.auxLength_eq]
    exact (i.overlapData hcase).second_uniform
  first_P_range := by
    rw [p.gluingFirstSpec_eq, ThreeSpec.compiledRealLottery_eq, p.auxLength_eq]
    exact (i.overlapData hcase).first_P_range
  first_Q_range := by
    rw [p.gluingFirstSpec_eq, ThreeSpec.compiledRealLottery_eq, p.auxLength_eq]
    exact (i.overlapData hcase).first_Q_range

theorem overlapData_eq {i : FourInput} (p : RealFourParameterTable i)
    (hcase : (1 - i.p) * i.ell ≤ i.w) : p.overlapData hcase = i.overlapData hcase := by
  apply OverlapGluing.eq_of_data
  · change (p.gluingFirstSpec hcase).compiledRealLottery = _
    rw [p.gluingFirstSpec_eq, ThreeSpec.compiledRealLottery_eq]
    rfl
  · change (p.gluingSecondSpec hcase).compiledRealLottery = _
    rw [p.gluingSecondSpec_eq, ThreeSpec.compiledRealLottery_eq]
    rfl
  · rfl
  · change AffineProbe.reflectedCoordinate p.auxLength 0 = AffineProbe.reflectedCoordinate i.auxLength 0
    rw [p.auxLength_eq]
  · exact p.auxLength_eq

noncomputable def gluingDescriptor {i : FourInput} (p : RealFourParameterTable i)
    (hcase : (1 - i.p) * i.ell ≤ i.w) : SegmentLottery 4 81 :=
  RealOverlapFormula.descriptor (p.overlapData hcase) i.B rfl rfl

theorem gluingDescriptor_eq {i : FourInput} (p : RealFourParameterTable i)
    (hcase : (1 - i.p) * i.ell ≤ i.w) : p.gluingDescriptor hcase = i.gluingDescriptor hcase := by
  exact (RealOverlapFormula.descriptor_eq (p.overlapData hcase) i.B rfl rfl).trans
    (congrArg (fun G : OverlapGluing 9 9 => G.descriptor i.B) (p.overlapData_eq hcase))

end Blotto.RealFourParameterTable
