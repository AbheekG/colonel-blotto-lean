import Blotto.RationalOverlapCompiler
import Blotto.RationalFourGluingDescriptor

namespace Blotto.RationalFourInput

def compiledRationalGluingDescriptor (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : RationalSegmentLottery 4 81 :=
  RationalOverlapFormula.descriptor (i.overlapData hcase) i.B

theorem compiledRationalGluingDescriptor_eq (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    i.compiledRationalGluingDescriptor hcase = i.gluingDescriptor hcase := rfl

theorem rationalGluingDescriptorWork_bound (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    RationalOverlapFormula.descriptorWork (i.overlapData hcase) i.B ≤ 176256 :=
  RationalOverlapFormula.descriptorWork_bound _ _

end Blotto.RationalFourInput
