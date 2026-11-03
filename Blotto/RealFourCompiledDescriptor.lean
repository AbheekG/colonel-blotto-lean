import Blotto.RealFourOverlapFactory

namespace Blotto.FourInput

noncomputable def compiledRealGluingDescriptor (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : SegmentLottery 4 81 :=
  (RealFourParameterTable.prepare i).gluingDescriptor hcase

theorem compiledRealGluingDescriptor_eq (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    i.compiledRealGluingDescriptor hcase = i.gluingDescriptor hcase :=
  (RealFourParameterTable.prepare i).gluingDescriptor_eq hcase

theorem realGluingDescriptorWork_bound (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    RealOverlapFormula.descriptorWork (i.overlapData hcase) i.B ≤ 176256 :=
  RealOverlapFormula.descriptorWork_bound _ _

end Blotto.FourInput
