import Blotto.FourGluingDescriptor
import Blotto.DyadicSegmentLottery

/-! The finite gluing descriptor's K-bit scalar implementation. The actual
law has a uniform CDF error; every bit vector and descriptor slot is feasible. -/

namespace Blotto.FourInput
open MeasureTheory

noncomputable def gluingDyadicLaw (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (K : ℕ) : Mixed 4 :=
  (i.gluingDescriptor hcase).dyadicLaw K

theorem gluingDyadicLaw_CDF_error (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (K : ℕ) :
    CDFClose (i.gluingDyadicLaw hcase K) (i.gluingCaseLaw hcase) (1 / (2 * (2 : ℝ) ^ K)) := by
  have he := (i.gluingDescriptor hcase).dyadicLaw_CDF_error K
  have hl : (i.gluingDescriptor hcase).law = i.gluingCaseLaw hcase :=
    ProbabilityMeasure.toMeasure_injective (i.gluingDescriptor_law hcase)
  rw [hl] at he
  exact he

theorem gluingDyadicLaw_fullBudget (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (K : ℕ) :
    ∀ᵐ x ∂(i.gluingDyadicLaw hcase K : Measure (Allocation 4)), FullBudget i.B x :=
  (i.gluingDescriptor hcase).dyadicLaw_fullBudget K (fun j =>
    ⟨(i.gluingDescriptor_endpoints hcase).1 j, (i.gluingDescriptor_endpoints hcase).2 j⟩)

theorem gluingDyadicPoint_fullBudget (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (K : ℕ)
    (slot : Fin 81) (bits : Fin K → Bool) :
    FullBudget i.B ((i.gluingDescriptor hcase).dyadicPoint K slot bits) :=
  (i.gluingDescriptor hcase).dyadicPoint_fullBudget K (fun j =>
    ⟨(i.gluingDescriptor_endpoints hcase).1 j, (i.gluingDescriptor_endpoints hcase).2 j⟩) slot bits

end Blotto.FourInput
