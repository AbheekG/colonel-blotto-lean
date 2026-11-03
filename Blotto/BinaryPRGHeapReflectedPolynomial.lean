import Blotto.BinaryPRGHeapReflectedWork
import Blotto.BinaryPRGWordControllerRawWorkBound

/-! The full reflected draw price, with physical resource setup and retained
categorical/profile emission, has polynomial growth in source height, scalar
precision and seed parameters. -/

namespace Blotto.BinaryPRGHeapReflectedPolynomial
open BinaryPRGHeapResourcePolynomial

theorem bound_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => BinaryPRGHeapReflectedWork.bound p.wordWidth p.count p.seedWidth p.seedCap) := by
  unfold BinaryPRGHeapReflectedWork.bound
  apply NaturalPolynomialEnvelope.add
  · unfold_controller_source_envelope
    unfold_boolean_three_envelope
    unfold_terminal_envelope
    resource_polynomial
  · exact BinaryPRGHeapReflectedSetup.bound_polynomial

end Blotto.BinaryPRGHeapReflectedPolynomial
