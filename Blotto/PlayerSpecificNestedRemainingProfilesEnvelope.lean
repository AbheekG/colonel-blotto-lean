import Blotto.PlayerSpecificNestedFirstProfileEnvelope
import Blotto.PlayerSpecificNestedSecondProfileSourceCost
import Blotto.PlayerSpecificNestedThirdProfileSourceCost
import Blotto.PlayerSpecificNestedInteriorProfileSourceCost
import Blotto.PlayerSpecificNestedAssemblyEnvelope

/-! The second, third and selected interior nested profile source work is
polynomial after composing reached assembly heights and descriptor costs. -/
namespace Blotto.PlayerSpecificNestedRemainingProfilesEnvelope
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev S := PlayerSpecificPolynomialPairTerms.size
private abbrev E (f : ℕ × ℕ → ℕ) := NaturalPolynomialEnvelope S f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : ℕ × ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun p => f p+g p) := NaturalPolynomialEnvelope.add hf hg
private theorem lift_first {f : ℕ → ℕ}
    (hf : NaturalPolynomialEnvelope (fun H : ℕ => H) f) :
    E (fun p => f p.1) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (g := fun p : ℕ × ℕ => p.1) hf PlayerSpecificPolynomialPairTerms.first

private theorem compare_term : E
    (fun p : ℕ × ℕ => PlayerSpecificCompareSourceCost.coefficient*(p.1+1)^3) :=
  lift_first (PlayerSpecificPolynomialTerms.iterated 0 1 3
    PlayerSpecificCompareSourceCost.coefficient)

theorem second_profile_work : E
    (fun p : ℕ × ℕ => PlayerSpecificNestedSecondProfileSourceCost.work p.1 p.2) := by
  have hu := lift_first PlayerSpecificNestedEndpointEnvelopes.second_uniform_work
  have hc := add compare_term (c 2)
  have hall := add (add (add (add
    PlayerSpecificNestedFirstProfileEnvelope.family_profile_work hc)
    (add hu PlayerSpecificNestedAssemblyEnvelope.binary_work))
    PlayerSpecificNestedAssemblyEnvelope.pad_work) (c 2)
  simpa only [PlayerSpecificNestedSecondProfileSourceCost.work] using hall

private theorem residual_work : NaturalPolynomialEnvelope (fun H : ℕ => H)
    (fun H => PlayerSpecificNestedThirdProfileSourceCost.residualWork H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 1 3
    PlayerSpecificResidualTableSourceCost.coefficient
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope
    PlayerSpecificPolynomialTerms.input 11
  have h2 := PlayerSpecificPolynomialSubstitution.substitute
    (g := fun H => iterate 11 H)
    (PlayerSpecificNestedDescriptorEnvelopes.pad_fixed 3 3 6) hi
  have hall := NaturalPolynomialEnvelope.add
    (NaturalPolynomialEnvelope.add h1 h2)
    (PlayerSpecificPolynomialTerms.constant 2)
  simpa only [PlayerSpecificNestedThirdProfileSourceCost.residualWork,iterate] using hall

theorem third_profile_work : E
    (fun p : ℕ × ℕ => PlayerSpecificNestedThirdProfileSourceCost.work p.1 p.2) := by
  have hr := lift_first residual_work
  have hc := add compare_term (c 2)
  have hall := add (add (add (add hr hc)
    (add PlayerSpecificNestedFirstProfileEnvelope.family_profile_work
      PlayerSpecificNestedAssemblyEnvelope.binary_work))
    PlayerSpecificNestedAssemblyEnvelope.pad_work) (c 2)
  simpa only [PlayerSpecificNestedThirdProfileSourceCost.work] using hall

theorem selected_work : E
    (fun p : ℕ × ℕ => PlayerSpecificNestedInteriorProfileSourceCost.selectedWork p.1 p.2) := by
  have hc := NaturalPolynomialEnvelope.mul (c 2) compare_term
  have hall := add (add (add (add hc
    PlayerSpecificNestedFirstProfileEnvelope.first_profile_work)
    second_profile_work) third_profile_work) (c 4)
  simpa only [PlayerSpecificNestedInteriorProfileSourceCost.selectedWork] using hall

theorem interior_profile_work : E
    (fun p : ℕ × ℕ => PlayerSpecificNestedInteriorProfileSourceCost.work p.1 p.2) := by
  have h1 := lift_first (PlayerSpecificPolynomialTerms.iterated 0 1 3
    PlayerSpecificNestedCaseParameterSourceCost.coefficient)
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope
    PlayerSpecificPolynomialPairTerms.first 9
  have hsize := add hi PlayerSpecificPolynomialPairTerms.second
  have h2 := PlayerSpecificPolynomialSubstitution.substitute
    (g := fun p : ℕ × ℕ => (iterate 9 p.1,p.2)) selected_work hsize
  have hall := add (add h1 h2) (c 2)
  simpa only [PlayerSpecificNestedInteriorProfileSourceCost.work,iterate] using hall

end Blotto.PlayerSpecificNestedRemainingProfilesEnvelope
