import Blotto.GeneralPaperRetainedEndpointFraction

/-! Complete arithmetic/bit construction prices for the retained basis
inputs. The matrix is passed by reference and is never reconstructed.
Canonical initializer controls occur only in erased price bounds. -/
namespace Blotto.GeneralPaperRetainedBasisInputsPrice
open GeneralPaperRetainedBasisInputs
set_option autoImplicit false
set_option maxHeartbeats 3500000

def arithmeticProfile (m K H p q : ℕ) (reciprocal : Bool) : ℕ :=
  12*binaryWordWidth (4*m*H*p*q)+
    128*(m+1)*(K+1)*((GeneralPaperInitializerParameters.prepare m H p q reciprocal).depth+1)+
    1024*(m*(K-1)+m+1)+274

theorem arithmetic_work {T m K S : ℕ} (model : RationalCostModel) (H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) :
    (run false model 1 H p q reciprocal prep matrix).2≤arithmeticProfile m K H p q reciprocal := by
  let ctl := controls false model 1 m H p q reciprocal
  have hc := GeneralPaperInitializerControlWork.work m H p q reciprocal
  change ctl.2≤_ at hc
  have hg := GeneralPaperInitializerGridPrice.unit_work ctl.1.1.N ctl.1.1.depth prep.dictionary
  change (grid false model 1 ctl.1.1.N ctl.1.1.depth prep.dictionary).2≤_ at hg
  have hd : ctl.1=(GeneralPaperInitializerParameters.prepare m H p q reciprocal,
      GeneralPaperBasisGridInputs.auxiliaryNumerator m H p q reciprocal) := controls_data false model 1 m H p q reciprocal
  rw [hd] at hg
  change ctl.2+(grid false model 1 ctl.1.1.N ctl.1.1.depth prep.dictionary).2+64≤_
  rw [hd]
  unfold arithmeticProfile
  dsimp only at hg ⊢
  omega

def bitProfile (model : RationalCostModel) (W H p q A m K : ℕ) (reciprocal : Bool) : ℕ :=
  GeneralPaperInitializerControlBits.profile model W m H p q+
    GeneralPaperInitializerGridPrice.profile model W
      (GeneralPaperInitializerParameters.prepare m H p q reciprocal).N
      (GeneralPaperInitializerParameters.prepare m H p q reciprocal).depth A m K+64*W

theorem bit_work {T m K S : ℕ} (model : RationalCostModel) (W H p q A : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q)
    (hUnit : ∀ j l,0≤prep.dictionary.anchor j l ∧ prep.dictionary.anchor j l≤1)
    (hHeight : ∀ j l,RationalHeight (prep.dictionary.anchor j l) A) (hW : 1≤W)
    (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) (hD : binaryWordWidth (m*(K-1)+1)≤W) :
    (run true model W H p q reciprocal prep matrix).2≤bitProfile model W H p q A m K reciprocal := by
  let ctl := controls true model W m H p q reciprocal
  have hc := GeneralPaperInitializerControlBits.work model W m H p q reciprocal
  change ctl.2≤_ at hc
  have hd : ctl.1=(GeneralPaperInitializerParameters.prepare m H p q reciprocal,
      GeneralPaperBasisGridInputs.auxiliaryNumerator m H p q reciprocal) := controls_data true model W m H p q reciprocal
  have hg := GeneralPaperInitializerGridPrice.work model W
    (GeneralPaperInitializerParameters.prepare m H p q reciprocal).N
    (GeneralPaperInitializerParameters.prepare m H p q reciprocal).depth A prep.dictionary
    (GeneralPaperInitializerParameters.N_positive m H p q reciprocal hm hH hp hq)
    (GeneralPaperInitializerParameters.quotient_cap m H p q reciprocal) hUnit hHeight hW hK hM hD
  change ctl.2+(grid true model W ctl.1.1.N ctl.1.1.depth prep.dictionary).2+64*W≤_
  rw [hd]
  unfold bitProfile
  exact Nat.add_le_add_right (Nat.add_le_add hc hg) _

end Blotto.GeneralPaperRetainedBasisInputsPrice
