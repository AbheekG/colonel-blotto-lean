import Blotto.GeneralPaperInitializerControlCounters

/-! One complete original-basis entry from the already prepared source
dictionary, H and displayed proxy p/q. It constructs the controls and
auxiliary numerator ONCE and passes those returned values to the rounded
grid, single score matrix and full native controller. Both paper models
retain the complete control pair and native child data for final rechecks.
-/
namespace Blotto.GeneralPaperBasisEntryPrice
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def bits {T m K S : ℕ} (model : RationalCostModel) (W scoreDepth H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (v : RationalFieldSelector m) :=
  let controls := GeneralPaperInitializerControlBits.run model W m H p q reciprocal
  let basis := GeneralPaperInitializedBasisBits.run model W scoreDepth prep v controls.1.1 controls.1.2
  ((controls.1,basis.1),controls.2+basis.2+24*W)

def unit {T m K S : ℕ} (scoreDepth H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (v : RationalFieldSelector m) :=
  let controls := GeneralPaperInitializerControlWork.run m H p q reciprocal
  let basis := GeneralPaperInitializedBasisWork.run scoreDepth prep v controls.1.1 controls.1.2
  ((controls.1,basis.1),controls.2+basis.2+24)

theorem data {T m K S : ℕ} (model : RationalCostModel) (W scoreDepth H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (v : RationalFieldSelector m)
    (hK : 0<K) (hCap : S<2^scoreDepth) :
    (bits model W scoreDepth H p q reciprocal prep v).1=(unit scoreDepth H p q reciprocal prep v).1 := by
  simp only [bits,unit,GeneralPaperInitializerControlBits.data,
    GeneralPaperInitializedBasisWork.data model W scoreDepth prep v _ _ hK hCap]

theorem controls_data {T m K S : ℕ} (model : RationalCostModel) (W scoreDepth H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (v : RationalFieldSelector m) :
    (bits model W scoreDepth H p q reciprocal prep v).1.1=
      (GeneralPaperInitializerParameters.prepare m H p q reciprocal,GeneralPaperBasisGridInputs.auxiliaryNumerator m H p q reciprocal) := by
  simp only [bits,GeneralPaperInitializerControlBits.data,GeneralPaperInitializerControlWork.data]

end Blotto.GeneralPaperBasisEntryPrice
