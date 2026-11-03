import Blotto.GeneralPaperInitializerProducts

/-! Construct N/depth/beta/tau/auxiliary and the original-grid auxiliary
numerator, using one shared product prefix and one power-ceiling execution.
The complete native control record, including its annotation, is preserved.
This unit-arithmetic call does not inspect input encodings or require bit
capacities. H and the classified proxy integers are inputs to this phase.
-/
namespace Blotto.GeneralPaperInitializerControlWork
set_option autoImplicit false
set_option maxHeartbeats 6000000

def beta (p q : ℕ) (reciprocal : Bool) : ℚ := if reciprocal then (q:ℚ)/p else (p:ℚ)/q

def assemble (m p q : ℕ) (reciprocal : Bool) (c : GeneralPaperInitializerProducts.Products)
    (scale : GeneralPaperPowerCeiling.Result) : GeneralPaperInitializerParameters.Parameters × ℤ :=
  let ratio := beta p q reciprocal
  let tau : ℚ := (m:ℚ)/c.N
  (⟨c.N,scale.doublings+1,ratio,tau,ratio-tau,scale.work+64⟩,(c.scaled:ℤ)-(m:ℤ))

theorem assemble_data (m H p q : ℕ) (reciprocal : Bool) :
    assemble m p q reciprocal (GeneralPaperInitializerProducts.run m H p q reciprocal)
      (GeneralPaperPowerCeiling.ceiling (GeneralPaperInitializerProducts.run m H p q reciprocal).N)=
        (GeneralPaperInitializerParameters.prepare m H p q reciprocal,GeneralPaperBasisGridInputs.auxiliaryNumerator m H p q reciprocal) := by
  cases reciprocal <;> rfl

def run (m H p q : ℕ) (reciprocal : Bool) : (GeneralPaperInitializerParameters.Parameters × ℤ) × ℕ :=
  let products := GeneralPaperInitializerProducts.run m H p q reciprocal
  let scale := GeneralPaperPowerCeiling.ceiling products.N
  (assemble m p q reciprocal products scale,scale.work+192)

theorem data (m H p q : ℕ) (reciprocal : Bool) :
    (run m H p q reciprocal).1=
      (GeneralPaperInitializerParameters.prepare m H p q reciprocal,GeneralPaperBasisGridInputs.auxiliaryNumerator m H p q reciprocal) :=
  assemble_data m H p q reciprocal

theorem work (m H p q : ℕ) (reciprocal : Bool) :
    (run m H p q reciprocal).2≤12*binaryWordWidth (4*m*H*p*q)+194 := by
  have hw := GeneralPaperPowerCeiling.ceiling_work (4*m*H*p*q)
  change (GeneralPaperPowerCeiling.ceiling (4*m*H*p*q)).work+192≤_
  omega

end Blotto.GeneralPaperInitializerControlWork
