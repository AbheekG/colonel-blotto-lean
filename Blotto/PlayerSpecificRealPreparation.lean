import Blotto.PlayerSpecificRationalRecognition
import Blotto.RealPRGGlobalExecution

/-! Accepted numerical parameters build the retained capacities and both
initial resource arrays through named real-RAM loads/arithmetic/stores.
The PlayerSpecificInput argument supplies erased proofs only. -/
namespace Blotto.PlayerSpecificRealPreparation
open PRGRealRAMExecution PRGExactRealRAMContract RealPRGNativeFactoryExecution
set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable def lengthField {n : ℕ} (gamma scale : ℝ) (v w : FixedArrayTable n ℝ) (j : Fin n) : Run ℝ :=
  let first := loadReal v j
  let second := loadReal w j
  let scaled := arithmetic .mul gamma second.value
  let smaller := arithmetic .minimum first.value scaled.value
  let result := arithmetic .div smaller.value scale
  join first (join second (join scaled (join smaller result)))

theorem lengthField_value {n : ℕ} (gamma scale : ℝ) (v w : FixedArrayTable n ℝ) (j : Fin n) :
    (lengthField gamma scale v w j).value=PlayerSpecificMarginals.length (v.read j) (w.read j) gamma scale := rfl

theorem lengthField_cost {n : ℕ} (gamma scale : ℝ) (v w : FixedArrayTable n ℝ) (j : Fin n) :
    (lengthField gamma scale v w j).cost=6 := rfl

noncomputable def lengths {n : ℕ} (gamma scale : ℝ) (v w : FixedArrayTable n ℝ) : Run (FixedArrayTable n ℝ) :=
  arrayRun n (lengthField gamma scale v w)

theorem lengths_value {n : ℕ} (gamma scale : ℝ) (v w : FixedArrayTable n ℝ) :
    (lengths gamma scale v w).value.read=fun j => PlayerSpecificMarginals.length (v.read j) (w.read j) gamma scale := by
  funext j
  exact arrayRun_read _ _ j

theorem lengths_cost {n : ℕ} (gamma scale : ℝ) (v w : FixedArrayTable n ℝ) :
    (lengths gamma scale v w).cost≤8*n+2 := by
  have h := arrayRun_bound n 6 _ (fun j => (lengthField_cost gamma scale v w j).le)
  change (lengths gamma scale v w).cost≤2+n*8 at h
  omega

noncomputable def initialField {n : ℕ} (firstPlayer : Bool) (gamma : ℝ)
    (v w ell : FixedArrayTable n ℝ) (j : Fin n) : Run ℝ :=
  let first := loadReal v j
  let second := loadReal w j
  let capacity := loadReal ell j
  let scaled := arithmetic .mul gamma second.value
  let ratio := if firstPlayer then arithmetic .div first.value scaled.value else arithmetic .div scaled.value first.value
  let one := RealPRGInputExecution.scalar 3 1
  let probability := arithmetic .minimum one.value ratio.value
  let result := arithmetic .mul probability.value capacity.value
  join (⟨(),[.control]⟩ : Run Unit)
    (join first (join second (join capacity (join scaled (join ratio (join one (join probability result)))))))

theorem initialField_value {n : ℕ} (firstPlayer : Bool) (gamma : ℝ)
    (v w ell : FixedArrayTable n ℝ) (j : Fin n) :
    (initialField firstPlayer gamma v w ell j).value=
      (if firstPlayer then PlayerSpecificMarginals.probA (v.read j) (w.read j) gamma
        else PlayerSpecificMarginals.probB (v.read j) (w.read j) gamma)*ell.read j := by
  cases firstPlayer <;> rfl

theorem initialField_cost {n : ℕ} (firstPlayer : Bool) (gamma : ℝ)
    (v w ell : FixedArrayTable n ℝ) (j : Fin n) :
    (initialField firstPlayer gamma v w ell j).cost=10 := by cases firstPlayer <;> rfl

noncomputable def initials {n : ℕ} (firstPlayer : Bool) (gamma : ℝ)
    (v w ell : FixedArrayTable n ℝ) : Run (FixedArrayTable n ℝ) :=
  arrayRun n (initialField firstPlayer gamma v w ell)

theorem initials_value {n : ℕ} (firstPlayer : Bool) (gamma : ℝ) (v w ell : FixedArrayTable n ℝ) :
    (initials firstPlayer gamma v w ell).value.read=fun j =>
      (if firstPlayer then PlayerSpecificMarginals.probA (v.read j) (w.read j) gamma
        else PlayerSpecificMarginals.probB (v.read j) (w.read j) gamma)*ell.read j := by
  funext j
  rw [initials,arrayRun_read,initialField_value]

theorem initials_cost {n : ℕ} (firstPlayer : Bool) (gamma : ℝ) (v w ell : FixedArrayTable n ℝ) :
    (initials firstPlayer gamma v w ell).cost≤12*n+2 := by
  have h := arrayRun_bound n 10 _ (fun j => (initialField_cost firstPlayer gamma v w ell j).le)
  change (initials firstPlayer gamma v w ell).cost≤2+n*12 at h
  omega

structure Prepared {n : ℕ} (i : PlayerSpecificInput n) where
  budget : ℝ
  lengths : FixedArrayTable n ℝ
  initialA : FixedArrayTable n ℝ
  initialB : FixedArrayTable n ℝ
  budget_correct : budget=i.budget
  lengths_correct : lengths.read=i.length
  initialA_correct : initialA.read=i.systemA.initial
  initialB_correct : initialB.read=i.systemB.initial

noncomputable def prepare {n : ℕ} (i : PlayerSpecificInput n) (v w : FixedArrayTable n ℝ)
    (hV : v.read=i.valuesA.weight) (hW : w.read=i.valuesB.weight)
    (gamma scale budget : ℝ) (hG : gamma=i.gamma) (hS : scale=i.scale) (hB : budget=i.budget) : Run (Prepared i) :=
  let loadedGamma := RealPRGInputExecution.scalar 0 gamma
  let loadedScale := RealPRGInputExecution.scalar 1 scale
  let loadedBudget := RealPRGInputExecution.scalar 2 budget
  let ell := lengths loadedGamma.value loadedScale.value v w
  let first := initials true loadedGamma.value v w ell.value
  let second := initials false loadedGamma.value v w ell.value
  have hL : ell.value.read=i.length := by
    rw [lengths_value]
    simp only [loadedGamma,loadedScale,RealPRGInputExecution.scalar,hV,hW,hG,hS]
    rfl
  have hA : first.value.read=i.systemA.initial := by
    rw [initials_value,hL]
    simp only [loadedGamma,RealPRGInputExecution.scalar,hV,hW,hG,ite_true,PlayerSpecificInput.systemA,PlayerSpecificInput.probA]
  have hC : second.value.read=i.systemB.initial := by
    rw [initials_value,hL]
    simp only [loadedGamma,RealPRGInputExecution.scalar,hV,hW,hG,Bool.false_eq_true,ite_false,PlayerSpecificInput.systemB,PlayerSpecificInput.probB]
  join loadedGamma (join loadedScale (join loadedBudget (join ell (join first (join second
    ⟨⟨loadedBudget.value,ell.value,first.value,second.value,hB,hL,hA,hC⟩,
      [.storeCell 0,.storeCell 1,.storeCell 2,.storeCell 3,.control,.control,.control,.control]⟩)))))

theorem prepare_cost {n : ℕ} (i : PlayerSpecificInput n) (v w : FixedArrayTable n ℝ)
    (hV : v.read=i.valuesA.weight) (hW : w.read=i.valuesB.weight)
    (gamma scale budget : ℝ) (hG : gamma=i.gamma) (hS : scale=i.scale) (hB : budget=i.budget) :
    (prepare i v w hV hW gamma scale budget hG hS hB).cost≤32*n+17 := by
  have hL := lengths_cost (RealPRGInputExecution.scalar 0 gamma).value (RealPRGInputExecution.scalar 1 scale).value v w
  have hA := initials_cost true (RealPRGInputExecution.scalar 0 gamma).value v w
    (lengths (RealPRGInputExecution.scalar 0 gamma).value (RealPRGInputExecution.scalar 1 scale).value v w).value
  have hC := initials_cost false (RealPRGInputExecution.scalar 0 gamma).value v w
    (lengths (RealPRGInputExecution.scalar 0 gamma).value (RealPRGInputExecution.scalar 1 scale).value v w).value
  unfold prepare
  rw [join_cost,join_cost,join_cost,join_cost,join_cost,join_cost]
  change 1+(1+(1+(_+(_+(_+8)))))≤_
  omega

end Blotto.PlayerSpecificRealPreparation
