import Blotto.GeneralPaperValueRoundingDriver

/-! The sum of individual operand prices is bounded by one price at their
aggregate length. Original input length is additive; no longest-value width
is charged once per field. All aggregate lengths are erased analysis. -/
namespace Blotto.GeneralPaperValueRoundingInputPrice
open GeneralPaperFastRationalModel GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

theorem sum_price {ι : Type*} (model : RationalCostModel) (s : Finset ι) (f : ι → ℕ) :
    (∑ i∈s,model.rat (f i))≤model.rat (∑ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,price_zero,le_refl]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert,ha,not_false_eq_true]
    exact (Nat.add_le_add_left ih _).trans (model.superadditive _ _)

def inputSize {n : ℕ} (values : FixedArrayTable n ℚ) : ℕ := ∑ j,rationalWordWidth (values.read j)
def aggregate {n : ℕ} (M : ℕ) (values : FixedArrayTable n ℚ) : ℕ :=
  (∑ j,GeneralPaperValueRoundArray.width M (values.read j))+n*(1+binaryWordWidth (M+n))
def size {n : ℕ} (M : ℕ) (values : FixedArrayTable n ℚ) : ℕ :=
  8*inputSize values+n*(33+9*binaryWordWidth (M+n))

theorem aggregate_bound {n : ℕ} (M : ℕ) (values : FixedArrayTable n ℚ) : aggregate M values≤size M values := by
  have he : (∑ j,GeneralPaperValueRoundArray.width M (values.read j))=
      n*32+8*(n*binaryWordWidth M+inputSize values) := by
    unfold GeneralPaperValueRoundArray.width inputSize
    rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  have hM := binaryWordWidth_mono (show M≤M+n by omega)
  unfold aggregate size
  rw [he]
  nlinarith only [Nat.mul_le_mul_left n hM]

theorem profile_bound {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ) :
    GeneralPaperValueRoundingDriver.bitProfile model W M values≤
      13*model.rat (size M values)+512*(n+1)*arrayWord W n := by
  have hp := sum_price model Finset.univ (fun j => GeneralPaperValueRoundArray.width M (values.read j))
  have hs := sum_price model (Finset.univ : Finset (Fin n)) (fun _ => 1+binaryWordWidth (M+n))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have ha : (∑ j,GeneralPaperValueRoundArray.width M (values.read j))≤aggregate M values := Nat.le_add_right _ _
  have hb : n*(1+binaryWordWidth (M+n))≤aggregate M values := Nat.le_add_left _ _
  have hp' := hp.trans (model.monotone (ha.trans (aggregate_bound M values)))
  have hs' := hs.trans (model.monotone (hb.trans (aggregate_bound M values)))
  unfold GeneralPaperValueRoundingDriver.bitProfile GeneralPaperValueRoundArray.bitProfile
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum]
  nlinarith only [hp',hs']

theorem native_bound {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (GeneralPaperValueRoundingDriver.run true model W M values).2≤
      13*model.rat (size M values)+512*(n+1)*arrayWord W n :=
  (GeneralPaperValueRoundingDriver.bit_work model W M values v hv).trans (profile_bound model W M values)

theorem native_fast_bound {n : ℕ} {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (W M : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (GeneralPaperValueRoundingDriver.run true actual W M values).2≤
      13*C*size M values*logFactor d (size M values)+512*(n+1)*arrayWord W n := by
  have h := (native_bound actual W M values v hv).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 13 (hg (size M values))) _)
  unfold charge at h
  exact h.trans_eq (by ring)

end Blotto.GeneralPaperValueRoundingInputPrice
