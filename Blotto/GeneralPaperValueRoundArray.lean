import Blotto.GeneralPaperPositiveCeiling

/-! Read each original rational value once, scale it and compute its own
ceiling. No original-value rational sum or common denominator is formed.
Prices retain the individual input word lengths; array controls are separate. -/
namespace Blotto.GeneralPaperValueRoundArray
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

def coordinate (bits : Bool) (model : RationalCostModel) (W M : ℕ) (v : ℚ) : ℕ × ℕ :=
  let scaled := (M:ℚ)*v
  let rounded := if bits then GeneralPaperPositiveCeiling.bits model W scaled else GeneralPaperPositiveCeiling.arithmetic scaled M
  let primitive := if bits then model.rat else fun _ => 1
  (rounded.1,rounded.2+primitive (rationalWordWidth (M:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary primitive (fun a b => a*b) M v+64*W)

theorem coordinate_data (bits : Bool) (model : RationalCostModel) (W M : ℕ) (v : ℚ) (hv : 0≤v) (hOne : v≤1) :
    (coordinate bits model W M v).1=⌈(M:ℚ)*v⌉₊ := by
  have h0 : (0:ℚ)≤(M:ℚ)*v := mul_nonneg (Nat.cast_nonneg _) hv
  have hM : (M:ℚ)*v≤M := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hOne (Nat.cast_nonneg M)
  cases bits
  · exact GeneralPaperPositiveCeiling.arithmetic_data _ M h0 hM
  · exact GeneralPaperPositiveCeiling.bits_data model W _ h0

def width (M : ℕ) (v : ℚ) : ℕ := 32+8*(binaryWordWidth M+rationalWordWidth v)

theorem widths (M : ℕ) (v : ℚ) :
    rationalWordWidth (M:ℚ)≤width M v ∧ rationalWordWidth v≤width M v ∧
      rationalWordWidth ((M:ℚ)*v)≤width M v ∧ GeneralPaperPositiveCeiling.width ((M:ℚ)*v)≤width M v := by
  have hM := GeneralPaperBasisDivideBits.nat_height M
  have hv := rationalHeight_of_wordWidth v
  have hCast := rationalWordWidth_of_height hM
  have hScaled := rationalWordWidth_of_height (hM.mul hv)
  unfold width GeneralPaperPositiveCeiling.width
  omega

theorem coordinate_bit_work (model : RationalCostModel) (W M : ℕ) (v : ℚ) :
    (coordinate true model W M v).2≤11*model.rat (width M v)+128*W := by
  obtain ⟨hM,hv,hScaled,hCeil⟩ := widths M v
  have hc := (GeneralPaperPositiveCeiling.bits_work model W ((M:ℚ)*v)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 8 (model.monotone hCeil)) _)
  have hr := model.monotone hM
  have hm := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b) M v _ hM hv hScaled
  unfold coordinate
  simp only [ite_true]
  nlinarith only [hc,hr,hm]

theorem coordinate_arithmetic_work (model : RationalCostModel) (M : ℕ) (v : ℚ) (hv : 0≤v) (hOne : v≤1) :
    (coordinate false model 1 M v).2≤14*binaryWordWidth M+103 := by
  have hM : (M:ℚ)*v≤M := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hOne (Nat.cast_nonneg M)
  have h := GeneralPaperPositiveCeiling.arithmetic_work ((M:ℚ)*v) M (mul_nonneg (Nat.cast_nonneg _) hv) hM
  unfold coordinate GeneralPaperRationalPrimitivePrice.binary
  simp only [Bool.false_eq_true,ite_false,Nat.mul_one]
  nlinarith only [h]

def run {n : ℕ} (bits : Bool) (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ) : FixedArrayTable n ℕ × ℕ :=
  PaperIndexedArrayConstruction.run (index bits) (address bits W n) (fun j =>
    let value := coordinate bits model W M (values.read j)
    (value.1,value.2+32*address bits W n))

theorem data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ)
    (h0 : ∀ j,0≤values.read j) (hOne : ∀ j,values.read j≤1) :
    (run bits model W M values).1=FixedArrayTable.ofFn (fun j => ⌈(M:ℚ)*values.read j⌉₊) := by
  unfold run
  rw [PaperIndexedArrayConstruction.run_data]
  congr 1
  funext j
  exact coordinate_data bits model W M _ (h0 j) (hOne j)

def bitProfile {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ) : ℕ :=
  (∑ j,(11*model.rat (width M (values.read j))+160*arrayWord W n))+44*(n+1)*arrayWord W n

theorem bit_work {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ) :
    (run true model W M values).2≤bitProfile model W M values := by
  have hA := GeneralPaperSummaryArrayControls.array_word_positive W n
  have hW : W≤arrayWord W n := by unfold arrayWord; omega
  have hOver := GeneralPaperControlArrayPrice.overhead (fun w => w) (arrayWord W n) n n hA le_rfl
    (GeneralPaperSummaryArrayControls.array_index W n)
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ =>
    Nat.add_le_add_right (coordinate_bit_work model W M (values.read j)) (32*arrayWord W n))
  have hs' : (∑ j,((coordinate true model W M (values.read j)).2+32*arrayWord W n))≤
      ∑ j,(11*model.rat (width M (values.read j))+160*arrayWord W n) := by
    apply hs.trans
    apply Finset.sum_le_sum
    intro j _
    nlinarith only [hW]
  unfold run bitProfile
  rw [PaperIndexedArrayConstruction.run_work]
  simp only [index,address,ite_true]
  exact Nat.add_le_add hs' hOver

def arithmeticProfile (n M : ℕ) : ℕ := n*(14*binaryWordWidth M+135)+44*(n+1)

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (M : ℕ) (values : FixedArrayTable n ℚ)
    (h0 : ∀ j,0≤values.read j) (hOne : ∀ j,values.read j≤1) :
    (run false model 1 M values).2≤arithmeticProfile n M := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 (14*binaryWordWidth M+135)
    (fun j => let value := coordinate false model 1 M (values.read j)
      (value.1,value.2+32)) le_rfl (fun _ _ => le_rfl) (fun j => by
        have hc := coordinate_arithmetic_work model M (values.read j) (h0 j) (hOne j)
        dsimp only
        omega)
  simpa only [run,arithmeticProfile,index,address,Bool.false_eq_true,ite_false,Nat.mul_one] using h

end Blotto.GeneralPaperValueRoundArray
