import Blotto.GeneralPaperPositiveCeilingConstructionStorage

/-! Actual original rational coordinate rounding and the full indexed
array constructor. Long rational precision occurs in the input owner and
one active scalar window. Fill frames retain short rounded integer weights
and encoded prices, preserving additive original input length. -/
namespace Blotto.GeneralPaperOriginalValueRoundConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperValueRoundArray GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

def scalarPrice (model : RationalCostModel) (A H : ℕ) : ℕ := 11*model.rat H+128*A

def scalarControls (model : RationalCostModel) (A M : ℕ) (v : ℚ) : List ℕ :=
  let scaled := (M:ℚ)*v
  let rounded := GeneralPaperPositiveCeiling.bits model A scaled
  let cast := model.rat (rationalWordWidth (M:ℚ))
  let multiply := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) M v
  [M,(coordinate true model A M v).1,rounded.2,cast,multiply,64*A,rounded.2+cast,
    rounded.2+cast+multiply,(coordinate true model A M v).2]

def scalarWindow (model : RationalCostModel) (A M : ℕ) (v : ℚ) : ℕ :=
  rationalWordWidth v+rationalWordWidth (M:ℚ)+rationalWordWidth ((M:ℚ)*v)+
    GeneralPaperPositiveCeilingConstructionStorage.window model A ((M:ℚ)*v)+
    model.rat (rationalWordWidth (M:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) M v+
    fields A (scalarControls model A M v)+128*A

def scalarProfile (model : RationalCostModel) (A M H : ℕ) : ℕ :=
  3*H+GeneralPaperPositiveCeilingConstructionStorage.profile model A H+3*model.rat H+
    9*(natBits (M+scalarPrice model A H+1)+A)+160*A

theorem output_bound (model : RationalCostModel) (A M : ℕ) (v : ℚ) (hv : 0≤v) (hOne : v≤1) :
    (coordinate true model A M v).1≤M := by
  rw [coordinate_data true model A M v hv hOne]
  apply Nat.ceil_le.mpr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hOne (Nat.cast_nonneg M)

theorem scalar_work (model : RationalCostModel) (A M H : ℕ) (v : ℚ) (hH : width M v≤H) :
    (coordinate true model A M v).2≤scalarPrice model A H :=
  (coordinate_bit_work model A M v).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 11 (model.monotone hH)) _)

theorem scalar_bounded (model : RationalCostModel) (A M H : ℕ) (v : ℚ)
    (hv : 0≤v) (hOne : v≤1) (hH : width M v≤H) : scalarWindow model A M v≤scalarProfile model A M H := by
  let rounded := GeneralPaperPositiveCeiling.bits model A ((M:ℚ)*v)
  let cast := model.rat (rationalWordWidth (M:ℚ))
  let multiply := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) M v
  obtain ⟨hM,hvW,hScaled,hCeil⟩ := widths M v
  have hM' := hM.trans hH
  have hv' := hvW.trans hH
  have hScaled' := hScaled.trans hH
  have hCeiling := GeneralPaperPositiveCeilingConstructionStorage.bounded model A H ((M:ℚ)*v) (hCeil.trans hH)
  have hCast : cast≤model.rat H := model.monotone hM'
  have hMultiply : multiply≤2*model.rat H :=
    GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b) M v H hM' hv' hScaled'
  have hWork := scalar_work model A M H v hH
  have hOutput := output_bound model A M v hv hOne
  have hShape : (coordinate true model A M v).2=rounded.2+cast+multiply+64*A := rfl
  have hf := fields_bound A (natBits (M+scalarPrice model A H+1)) (scalarControls model A M v) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [scalarControls,List.mem_cons,List.not_mem_nil,or_false] at hz
    change z=M ∨ z=(coordinate true model A M v).1 ∨ z=rounded.2 ∨ z=cast ∨ z=multiply ∨ z=64*A ∨
      z=rounded.2+cast ∨ z=rounded.2+cast+multiply ∨ z=(coordinate true model A M v).2 at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields A _≤9*(natBits (M+scalarPrice model A H+1)+A)+32*A at hf
  change rationalWordWidth v+rationalWordWidth (M:ℚ)+rationalWordWidth ((M:ℚ)*v)+
    GeneralPaperPositiveCeilingConstructionStorage.window model A ((M:ℚ)*v)+cast+multiply+
    fields A (scalarControls model A M v)+128*A≤_
  unfold scalarProfile
  omega

theorem scalar_profile_mono (model : RationalCostModel) (W A M H : ℕ) (hWA : W≤A) :
    scalarProfile model W M H≤scalarProfile model A M H := by
  unfold scalarProfile scalarPrice GeneralPaperPositiveCeilingConstructionStorage.profile
    GeneralPaperPositiveCeilingConstructionStorage.price natBits
  gcongr

theorem scalar_work_upper (model : RationalCostModel) (W A M H : ℕ) (v : ℚ) (hWA : W≤A) (hH : width M v≤H) :
    (coordinate true model W M v).2≤scalarPrice model A H := by
  have h := scalar_work model W M H v hH
  unfold scalarPrice at *
  omega

def aggregateWidth (M S : ℕ) : ℕ := 32+8*(binaryWordWidth M+S)
def callbackPrice (model : RationalCostModel) (A H : ℕ) : ℕ := scalarPrice model A H+32*A

def callback {n : ℕ} (model : RationalCostModel) (W A M : ℕ) (values : FixedArrayTable n ℚ) (j : Fin n) : ℕ×ℕ :=
  let made := coordinate true model W M (values.read j)
  (made.1,made.2+32*A)

def callbackWindow {n : ℕ} (model : RationalCostModel) (W A M : ℕ) (values : FixedArrayTable n ℚ) (j : Fin n) : ℕ :=
  scalarWindow model W M (values.read j)+
    fields A [j.val,(coordinate true model W M (values.read j)).2,32*A,(callback model W A M values j).2]+128*A

def callbackProfile (model : RationalCostModel) (A n M H : ℕ) : ℕ :=
  scalarProfile model A M H+4*(natBits (n+callbackPrice model A H+1)+A)+160*A

theorem individual_width {n : ℕ} (M : ℕ) (values : FixedArrayTable n ℚ) (j : Fin n) :
    width M (values.read j)≤aggregateWidth M (GeneralPaperValueRoundingInputPrice.inputSize values) := by
  have h : rationalWordWidth (values.read j)≤GeneralPaperValueRoundingInputPrice.inputSize values :=
    Finset.single_le_sum (f:=fun a : Fin n => rationalWordWidth (values.read a)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold width aggregateWidth
  omega

theorem callback_bounded {n : ℕ} (model : RationalCostModel) (W A M H : ℕ) (values : FixedArrayTable n ℚ)
    (h0 : ∀ j,0≤values.read j) (hOne : ∀ j,values.read j≤1) (hH : ∀ j,width M (values.read j)≤H) (hWA : W≤A) (j : Fin n) :
    callbackWindow model W A M values j≤callbackProfile model A n M H := by
  have hScalar := (scalar_bounded model W M H (values.read j) (h0 j) (hOne j) (hH j)).trans
    (scalar_profile_mono model W A M H hWA)
  have hw := scalar_work_upper model W A M H (values.read j) hWA (hH j)
  have hj := j.isLt.le
  have hf := fields_bound A (natBits (n+callbackPrice model A H+1))
    [j.val,(coordinate true model W M (values.read j)).2,32*A,(callback model W A M values j).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false,callback] at hz
      unfold callbackPrice
      rcases hz with rfl|rfl|rfl|rfl <;> omega)
  change fields A _≤4*(natBits (n+callbackPrice model A H+1)+A)+32*A at hf
  unfold callbackWindow callbackProfile
  omega

def cap (model : RationalCostModel) (A n M H : ℕ) : ℕ :=
  n+M+A+GeneralPaperNativePayloadFillStorage.workCap A n (callbackPrice model A H)+1

def window {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ) (count : ℕ) (hc : count≤n) : ℕ :=
  let A := arrayWord W n
  arrayFootprint A rationalWordWidth values+
    GeneralPaperNativePayloadFillStorage.window A natBits (callback model W A M values) (callbackWindow model W A M values) count hc+
    fields A [n,M,A,(run true model W M values).2]+128*A

def profile (model : RationalCostModel) (W n M S : ℕ) : ℕ :=
  let A := arrayWord W n
  let H := aggregateWidth M S
  S+n*A+64*A+
    GeneralPaperNativePayloadFillStorage.profile A (natBits M) n (callbackPrice model A H) (callbackProfile model A n M H)+
    4*(natBits (cap model A n M H)+A)+160*A

theorem work {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ) :
    (run true model W M values).2≤GeneralPaperNativePayloadFillStorage.workCap (arrayWord W n) n
      (callbackPrice model (arrayWord W n) (aggregateWidth M (GeneralPaperValueRoundingInputPrice.inputSize values))) := by
  have hA := GeneralPaperSummaryArrayControls.array_word_positive W n
  have hIndex := GeneralPaperSummaryArrayControls.array_index W n n le_rfl
  have h := GeneralPaperNativePayloadFillStorage.prefix_work (arrayWord W n)
    (callbackPrice model (arrayWord W n) (aggregateWidth M (GeneralPaperValueRoundingInputPrice.inputSize values)))
    (callback model W (arrayWord W n) M values)
    (fun j => Nat.add_le_add_right (scalar_work_upper model W (arrayWord W n) M _ _
      (by unfold arrayWord;omega) (individual_width M values j)) _) hA hIndex n le_rfl
  exact h

theorem bounded {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ)
    (h0 : ∀ j,0≤values.read j) (hOne : ∀ j,values.read j≤1) (count : ℕ) (hc : count≤n) :
    window model W M values count hc≤profile model W n M (GeneralPaperValueRoundingInputPrice.inputSize values) := by
  let A := arrayWord W n
  let H := aggregateWidth M (GeneralPaperValueRoundingInputPrice.inputSize values)
  have hA := GeneralPaperSummaryArrayControls.array_word_positive W n
  have hWA : W≤A := by unfold A arrayWord;omega
  have hIndex := GeneralPaperSummaryArrayControls.array_index W n n le_rfl
  have hFill := GeneralPaperNativePayloadFillStorage.bounded A (natBits M) (callbackPrice model A H) (callbackProfile model A n M H)
    natBits (callback model W A M values) (callbackWindow model W A M values)
    (fun j => Nat.add_le_add_left (binaryWordWidth_mono (output_bound model W M _ (h0 j) (hOne j))) 1)
    (fun j => Nat.add_le_add_right (scalar_work_upper model W A M H _ hWA (individual_width M values j)) _)
    (fun j => callback_bounded model W A M H values h0 hOne (individual_width M values) hWA j) hA hIndex count hc
  have hWork := work model W M values
  have hInput : arrayFootprint A rationalWordWidth values=
      GeneralPaperValueRoundingInputPrice.inputSize values+n*A+64*A := by
    unfold arrayFootprint GeneralPaperValueRoundingInputPrice.inputSize
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    omega
  have hf := fields_bound A (natBits (cap model A n M H)) [n,M,A,(run true model W M values).2] (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold cap
    change (run true model W M values).2≤GeneralPaperNativePayloadFillStorage.workCap A n (callbackPrice model A H) at hWork
    rcases hz with rfl|rfl|rfl|rfl <;> omega)
  change fields A _≤4*(natBits (cap model A n M H)+A)+32*A at hf
  change arrayFootprint A rationalWordWidth values+
    GeneralPaperNativePayloadFillStorage.window A natBits (callback model W A M values) (callbackWindow model W A M values) count hc+
    fields A [n,M,A,(run true model W M values).2]+128*A≤_
  unfold profile
  change _≤GeneralPaperValueRoundingInputPrice.inputSize values+n*A+64*A+
    GeneralPaperNativePayloadFillStorage.profile A (natBits M) n (callbackPrice model A H) (callbackProfile model A n M H)+
    4*(natBits (cap model A n M H)+A)+160*A
  omega

theorem native_bounded {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (count : ℕ) (hc : count≤n) :
    window model W M values count hc≤profile model W n M (GeneralPaperValueRoundingInputPrice.inputSize values) :=
  bounded model W M values (fun j => by rw [hv];exact (v.positive j).le)
    (fun j => by rw [hv];exact GeneralPaperPositiveValueRounding.input_le_one v j) count hc

@[fun_prop]
theorem profile_scaling (model : RationalCostModel) (n M S : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model W n M S) := by
  unfold profile cap callbackPrice callbackProfile scalarProfile scalarPrice
    GeneralPaperPositiveCeilingConstructionStorage.profile GeneralPaperPositiveCeilingConstructionStorage.price
    GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
    GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap arrayWord
  dsimp only [callbackPrice,scalarPrice]
  fun_prop

end Blotto.GeneralPaperOriginalValueRoundConstructionStorage
