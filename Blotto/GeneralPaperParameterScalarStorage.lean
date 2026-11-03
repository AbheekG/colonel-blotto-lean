import Blotto.GeneralPaperFastFrontStorageRates

/-! Scalar primitive windows used by the actual four source-parameter
constructors. Literal operands/results and primitive-price fields are
counted. Finite operation lists below are erased observers, not execution
traces or replay; recursive dyadic/ceiling children are separate. -/
namespace Blotto.GeneralPaperParameterScalarStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def naturalWindow (model : RationalCostModel) (W : ℕ) (op : ℕ → ℕ → ℕ) (a b : ℕ) : ℕ :=
  let input := model.rat (max (natBits a) (natBits b))
  let output := model.rat (natBits (op a b))
  natBits a+natBits b+natBits (op a b)+input+output+fields W [input,output,input+output]+128*W

theorem natural_bound (model : RationalCostModel) (W : ℕ) (op : ℕ → ℕ → ℕ) (a b : ℕ) :
    naturalWindow model W op a b≤8*GeneralPaperNaturalPrimitivePrice.binary model.rat op a b+192*W+16 := by
  let input := model.rat (max (natBits a) (natBits b))
  let output := model.rat (natBits (op a b))
  have hi := model.word_le (max (natBits a) (natBits b))
  have ho := model.word_le (natBits (op a b))
  change max (natBits a) (natBits b) ≤ input at hi
  change natBits (op a b)≤output at ho
  have ha := (le_max_left (natBits a) (natBits b)).trans hi
  have hb := (le_max_right (natBits a) (natBits b)).trans hi
  have hf := fields_bound W (input+output+2) [input,output,input+output] (by
    intro z hz
    have hw := GeneralPaperInitializerControlCounters.word_le_self z
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> unfold natBits <;> omega)
  change fields W _≤3*(input+output+2+W)+32*W at hf
  change natBits a+natBits b+natBits (op a b)+input+output+fields W [input,output,input+output]+128*W≤8*(input+output)+192*W+16
  omega

def inverseWindow (model : RationalCostModel) (W d : ℕ) : ℕ :=
  let cast := model.rat (rationalWordWidth (d:ℚ))
  let division := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) 1 (d:ℚ)
  rationalWordWidth (1:ℚ)+rationalWordWidth (d:ℚ)+rationalWordWidth (1/(d:ℚ))+cast+division+
    fields W [cast,division,cast+division]+128*W

theorem inverse_bound (model : RationalCostModel) (W d : ℕ) :
    inverseWindow model W d≤8*GeneralPaperSourceParameterPrice.inverseCost model.rat d+192*W+16 := by
  let cast := model.rat (rationalWordWidth (d:ℚ))
  let division := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) 1 (d:ℚ)
  have hD := model.word_le (rationalWordWidth (d:ℚ))
  have hInput := model.word_le (max (rationalWordWidth (1:ℚ)) (rationalWordWidth (d:ℚ)))
  have hOutput := model.word_le (rationalWordWidth (1/(d:ℚ)))
  have hOne : rationalWordWidth (1:ℚ)≤division := by
    have h := le_max_left (rationalWordWidth (1:ℚ)) (rationalWordWidth (d:ℚ))
    dsimp only [division,GeneralPaperRationalPrimitivePrice.binary,RationalExpression.pairWidth]
    omega
  have hRatio : rationalWordWidth (1/(d:ℚ))≤division := by
    dsimp only [division,GeneralPaperRationalPrimitivePrice.binary]
    omega
  have hf := fields_bound W (cast+division+2) [cast,division,cast+division] (by
    intro z hz
    have hw := GeneralPaperInitializerControlCounters.word_le_self z
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> unfold natBits <;> omega)
  change fields W _≤3*(cast+division+2+W)+32*W at hf
  change rationalWordWidth (d:ℚ)≤cast at hD
  change rationalWordWidth (1:ℚ)+rationalWordWidth (d:ℚ)+rationalWordWidth (1/(d:ℚ))+cast+division+
    fields W [cast,division,cast+division]+128*W≤8*(cast+division)+192*W+16
  omega

def compareWindow (model : RationalCostModel) (W a b : ℕ) : ℕ :=
  let price := GeneralPaperIntegerWordPrice.compare model.rat a b
  natBits a+natBits b+price+fields W [price,if a≤b then 1 else 0]+128*W

theorem compare_bound (model : RationalCostModel) (W a b : ℕ) :
    compareWindow model W a b≤8*GeneralPaperIntegerWordPrice.compare model.rat a b+192*W+16 := by
  let price := GeneralPaperIntegerWordPrice.compare model.rat a b
  have h := model.word_le (max (natBits a) (natBits b))
  change max (natBits a) (natBits b)≤price at h
  have ha := (le_max_left (natBits a) (natBits b)).trans h
  have hb := (le_max_right (natBits a) (natBits b)).trans h
  have hBit : (if a≤b then 1 else 0)≤1 := by split <;> omega
  have hBitWord := binaryWordWidth_mono hBit
  rw [show binaryWordWidth 1=1 by decide] at hBitWord
  have hf := fields_bound W (price+2) [price,if a≤b then 1 else 0] (by
    intro z hz
    have hw := GeneralPaperInitializerControlCounters.word_le_self z
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> unfold natBits <;> omega)
  change fields W _≤2*(price+2+W)+32*W at hf
  change natBits a+natBits b+price+fields W [price,if a≤b then 1 else 0]+128*W≤8*price+192*W+16
  omega

def writeWindow (model : RationalCostModel) (W n : ℕ) : ℕ :=
  natBits n+model.rat (natBits n)+fields W [model.rat (natBits n)]+128*W

theorem write_bound (model : RationalCostModel) (W n : ℕ) :
    writeWindow model W n≤8*model.rat (natBits n)+192*W+16 := by
  have hn := model.word_le (natBits n)
  have hw := GeneralPaperInitializerControlCounters.word_le_self (model.rat (natBits n))
  unfold writeWindow fields
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  unfold natBits at *
  omega

abbrev NaturalOp := (ℕ → ℕ → ℕ)×ℕ×ℕ

def opCost (model : RationalCostModel) (x : NaturalOp) : ℕ := GeneralPaperNaturalPrimitivePrice.binary model.rat x.1 x.2.1 x.2.2
def opWindow (model : RationalCostModel) (W : ℕ) (x : NaturalOp) : ℕ := naturalWindow model W x.1 x.2.1 x.2.2
def cost (model : RationalCostModel) (xs : List NaturalOp) : ℕ := (xs.map (opCost model)).sum
def window (model : RationalCostModel) (W : ℕ) (xs : List NaturalOp) : ℕ := (xs.map (opWindow model W)).sum

theorem list_bound (model : RationalCostModel) (W : ℕ) (xs : List NaturalOp) :
    window model W xs≤8*cost model xs+xs.length*(192*W+16) := by
  induction xs with
  | nil => simp only [window,cost,List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons x xs ih =>
    have h := natural_bound model W x.1 x.2.1 x.2.2
    change opWindow model W x≤8*opCost model x+192*W+16 at h
    simpa only [window,cost,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul] using
      (show opWindow model W x+window model W xs≤8*(opCost model x+cost model xs)+(xs.length+1)*(192*W+16) by
        rw [Nat.add_mul,Nat.one_mul]
        omega)

def prefixes (xs : List ℕ) : List ℕ := (List.range (xs.length+1)).map (fun i => (xs.take i).sum)
def priceFields (W : ℕ) (xs : List ℕ) : ℕ := fields W (xs++prefixes xs)

theorem price_fields_bound (W : ℕ) (xs : List ℕ) :
    priceFields W xs≤(2*xs.length+1)*(natBits xs.sum+W)+32*W := by
  have hf := fields_bound W (natBits xs.sum) (xs++prefixes xs) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_append,prefixes,List.mem_map] at hz
    rcases hz with hz|⟨i,_,rfl⟩
    · exact List.single_le_sum (fun _ _ => Nat.zero_le _) z hz
    · have h := List.sum_take_add_sum_drop xs i
      omega)
  simpa only [priceFields,prefixes,List.length_append,List.length_map,List.length_range,show xs.length+(xs.length+1)=2*xs.length+1 by omega] using hf

end Blotto.GeneralPaperParameterScalarStorage
