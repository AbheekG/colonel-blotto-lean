import Blotto.GeneralPaperSourceStaticRowReachedRates

/-! Static positive-slope candidates and earliest-row minimum picks.
Only the positive branch reserves negation/division. Full original blocker
indices and reduced root payloads are owned, with native price metadata. -/
namespace Blotto.GeneralPaperStaticChoiceStorage
open RationalOrderCell GeneralPaperRayAffine GeneralPaperRayMinimum GeneralPaperStaticMinimumPrice
open GeneralPaperEncodedScalarStorage GeneralPaperRationalPrimitivePrice GeneralPaperAffineWitnessStorage
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def choiceFoot {i : Type*} (W : ℕ) (encode : i → ℕ) : Option (Choice i) → ℕ
  | none => 1
  | some c => 1+encode c.blocker+rationalWordWidth c.time+32*W

def choiceProfile (W I R : ℕ) : ℕ := 1+I+(1+2*R)+32*W

def Good {i : Type*} (encode : i → ℕ) (I R : ℕ) (a : Option (Choice i)) : Prop :=
  ∀ c,a=some c → encode c.blocker≤I ∧ RationalHeight c.time R

theorem choice_bound {i : Type*} (W I R : ℕ) (encode : i → ℕ) (a : Option (Choice i)) (ha : Good encode I R a) :
    choiceFoot W encode a≤choiceProfile W I R := by
  cases a with
  | none => dsimp only [choiceFoot,choiceProfile]; omega
  | some c =>
    have h := ha c rfl
    have ht := rationalWordWidth_of_height h.2
    dsimp only [choiceFoot,choiceProfile]
    omega

theorem candidate_good {i : Type*} (model : RationalCostModel) (W D E A B R I : ℕ) (hD : 0<D) (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R) (encode : i → ℕ) (j : i) (hj : encode j≤I)
    (a : Affine) (ha : GeneralPaperRayAffineBound.Bounded D E A B a) :
    Good encode I R (GeneralPaperStaticMinimumPrice.candidate model.rat W j a).1 := by
  have hHeight := GeneralPaperStaticMinimumPrice.candidate_height model.rat W D E A B R hD hE hR j a ha
  intro c hc
  refine ⟨?_,hHeight c hc⟩
  rw [GeneralPaperStaticMinimumPrice.candidate_data] at hc
  unfold GeneralPaperRayMinimum.candidate at hc
  split at hc
  · cases hc; exact hj
  · contradiction

def candidateCap (model : RationalCostModel) (W R : ℕ) : ℕ := 1+32*W+5*model.rat (1+2*R)

def candidateBranch (model : RationalCostModel) (W : ℕ) (a : Affine) : ℕ :=
  let negate := unary model.rat Neg.neg a.intercept
  let divide := binary model.rat (·/·) (-a.intercept) a.slope
  rationalWordWidth (-a.intercept)+negate+divide+fields W [negate,divide,negate+divide]+128*W

def candidateWindow {i : Type*} (model : RationalCostModel) (W : ℕ) (encode : i → ℕ) (j : i) (a : Affine) : ℕ :=
  let test := model.rat (RationalExpression.pairWidth 0 a.slope)
  let result := GeneralPaperStaticMinimumPrice.candidate model.rat W j a
  encode j+affineFoot W a+choiceFoot W encode result.1+test+fields W [test,result.2,16*W,32*W]+128*W+
    if 0<a.slope then candidateBranch model W a else 0

def candidateProfile (model : RationalCostModel) (W I R : ℕ) : ℕ :=
  I+affineProfile W R+choiceProfile W I R+(1+2*R)+5*model.rat (1+2*R)+7*(natBits (candidateCap model W R)+W)+320*W

theorem candidate_bound {i : Type*} (model : RationalCostModel) (W D E A B R I : ℕ) (hD : 0<D) (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R) (encode : i → ℕ) (j : i) (hj : encode j≤I)
    (a : Affine) (ha : GeneralPaperRayAffineBound.Bounded D E A B a) :
    candidateWindow model W encode j a≤candidateProfile model W I R := by
  let test := model.rat (RationalExpression.pairWidth 0 a.slope)
  let result := GeneralPaperStaticMinimumPrice.candidate model.rat W j a
  let negate := unary model.rat Neg.neg a.intercept
  let divide := binary model.rat (·/·) (-a.intercept) a.slope
  have hCo := GeneralPaperAffineValuePrice.coefficients hD hE a ha
  have hI := hCo.1.mono hR
  have hS := hCo.2.mono hR
  have hRoot := (GeneralPaperRayAffineBound.crossing_height hD hE ha).mono hR
  have hPos : 0<R := by
    have hd := binaryWordWidth_pos D
    unfold GeneralPaperRayAffineBound.rootWidth at hR
    omega
  have hZero := GeneralPaperQuantizedHeight.zero_height R hPos
  have hAffine := affine_bound W R a hI hS
  have hResult := choice_bound W I R encode result.1 (candidate_good model W D E A B R I hD hE hR encode j hj a ha)
  have hTest : test≤model.rat (1+2*R) := model.monotone (max_le (rationalWordWidth_of_height hZero) (rationalWordWidth_of_height hS))
  have hNegate : negate≤2*model.rat (1+2*R) := unary_le model.rat model.monotone Neg.neg _ _ (rationalWordWidth_of_height hI) (rationalWordWidth_of_height hI.neg)
  have hDivide : divide≤2*model.rat (1+2*R) := binary_le model.rat model.monotone (·/·) _ _ _
    (rationalWordWidth_of_height hI.neg) (rationalWordWidth_of_height hS) (rationalWordWidth_of_height hRoot)
  have hNegWord := rationalWordWidth_of_height hI.neg
  have hWork := GeneralPaperStaticMinimumPrice.candidate_work model.rat model.monotone W D E A B R hD hE hR j a ha
  change result.2≤32*W+5*model.rat (1+2*R) at hWork
  have hFields := fields_bound W (natBits (candidateCap model W R)) [test,result.2,16*W,32*W] (by
    intro b hb
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl
    all_goals unfold candidateCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (candidateCap model W R)+W)+32*W at hFields
  have hBranch : (if 0<a.slope then candidateBranch model W a else 0)≤
      (1+2*R)+4*model.rat (1+2*R)+3*(natBits (candidateCap model W R)+W)+160*W := by
    split
    · have hf := fields_bound W (natBits (candidateCap model W R)) [negate,divide,negate+divide] (by
        intro b hb
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
        rcases hb with rfl|rfl|rfl
        all_goals unfold candidateCap; omega)
      change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (candidateCap model W R)+W)+32*W at hf
      change rationalWordWidth (-a.intercept)+negate+divide+GeneralPaperEncodedScalarStorage.fields W [negate,divide,negate+divide]+128*W≤_
      omega
    · omega
  change encode j+affineFoot W a+choiceFoot W encode result.1+test+GeneralPaperEncodedScalarStorage.fields W [test,result.2,16*W,32*W]+128*W+_≤_
  unfold candidateProfile
  omega

theorem pick_good {i : Type*} (model : RationalCostModel) (W I R : ℕ) (encode : i → ℕ)
    (a b : Option (Choice i)) (ha : Good encode I R a) (hb : Good encode I R b) :
    Good encode I R (GeneralPaperStaticMinimumPrice.pick model.rat W a b).1 := by
  rw [GeneralPaperStaticMinimumPrice.pick_data]
  cases a with
  | none => exact hb
  | some a =>
    cases b with
    | none => exact ha
    | some b =>
      change Good encode I R (if a.time≤b.time then some a else some b)
      split
      · exact ha
      · exact hb

def comparePrice {i : Type*} (model : RationalCostModel) : Option (Choice i) → Option (Choice i) → ℕ
  | some a,some b => model.rat (RationalExpression.pairWidth a.time b.time)
  | _,_ => 0

def pickCap (model : RationalCostModel) (W R : ℕ) : ℕ := 1+8*W+model.rat (1+2*R)
def pickWindow {i : Type*} (model : RationalCostModel) (W : ℕ) (encode : i → ℕ) (a b : Option (Choice i)) : ℕ :=
  let result := GeneralPaperStaticMinimumPrice.pick model.rat W a b
  let compare := comparePrice model a b
  choiceFoot W encode a+choiceFoot W encode b+choiceFoot W encode result.1+compare+fields W [compare,result.2,8*W]+128*W

def pickProfile (model : RationalCostModel) (W I R : ℕ) : ℕ :=
  3*choiceProfile W I R+model.rat (1+2*R)+3*(natBits (pickCap model W R)+W)+160*W

theorem pick_bound {i : Type*} (model : RationalCostModel) (W I R : ℕ) (encode : i → ℕ)
    (a b : Option (Choice i)) (ha : Good encode I R a) (hb : Good encode I R b) :
    pickWindow model W encode a b≤pickProfile model W I R := by
  let result := GeneralPaperStaticMinimumPrice.pick model.rat W a b
  let compare := comparePrice model a b
  have hA := choice_bound W I R encode a ha
  have hB := choice_bound W I R encode b hb
  have hResult := choice_bound W I R encode result.1 (pick_good model W I R encode a b ha hb)
  have hCompare : compare≤model.rat (1+2*R) := by
    cases a with
    | none => change 0≤_; omega
    | some a =>
      cases b with
      | none => change 0≤_; omega
      | some b => exact model.monotone (max_le (rationalWordWidth_of_height (ha a rfl).2) (rationalWordWidth_of_height (hb b rfl).2))
  have hWork := GeneralPaperStaticMinimumPrice.pick_work model.rat model.monotone W R a b
    (fun c hc => (ha c hc).2) (fun c hc => (hb c hc).2)
  change result.2≤8*W+model.rat (1+2*R) at hWork
  have hf := fields_bound W (natBits (pickCap model W R)) [compare,result.2,8*W] (by
    intro c hc
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl
    all_goals unfold pickCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (pickCap model W R)+W)+32*W at hf
  change choiceFoot W encode a+choiceFoot W encode b+choiceFoot W encode result.1+compare+GeneralPaperEncodedScalarStorage.fields W [compare,result.2,8*W]+128*W≤_
  unfold pickProfile
  omega

end Blotto.GeneralPaperStaticChoiceStorage
