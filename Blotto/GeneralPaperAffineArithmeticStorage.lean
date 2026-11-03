import Blotto.GeneralPaperAffineWitnessStorage

/-! Literal affine coefficient addition and guarded crossing arithmetic.
Operands, reduced differences/negation/root, primitive scratch and encoded
native price counters are retained. Parallel pairs execute no division.
Only primitive reservations, not a traversal runtime, contribute scratch. -/
namespace Blotto.GeneralPaperAffineArithmeticStorage
open GeneralPaperEncodedScalarStorage GeneralPaperAffineWitnessStorage GeneralPaperRayAffine
open GeneralPaperRationalPrimitivePrice GeneralPaperRayAffineComparison
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def addCap (model : RationalCostModel) (W R : ℕ) : ℕ := 32*W+4*model.rat (1+2*R)
def addWindow (model : RationalCostModel) (W : ℕ) (f g : Affine) : ℕ :=
  let result := GeneralPaperAffineValuePrice.addRun model.rat W f g
  let a := binary model.rat (·+·) f.intercept g.intercept
  let b := binary model.rat (·+·) f.slope g.slope
  affineFoot W f+affineFoot W g+affineFoot W result.1+a+b+fields W [result.2,a,b,32*W,32*W+a]+128*W
def addProfile (model : RationalCostModel) (W R : ℕ) : ℕ :=
  3*affineProfile W R+4*model.rat (1+2*R)+5*(natBits (addCap model W R)+W)+160*W

theorem add_bounded (model : RationalCostModel) (W R : ℕ) (f g : Affine)
    (hf : RationalHeight f.intercept R ∧ RationalHeight f.slope R)
    (hg : RationalHeight g.intercept R ∧ RationalHeight g.slope R)
    (hs : RationalHeight (f.intercept+g.intercept) R ∧ RationalHeight (f.slope+g.slope) R) :
    addWindow model W f g≤addProfile model W R := by
  let result := GeneralPaperAffineValuePrice.addRun model.rat W f g
  let a := binary model.rat (·+·) f.intercept g.intercept
  let b := binary model.rat (·+·) f.slope g.slope
  have hF := affine_bound W R f hf.1 hf.2
  have hG := affine_bound W R g hg.1 hg.2
  have hS := affine_bound W R result.1 hs.1 hs.2
  have ha : a≤2*model.rat (1+2*R) := binary_le model.rat model.monotone (·+·) _ _ _
    (rationalWordWidth_of_height hf.1) (rationalWordWidth_of_height hg.1) (rationalWordWidth_of_height hs.1)
  have hb : b≤2*model.rat (1+2*R) := binary_le model.rat model.monotone (·+·) _ _ _
    (rationalWordWidth_of_height hf.2) (rationalWordWidth_of_height hg.2) (rationalWordWidth_of_height hs.2)
  have hWork : result.2=32*W+a+b := rfl
  have hFields := fields_bound W (natBits (addCap model W R)) [result.2,a,b,32*W,32*W+a] (by
    intro c hc
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    all_goals unfold addCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (addCap model W R)+W)+32*W at hFields
  change affineFoot W f+affineFoot W g+affineFoot W result.1+a+b+GeneralPaperEncodedScalarStorage.fields W [result.2,a,b,32*W,32*W+a]+128*W≤_
  unfold addProfile
  omega

def rootFoot (W : ℕ) : Option ℚ → ℕ
  | none => 1
  | some q => 1+rationalWordWidth q+32*W
def rootProfile (W R : ℕ) : ℕ := 1+(1+2*R)+32*W

theorem root_bound (W R : ℕ) (a : Option ℚ) (h : ∀ q,a=some q → RationalHeight q R) : rootFoot W a≤rootProfile W R := by
  cases a with
  | none => change 1≤_; unfold rootProfile; omega
  | some q =>
    have hw := rationalWordWidth_of_height (h q rfl)
    change 1+rationalWordWidth q+32*W≤_
    unfold rootProfile
    omega

def crossingCap (model : RationalCostModel) (W R : ℕ) : ℕ := 1+64*W+9*model.rat (1+2*R)
def branchWindow (model : RationalCostModel) (W : ℕ) (a b : Affine) : ℕ :=
  let d := difference a b
  let p := binary model.rat (·-·) a.intercept b.intercept
  let q := binary model.rat (·-·) a.slope b.slope
  let r := unary model.rat Neg.neg d.intercept
  let s := binary model.rat (·/·) (-d.intercept) d.slope
  affineFoot W d+rationalWordWidth (-d.intercept)+p+q+r+s+
    fields W [p,q,r,s,p+q,p+q+r,p+q+r+s]+128*W

def crossingWindow (model : RationalCostModel) (W : ℕ) (a b : Affine) : ℕ :=
  let result := GeneralPaperAffineCrossingPrice.run model.rat W a b
  let equality := model.rat (RationalExpression.pairWidth a.slope b.slope)
  affineFoot W a+affineFoot W b+rootFoot W result.1+equality+
    fields W [result.2,equality,16*W,64*W]+256*W+
    if a.slope=b.slope then 0 else branchWindow model W a b

def crossingProfile (model : RationalCostModel) (W R : ℕ) : ℕ :=
  3*affineProfile W R+(1+2*R)+rootProfile W R+9*model.rat (1+2*R)+
    11*(natBits (crossingCap model W R)+W)+448*W

theorem crossing_bounded (model : RationalCostModel) (W D E A B R : ℕ) (hD : 0<D) (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E (A+A) (B+B)≤R) (a b : Affine)
    (ha : GeneralPaperRayAffineBound.Bounded D E A B a) (hb : GeneralPaperRayAffineBound.Bounded D E A B b) :
    crossingWindow model W a b≤crossingProfile model W R := by
  let d := difference a b
  let result := GeneralPaperAffineCrossingPrice.run model.rat W a b
  let equality := model.rat (RationalExpression.pairWidth a.slope b.slope)
  let p := binary model.rat (·-·) a.intercept b.intercept
  let q := binary model.rat (·-·) a.slope b.slope
  let r := unary model.rat Neg.neg d.intercept
  let s := binary model.rat (·/·) (-d.intercept) d.slope
  have hBase := (GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B) (Nat.le_add_right _ _) (Nat.le_add_right _ _)).trans hR
  have hA := GeneralPaperAffineValuePrice.coefficients hD hE a ha
  have hB := GeneralPaperAffineValuePrice.coefficients hD hE b hb
  have hAI := hA.1.mono hBase
  have hAS := hA.2.mono hBase
  have hBI := hB.1.mono hBase
  have hBS := hB.2.mono hBase
  have hd := GeneralPaperRayAffineBound.difference ha hb
  have hDiff := GeneralPaperAffineValuePrice.coefficients hD hE d hd
  have hDI := hDiff.1.mono hR
  have hDS := hDiff.2.mono hR
  have hRoot := (GeneralPaperRayAffineBound.crossing_height hD hE hd).mono hR
  have hAF := affine_bound W R a hAI hAS
  have hBF := affine_bound W R b hBI hBS
  have hDF := affine_bound W R d hDI hDS
  have hNeg := rationalWordWidth_of_height hDI.neg
  have hEq : equality≤model.rat (1+2*R) := model.monotone (max_le (rationalWordWidth_of_height hAS) (rationalWordWidth_of_height hBS))
  have hp : p≤2*model.rat (1+2*R) := binary_le model.rat model.monotone (·-·) _ _ _
    (rationalWordWidth_of_height hAI) (rationalWordWidth_of_height hBI) (rationalWordWidth_of_height hDI)
  have hq : q≤2*model.rat (1+2*R) := binary_le model.rat model.monotone (·-·) _ _ _
    (rationalWordWidth_of_height hAS) (rationalWordWidth_of_height hBS) (rationalWordWidth_of_height hDS)
  have hr : r≤2*model.rat (1+2*R) := unary_le model.rat model.monotone Neg.neg _ _ (rationalWordWidth_of_height hDI) hNeg
  have hs : s≤2*model.rat (1+2*R) := binary_le model.rat model.monotone (·/·) _ _ _ hNeg
    (rationalWordWidth_of_height hDS) (rationalWordWidth_of_height hRoot)
  have hOpt := root_bound W R result.1 (by
    intro c hc
    rw [GeneralPaperAffineCrossingPrice.data] at hc
    exact (GeneralPaperRayCrossingSize.crossing hD hE a b ha hb c hc).mono hR)
  have hWork := GeneralPaperAffineCrossingPrice.work model.rat model.monotone W D E A B R hD hE hR a b ha hb
  change result.2≤64*W+9*model.rat (1+2*R) at hWork
  have hOuter := fields_bound W (natBits (crossingCap model W R)) [result.2,equality,16*W,64*W] (by
    intro c hc
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl
    all_goals unfold crossingCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (crossingCap model W R)+W)+32*W at hOuter
  have hFields := fields_bound W (natBits (crossingCap model W R)) [p,q,r,s,p+q,p+q+r,p+q+r+s] (by
    intro c hc
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold crossingCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤7*(natBits (crossingCap model W R)+W)+32*W at hFields
  have hBranch : branchWindow model W a b≤affineProfile W R+(1+2*R)+8*model.rat (1+2*R)+
      7*(natBits (crossingCap model W R)+W)+160*W := by
    change affineFoot W d+rationalWordWidth (-d.intercept)+p+q+r+s+
      GeneralPaperEncodedScalarStorage.fields W [p,q,r,s,p+q,p+q+r,p+q+r+s]+128*W≤_
    omega
  change affineFoot W a+affineFoot W b+rootFoot W result.1+equality+
    GeneralPaperEncodedScalarStorage.fields W [result.2,equality,16*W,64*W]+256*W+(if a.slope=b.slope then 0 else branchWindow model W a b)≤_
  unfold crossingProfile
  split_ifs <;> omega

def optionalWindow (model : RationalCostModel) (W : ℕ) (a b : Option Affine) : ℕ :=
  optionAffineFoot W a+optionAffineFoot W b+
    match a,b with
    | some f,some g =>
      let root := GeneralPaperAffineCrossingPrice.run model.rat W f g
      let result := GeneralPaperAffineCrossingPrice.optionalRun model.rat W a b
      crossingWindow model W f g+fields W [root.2,result.2,8*W]+128*W
    | _,_ => fields W [(GeneralPaperAffineCrossingPrice.optionalRun model.rat W a b).2,8*W]+128*W

def optionalProfile (model : RationalCostModel) (W R : ℕ) : ℕ :=
  2*optionAffineProfile W R+crossingProfile model W R+
    3*(natBits (1+72*W+9*model.rat (1+2*R))+W)+160*W

theorem optional_bounded (model : RationalCostModel) (W D E A B R : ℕ) (hD : 0<D) (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E (A+A) (B+B)≤R) (a b : Option Affine)
    (ha : ∀ f,a=some f → GeneralPaperRayAffineBound.Bounded D E A B f)
    (hb : ∀ f,b=some f → GeneralPaperRayAffineBound.Bounded D E A B f) :
    optionalWindow model W a b≤optionalProfile model W R := by
  have hBase := (GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B) (Nat.le_add_right _ _) (Nat.le_add_right _ _)).trans hR
  have hA := option_affine_bound W R a (by
    intro f hf
    have hh := GeneralPaperAffineValuePrice.coefficients hD hE f (ha f hf)
    exact ⟨hh.1.mono hBase,hh.2.mono hBase⟩)
  have hB := option_affine_bound W R b (by
    intro f hf
    have hh := GeneralPaperAffineValuePrice.coefficients hD hE f (hb f hf)
    exact ⟨hh.1.mono hBase,hh.2.mono hBase⟩)
  have short (cost : ℕ) (hc : cost≤72*W+9*model.rat (1+2*R)) :
      fields W [cost,8*W]+128*W≤3*(natBits (1+72*W+9*model.rat (1+2*R))+W)+160*W := by
    have hf := fields_bound W (natBits (1+72*W+9*model.rat (1+2*R))) [cost,8*W] (by
      intro c hh
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl|rfl <;> omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (1+72*W+9*model.rat (1+2*R))+W)+32*W at hf
    omega
  cases a with
  | none =>
    cases b <;> (have hs := short (8*W) (by omega); dsimp only [optionalWindow,GeneralPaperAffineCrossingPrice.optionalRun]; unfold optionalProfile; omega)
  | some f =>
    cases b with
    | none =>
      have hs := short (8*W) (by omega)
      dsimp only [optionalWindow,GeneralPaperAffineCrossingPrice.optionalRun]
      unfold optionalProfile
      omega
    | some g =>
      let root := GeneralPaperAffineCrossingPrice.run model.rat W f g
      let result := GeneralPaperAffineCrossingPrice.optionalRun model.rat W (some f) (some g)
      have hC := crossing_bounded model W D E A B R hD hE hR f g (ha f rfl) (hb g rfl)
      have hw := GeneralPaperAffineCrossingPrice.work model.rat model.monotone W D E A B R hD hE hR f g (ha f rfl) (hb g rfl)
      change root.2≤64*W+9*model.rat (1+2*R) at hw
      have hShape : result.2=root.2+8*W := rfl
      have hf := fields_bound W (natBits (1+72*W+9*model.rat (1+2*R))) [root.2,result.2,8*W] (by
        intro c hh
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
        rcases hh with rfl|rfl|rfl <;> omega)
      change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (1+72*W+9*model.rat (1+2*R))+W)+32*W at hf
      change optionAffineFoot W (some f)+optionAffineFoot W (some g)+
        (crossingWindow model W f g+GeneralPaperEncodedScalarStorage.fields W [root.2,result.2,8*W]+128*W)≤_
      unfold optionalProfile
      omega

end Blotto.GeneralPaperAffineArithmeticStorage
