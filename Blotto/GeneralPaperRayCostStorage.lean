import Blotto.GeneralPaperRayMinimumStorage

/-! One actual fixed-probe ray-cost evaluation, including its returned
score/cost pair, all five rational operands/results, multiplication/addition
scratch and encoded native work/price/index metadata. Point, direction and
input score matrix are borrowed; no total query-time bound is used as space. -/
namespace Blotto.GeneralPaperRayCostStorage
open RationalOrderCell GeneralPaperRayRationalBound GeneralPaperRayAnchorCosts
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedScoreMatrixStorage
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

def metadataCap (model : RationalCostModel) (W m K S D M : ℕ) : ℕ :=
  m+K+S+1+32*W+4*model.rat (GeneralPaperCommonLatticeDPBits.width D M m)

def window {m K : ℕ} (model : RationalCostModel) (W score : ℕ) (x w : Variable m K → ℚ)
    (t : ℚ) (j : Fin m) (l : Fin K) : ℕ :=
  let a := anchorQ x j l
  let b := anchorQ w j l
  let product := t*b
  let result := GeneralPaperRayCostBits.run model W x w t j l
  let multiply := GeneralPaperRayCostBits.multiplyPrice model t b
  let add := GeneralPaperScoreBitPrimitive.additionPrice model a product
  rationalWordWidth a+rationalWordWidth b+rationalWordWidth t+rationalWordWidth product+rationalWordWidth result.1+
    multiply+add+entryFootprint W (score,result.1)+
    fields W [j.val,l.val,l.val-1,score,24*W,multiply,add,24*W+multiply,result.2,result.2+8*W]+256*W

def profile (model : RationalCostModel) (W m K S D M : ℕ) : ℕ :=
  5*GeneralPaperCommonLatticeDPBits.width D M m+4*model.rat (GeneralPaperCommonLatticeDPBits.width D M m)+
    entryProfile W S (GeneralPaperRayMinimumStorage.height D M)+
    10*(natBits (metadataCap model W m K S D M)+W)+32*W+256*W

theorem bounded {m K : ℕ} (model : RationalCostModel) (W score S D E X V : ℕ) (hs : score≤S)
    (hD : 0<D) (hED : E∣D) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (t : ℚ) (ht : 0≤t ∧ t≤1) (j : Fin m) (l : Fin K) :
    window model W score x w t j l≤profile model W m K S (D*t.den) (X+V+1) := by
  let a := anchorQ x j l
  let b := anchorQ w j l
  let product := t*b
  let result := GeneralPaperRayCostBits.run model W x w t j l
  let multiply := GeneralPaperRayCostBits.multiplyPrice model t b
  let add := GeneralPaperScoreBitPrimitive.additionPrice model a product
  let P := GeneralPaperCommonLatticeDPBits.width (D*t.den) (X+V+1) m
  have hO := GeneralPaperRayCostBits.operands D E X V hED x w hx hw t ht j l
  have hPositive := Nat.mul_pos hD t.den_pos
  have width (q : ℚ) (hq : Bounded (D*t.den) (X+V+1) q) : rationalWordWidth q≤P :=
    GeneralPaperCommonLatticeDPBits.input_width _ _ _ hPositive q hq
  have hA := width _ hO.1
  have hB := width _ hO.2.1
  have hT := width _ hO.2.2.1
  have hProduct := width _ hO.2.2.2.1
  have hResult := width _ hO.2.2.2.2
  have hMultiply := GeneralPaperRayCostBits.multiplyPrice_le model t b P hT hB hProduct
  have hAdd := GeneralPaperScoreBitPrimitive.additionPrice_le model a product P hA hProduct hResult
  have hEntry := entry_bound W S (GeneralPaperRayMinimumStorage.height (D*t.den) (X+V+1))
    (score,result.1) hs (hO.2.2.2.2.height hPositive)
  have hShape : result.2=24*W+multiply+add := rfl
  have hf := fields_bound W (natBits (metadataCap model W m K S (D*t.den) (X+V+1)))
    [j.val,l.val,l.val-1,score,24*W,multiply,add,24*W+multiply,result.2,result.2+8*W] (by
      intro n hn
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; change _≤m+K+S+1+32*W+4*model.rat P; have hj := j.isLt; have hl := l.isLt; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤
    10*(natBits (metadataCap model W m K S (D*t.den) (X+V+1))+W)+32*W at hf
  change rationalWordWidth a≤P at hA
  change rationalWordWidth b≤P at hB
  change rationalWordWidth product≤P at hProduct
  change rationalWordWidth result.1≤P at hResult
  change multiply≤2*model.rat P at hMultiply
  change add≤2*model.rat P at hAdd
  change rationalWordWidth a+rationalWordWidth b+rationalWordWidth t+rationalWordWidth product+rationalWordWidth result.1+
    multiply+add+entryFootprint W (score,result.1)+
    fields W [j.val,l.val,l.val-1,score,24*W,multiply,add,24*W+multiply,result.2,result.2+8*W]+256*W≤_
  unfold profile
  change _≤5*P+4*model.rat P+entryProfile W S (GeneralPaperRayMinimumStorage.height (D*t.den) (X+V+1))+
    10*(natBits (metadataCap model W m K S (D*t.den) (X+V+1))+W)+32*W+256*W
  omega

@[fun_prop]
theorem scaling (model : RationalCostModel) (m K S D M : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model W m K S D M) := by
  unfold profile metadataCap entryProfile
  fun_prop

end Blotto.GeneralPaperRayCostStorage
