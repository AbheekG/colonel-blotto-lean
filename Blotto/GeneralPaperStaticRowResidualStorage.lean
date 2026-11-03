import Blotto.GeneralPaperSparseResidualStorage

/-! Actual native static-row residuals and full sparse-row ownership.
Literal box/order/budget rows supply term/RHS unit caps and lengths; the
caller owns the original dictionary and packed point/direction readers.
Sparse-row construction frames and the outer static scan remain separate. -/
namespace Blotto.GeneralPaperStaticRowResidualStorage
open RationalOrderCell GeneralPaperStaticRayRows GeneralPaperRayUniformSize GeneralPaperRayRationalBound
open GeneralPaperAffineConstraintRows GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
open scoped BigOperators

def variableFoot {m K : ℕ} (W : ℕ) (v : Variable m K) : ℕ := natBits v.1.val+natBits v.2.val+32*W
def termFoot {m K : ℕ} (W : ℕ) (t : Variable m K×ℤ) : ℕ := variableFoot W t.1+GeneralPaperEncodedBasisStorage.integerBits t.2+32*W
def termProfile (W m K : ℕ) : ℕ := 2*natBits (m+K+1)+64*W+2

theorem term_bound {m K : ℕ} (W : ℕ) (t : Variable m K×ℤ) (hc : t.2.natAbs≤1) : termFoot W t≤termProfile W m K := by
  have hm := t.1.1.isLt
  have hK := t.1.2.isLt
  have ha := Nat.add_le_add_left (binaryWordWidth_mono (show t.1.1.val≤m+K+1 by omega)) 1
  have hb := Nat.add_le_add_left (binaryWordWidth_mono (show t.1.2.val≤m+K+1 by omega)) 1
  have hC := binaryWordWidth_mono hc
  have hOne : binaryWordWidth 1=1 := by decide
  unfold termFoot variableFoot termProfile GeneralPaperEncodedBasisStorage.integerBits natBits at *
  omega

def rowFoot {v : Type*} (W : ℕ) (encode : v×ℤ → ℕ) (r : Row v) : ℕ :=
  listFootprint W encode r.terms+GeneralPaperEncodedBasisStorage.integerBits r.constant+GeneralPaperEncodedBasisStorage.integerBits r.slope+32*W

def rowProfile (W m K : ℕ) : ℕ := (m+1)*(termProfile W m K+2*W)+64*W+4

theorem row_bound {T m K : ℕ} (W : ℕ) (hm : 0<m) (labels : Fin T → Fin m → Fin K) (i : StaticIndex T m K) :
    rowFoot W (termFoot W) (row labels i)≤rowProfile W m K := by
  have hLen := (GeneralPaperStaticRowPrice.row_length labels i).trans (GeneralPaperStaticRowPrice.support_bound hm i)
  have hList := (list_bound W (termProfile W m K) (termFoot W) (row labels i).terms
    (fun t ht => term_bound W t (GeneralPaperStaticRowPrice.unit_terms labels i t ht))).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) _)
  have hConst := binaryWordWidth_mono (GeneralPaperStaticRowPrice.constant_unit labels i)
  have hSlope := binaryWordWidth_mono (GeneralPaperAffineConstraintRows.rhs_unit labels (fun _ _ => 0) 0 (embed i)).2
  have hOne : binaryWordWidth 1=1 := by decide
  change binaryWordWidth (row labels i).slope.natAbs≤_ at hSlope
  unfold rowFoot rowProfile GeneralPaperEncodedBasisStorage.integerBits
  omega

def generationCap (m : ℕ) : ℕ := 16*m+32

theorem generation_bound {T m K : ℕ} (i : StaticIndex T m K) : GeneralPaperStaticRayScan.generation i≤generationCap m := by
  rcases i with v|v|i <;> dsimp only [GeneralPaperStaticRayScan.generation,generationCap] <;> omega

def metadataCap (model : RationalCostModel) (W m R : ℕ) : ℕ :=
  1+2*GeneralPaperSparseResidualStorage.price model W (m+1) R+generationCap m+generationCap m*W

def window {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (x w : Variable m K → ℚ) (i : StaticIndex T m K) : ℕ :=
  let r := row labels i
  let residual := GeneralPaperSparseResidualPrice.evaluate model.rat W r x w
  let result := GeneralPaperStaticRowPrice.evaluate model.rat W labels x w i
  rowFoot W (termFoot W) r+GeneralPaperSparseResidualStorage.window model W r x w+
    fields W [residual.2,GeneralPaperStaticRayScan.generation i,GeneralPaperStaticRayScan.generation i*W,result.2]+128*W

def profile (model : RationalCostModel) (W m K R : ℕ) : ℕ :=
  rowProfile W m K+GeneralPaperSparseResidualStorage.profile model W (m+1) R+4*(natBits (metadataCap model W m R)+W)+160*W

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ) (hm : 0<m) (hD : 0<D) (hE : 0<E)
    (labels : Fin T → Fin m → Fin K) (x w : Variable m K → ℚ)
    (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j)) (i : StaticIndex T m K) :
    window model W labels x w i≤profile model W m K (width D E m X V P) := by
  let R := width D E m X V P
  let A := interceptCap m X P
  let B := slopeCap m V
  let r := row labels i
  let residual := GeneralPaperSparseResidualPrice.evaluate model.rat W r x w
  let result := GeneralPaperStaticRowPrice.evaluate model.rat W labels x w i
  have hLen := (GeneralPaperStaticRowPrice.row_length labels i).trans (GeneralPaperStaticRowPrice.support_bound hm i)
  have hX : X≤A := by unfold A interceptCap; nlinarith
  have hV : V≤B := by unfold B slopeCap; nlinarith
  have hU : 1≤A := by unfold A interceptCap; nlinarith
  have hMassX : r.terms.length*X+1≤A := by have h := Nat.mul_le_mul_right X hLen; unfold A interceptCap; nlinarith
  have hMassV : r.terms.length*V≤B := by have h := Nat.mul_le_mul_right V hLen; unfold B slopeCap; nlinarith
  have hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R :=
    GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hResidual := GeneralPaperSparseResidualStorage.bounded model W D E X V A B R (m+1) hD hE hU hX hV hR r x w hx hw hLen
    (GeneralPaperStaticRowPrice.unit_terms labels i) (GeneralPaperStaticRowPrice.constant_unit labels i) hMassX hMassV
  have hRow := row_bound W hm labels i
  have hWork := (GeneralPaperSparseResidualPrice.work model.rat model.monotone W D E X V A B R hD hE hU hX hV hR r x w hx hw
    (GeneralPaperStaticRowPrice.unit_terms labels i) (GeneralPaperStaticRowPrice.constant_unit labels i) hMassX hMassV).trans
      (show r.terms.length*(48*W+9*model.rat (1+2*R))+26*W+3*model.rat (1+2*R)≤GeneralPaperSparseResidualStorage.price model W (m+1) R by
        unfold GeneralPaperSparseResidualStorage.price; gcongr)
  change residual.2≤GeneralPaperSparseResidualStorage.price model W (m+1) R at hWork
  have hGeneration := generation_bound i
  have hGenW := Nat.mul_le_mul_right W hGeneration
  have hShape : result.2=residual.2+GeneralPaperStaticRayScan.generation i*W := rfl
  have hf := fields_bound W (natBits (metadataCap model W m R))
    [residual.2,GeneralPaperStaticRayScan.generation i,GeneralPaperStaticRayScan.generation i*W,result.2] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (metadataCap model W m R)+W)+32*W at hf
  change rowFoot W (termFoot W) r+GeneralPaperSparseResidualStorage.window model W r x w+
    GeneralPaperEncodedScalarStorage.fields W [residual.2,GeneralPaperStaticRayScan.generation i,GeneralPaperStaticRayScan.generation i*W,result.2]+128*W≤_
  change rowFoot W (termFoot W) r≤rowProfile W m K at hRow
  unfold profile
  dsimp only [R] at hResidual hf
  omega

end Blotto.GeneralPaperStaticRowResidualStorage
