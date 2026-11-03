import Blotto.GeneralPaperBasisProductBits
import Blotto.GeneralPaperBasisCacheSize

/-! The retained affine cache is built once with operand-sensitive RHS
copies and two integer matrix/vector products. The original row invariant
discharges all integer bounds; initializer denominators do not enter it. -/
namespace Blotto.GeneralPaperBasisAffineBits
open GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisAffineData
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6000000

def rhsRun {d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (state : State d d) (useSlope : Bool) : Vector d × ℕ :=
  PaperIndexedArrayConstruction.run (fun w => w) W (fun i =>
    let a := if useSlope then (state.rows.read i).slope else (state.rows.read i).constant
    (a,16*W+primitive (GeneralPaperIntegerPrimitivePrice.word a)))

theorem rhs_data {d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (state : State d d) (useSlope : Bool) :
    (rhsRun primitive W state useSlope).1=(GeneralPaperBasisAffineData.rhsRun state useSlope).1 := by
  simp only [rhsRun,GeneralPaperBasisAffineData.rhsRun,PaperIndexedArrayConstruction.run_data]

def prepare {d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (state : State d d) : Data d :=
  let c := rhsRun primitive W state false
  let s := rhsRun primitive W state true
  let ac := GeneralPaperBasisProductBits.mulVecRun primitive W state.adjugate c.1
  let bs := GeneralPaperBasisProductBits.mulVecRun primitive W state.adjugate s.1
  ⟨ac.1,bs.1,state.determinant,c.2+s.2+ac.2+bs.2+16*W+
    primitive (GeneralPaperIntegerPrimitivePrice.word state.determinant)⟩

theorem constant {d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (state : State d d) :
    (prepare primitive W state).constant=(GeneralPaperBasisAffineData.prepare state).constant := by
  simp only [prepare,GeneralPaperBasisAffineData.prepare,GeneralPaperBasisProductBits.mulVec_data,rhs_data]

theorem slope {d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (state : State d d) :
    (prepare primitive W state).slope=(GeneralPaperBasisAffineData.prepare state).slope := by
  simp only [prepare,GeneralPaperBasisAffineData.prepare,GeneralPaperBasisProductBits.mulVec_data,rhs_data]

theorem determinant {d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (state : State d d) :
    (prepare primitive W state).determinant=state.determinant := rfl

def width (d H C : ℕ) : ℕ :=
  1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap d H C)+binaryWordWidth C+binaryWordWidth H

theorem rhs_work {d : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W C : ℕ)
    (hW : 1≤W) (hD : binaryWordWidth (d+1)≤W) (state : State d d) (useSlope : Bool)
    (hc : ∀ i,(if useSlope then (state.rows.read i).slope else (state.rows.read i).constant).natAbs≤C) :
    (rhsRun primitive W state useSlope).2≤128*(d+1)*(W+primitive (1+binaryWordWidth C)) := by
  let Q := primitive (1+binaryWordWidth C)
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => Nat.add_le_add_left
    (hMono (GeneralPaperIntegerPrimitivePrice.word_bound _ C (hc i))) (16*W))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fun i : Fin d => ((if useSlope then (state.rows.read i).slope else (state.rows.read i).constant),
      16*W+primitive (GeneralPaperIntegerPrimitivePrice.word
        (if useSlope then (state.rows.read i).slope else (state.rows.read i).constant))))
  change (rhsRun primitive W state useSlope).2≤_ at hh
  have ho : 6*W+10*1*binaryWordWidth (d+1)+28≤44*W := by omega
  have hO := Nat.mul_le_mul_left (d+1) ho
  change _≤d*(16*W+Q) at hs
  change _≤128*(d+1)*(W+Q)
  nlinarith only [hh,hs,hO,Nat.zero_le (d*W),Nat.zero_le (d*Q)]

theorem work {d : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W H C : ℕ)
    (hW : 1≤W) (hD : binaryWordWidth (d+1)≤W) (state : State d d)
    (hAdj : ∀ i j,((state.adjugate.read i).read j).natAbs≤H)
    (hDet : state.determinant.natAbs≤H)
    (hConstant : ∀ i,(state.rows.read i).constant.natAbs≤C)
    (hSlope : ∀ i,(state.rows.read i).slope.natAbs≤C) :
    (prepare primitive W state).work≤2048*(d+1)^2*(W+primitive (width d H C)) := by
  let Q := primitive (width d H C)
  have hpC := hMono (show 1+binaryWordWidth C≤width d H C by unfold width; omega)
  have hpP := hMono (show 1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap d H C)≤width d H C by unfold width; omega)
  have hpH := hMono ((GeneralPaperIntegerPrimitivePrice.word_bound _ H hDet).trans
    (show 1+binaryWordWidth H≤width d H C by unfold width; omega))
  have hc := (rhs_work primitive hMono W C hW hD state false hConstant).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left hpC W))
  have hs := (rhs_work primitive hMono W C hW hD state true hSlope).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left hpC W))
  have hrC (i : Fin d) : ((rhsRun primitive W state false).1.read i).natAbs≤C := by
    rw [rhs_data,GeneralPaperBasisAffineData.rhs_read]; exact hConstant i
  have hrS (i : Fin d) : ((rhsRun primitive W state true).1.read i).natAbs≤C := by
    rw [rhs_data,GeneralPaperBasisAffineData.rhs_read]; exact hSlope i
  have ha := (GeneralPaperBasisProductBits.mulVec_work primitive hMono W H C hW hD state.adjugate
    (rhsRun primitive W state false).1 hAdj hrC).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hpP W))
  have hb := (GeneralPaperBasisProductBits.mulVec_work primitive hMono W H C hW hD state.adjugate
    (rhsRun primitive W state true).1 hAdj hrS).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hpP W))
  change _≤2048*(d+1)^2*(W+Q)
  change (rhsRun primitive W state false).2+(rhsRun primitive W state true).2+
    (GeneralPaperBasisProductBits.mulVecRun primitive W state.adjugate (rhsRun primitive W state false).1).2+
    (GeneralPaperBasisProductBits.mulVecRun primitive W state.adjugate (rhsRun primitive W state true).1).2+
    16*W+primitive (GeneralPaperIntegerPrimitivePrice.word state.determinant)≤_
  nlinarith only [hc,hs,ha,hb,hpH,Nat.zero_le (d*W),Nat.zero_le (d*Q),Nat.zero_le (d^2*W),Nat.zero_le (d^2*Q)]

theorem invariant_work {T m K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W : ℕ)
    (hW : 1≤W) (hD : binaryWordWidth (m*(K-1)+1)≤W) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (S h N : ℕ)
    (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : GeneralPaperBasisInvariant.Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) :
    (prepare primitive W state).work≤2048*(m*(K-1)+1)^2*
      (W+primitive (width (m*(K-1)) ((m+1)^(m*(K-1))) (m+1))) :=
  work primitive hMono W _ _ hW hD state
    (GeneralPaperBasisCacheSize.adjugate hm dict v S h N betaN initialGrid (Nat.le_refl _) state inv)
    (GeneralPaperBasisCacheSize.determinant hm dict v S h N betaN initialGrid (Nat.le_refl _) state inv)
    (GeneralPaperBasisRowSize.rhs_entry hm dict v S h N betaN initialGrid (Nat.le_refl _) state inv · false)
    (GeneralPaperBasisRowSize.rhs_entry hm dict v S h N betaN initialGrid (Nat.le_refl _) state inv · true)

theorem invariant_output {T m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (S h N : ℕ)
    (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : GeneralPaperBasisInvariant.Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) :
    (prepare primitive W state).determinant.natAbs≤(m+1)^(m*(K-1)) ∧
      ∀ i,((prepare primitive W state).constant.read i).natAbs≤(m+1)^(m*(K-1)) ∧
        ((prepare primitive W state).slope.read i).natAbs≤(m+1)^(m*(K-1)) := by
  refine ⟨GeneralPaperBasisCacheSize.determinant hm dict v S h N betaN initialGrid (Nat.le_refl _) state inv,?_⟩
  intro i
  rw [constant,slope]
  exact GeneralPaperBasisCacheSize.affine_products hm dict v S h N betaN initialGrid state inv i

end Blotto.GeneralPaperBasisAffineBits
