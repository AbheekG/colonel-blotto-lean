import Blotto.GeneralPaperBasisSolveBits

/-! Bit-priced full point/direction assembly and next-column extraction.
Existing rational entries are referenced once; only fresh tail divisions
and prefix negations write new rational payloads. Literal native data agree.
-/
namespace Blotto.GeneralPaperBasisAssemblyBits
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperRationalPrimitivePrice
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 7000000

def pointScalar {j d : ℕ} (primitive : ℕ → ℕ) (W N : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j)
    (initial : Vector d) (k : Fin d) : ℚ × ℕ :=
  if h : k.val<j then (first.read ⟨k.val,h⟩,16*W) else
    ((initial.read k:ℚ)/(N:ℚ),32*W+primitive (rationalWordWidth (initial.read k:ℚ))+
      primitive (rationalWordWidth (N:ℚ))+binary primitive (fun a b => a/b) (initial.read k:ℚ) (N:ℚ))

theorem point_scalar_work {j d : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W N : ℕ)
    (first : GeneralPaperBasisRationalSolve.RatVector j) (initial : Vector d)
    (hGrid : ∀ i,(initial.read i).natAbs≤N) (k : Fin d) :
    (pointScalar primitive W N first initial k).2≤32*W+4*primitive (1+4*binaryWordWidth N) := by
  unfold pointScalar
  split
  · dsimp only; omega
  · dsimp only
    have hn := GeneralPaperBasisDivideBits.nat_height N
    have hu := GeneralPaperBasisStageSize.int_height (initial.read k) N (hGrid k)
    have hv := hu.div hn
    have hN : rationalWordWidth (N:ℚ)≤1+4*binaryWordWidth N := (rationalWordWidth_of_height hn).trans (by omega)
    have hU : rationalWordWidth (initial.read k:ℚ)≤1+4*binaryWordWidth N := (rationalWordWidth_of_height hu).trans (by omega)
    have hV : rationalWordWidth ((initial.read k:ℚ)/(N:ℚ))≤1+4*binaryWordWidth N := (rationalWordWidth_of_height hv).trans (by omega)
    have hcN := hMono hN
    have hcU := hMono hU
    have hd := binary_le primitive hMono (fun a b => a/b) _ _ _ hU hN hV
    omega

def pointRun {j d : ℕ} (primitive : ℕ → ℕ) (W N : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) (initial : Vector d) :
    GeneralPaperBasisRationalSolve.RatVector d × ℕ :=
  PaperIndexedArrayConstruction.run (fun w => w) W (pointScalar primitive W N first initial)

theorem point_data {j d : ℕ} (primitive : ℕ → ℕ) (W N : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) (initial : Vector d) :
    (pointRun primitive W N first initial).1=(GeneralPaperBasisFreshPoint.assemble N first initial).1 := by
  simp only [pointRun,pointScalar,GeneralPaperBasisFreshPoint.assemble,PaperIndexedArrayConstruction.run_data]
  congr 1
  funext k
  split <;> rfl

theorem point_work {j d : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W N : ℕ)
    (hW : 1≤W) (hD : binaryWordWidth (d+1)≤W) (first : GeneralPaperBasisRationalSolve.RatVector j)
    (initial : Vector d) (hGrid : ∀ i,(initial.read i).natAbs≤N) :
    (pointRun primitive W N first initial).2≤128*(d+1)*(W+primitive (1+4*binaryWordWidth N)) := by
  have hs := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => point_scalar_work primitive hMono W N first initial hGrid k)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W (pointScalar primitive W N first initial)
  change (pointRun primitive W N first initial).2≤_ at hh
  have hO : 6*W+10*1*binaryWordWidth (d+1)+28≤44*W := by omega
  have ho := Nat.mul_le_mul_left (d+1) hO
  nlinarith only [hs,hh,ho,Nat.zero_le (d*W),Nat.zero_le (d*primitive (1+4*binaryWordWidth N))]

def columnRun {j d : ℕ} (W : ℕ) (rows : Rows j d) (next : Fin d) : Vector j × ℕ :=
  PaperIndexedArrayConstruction.run (fun w => w) W (fun i => ((rows.read i).coefficients.read next,8*W))

theorem column_data {j d : ℕ} (W : ℕ) (rows : Rows j d) (next : Fin d) :
    (columnRun W rows next).1=(GeneralPaperBasisDirection.columnRun rows next).1 := by
  simp only [columnRun,GeneralPaperBasisDirection.columnRun,PaperIndexedArrayConstruction.run_data]

theorem column_work {j d : ℕ} (W : ℕ) (hW : 1≤W) (hJ : binaryWordWidth (j+1)≤W) (rows : Rows j d) (next : Fin d) :
    (columnRun W rows next).2≤64*(j+1)*W := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fun i : Fin j => ((rows.read i).coefficients.read next,8*W))
  change (columnRun W rows next).2≤_ at hh
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hh
  have hO : 6*W+10*1*binaryWordWidth (j+1)+28≤44*W := by omega
  have ho := Nat.mul_le_mul_left (j+1) hO
  nlinarith only [hh,ho,Nat.zero_le (j*W)]

def directionScalar {j d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) (k : Fin d) : ℚ × ℕ :=
  if h : k.val<j then (-(first.read ⟨k.val,h⟩),32*W+unary primitive (fun a => -a) (first.read ⟨k.val,h⟩))
  else if k.val=j then (1,16*W+primitive (rationalWordWidth (1:ℚ)))
  else (0,16*W+primitive (rationalWordWidth (0:ℚ)))

theorem direction_scalar_work {j d : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W s : ℕ) (hs : 1≤s)
    (first : GeneralPaperBasisRationalSolve.RatVector j) (hf : ∀ i,RationalHeight (first.read i) s) (k : Fin d) :
    (directionScalar primitive W first k).2≤32*W+2*primitive (1+2*s) := by
  unfold directionScalar
  split
  · rename_i hk
    dsimp only
    have hf' := hf ⟨k.val,hk⟩
    have hh := unary_le primitive hMono (fun a => -a) (first.read ⟨k.val,hk⟩) (1+2*s)
      (rationalWordWidth_of_height hf') (rationalWordWidth_of_height hf'.neg)
    omega
  · split
    · dsimp only
      have hWord : binaryWordWidth 1≤s := by
        have hw : binaryWordWidth 1=1 := by decide
        omega
      have hOne : RationalHeight (1:ℚ) s := (GeneralPaperBasisDivideBits.nat_height 1).mono hWord
      have hh := hMono (rationalWordWidth_of_height hOne)
      omega
    · dsimp only
      have hZero : RationalHeight (0:ℚ) s := GeneralPaperQuantizedHeight.zero_height s (by omega)
      have hh := hMono (rationalWordWidth_of_height hZero)
      omega

def directionRun {j d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) : GeneralPaperBasisRationalSolve.RatVector d × ℕ :=
  PaperIndexedArrayConstruction.run (fun w => w) W (directionScalar primitive W first)

theorem direction_data {j d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) :
    (directionRun (d:=d) primitive W first).1=(GeneralPaperBasisDirection.assemble (d:=d) first).1 := by
  simp only [directionRun,directionScalar,GeneralPaperBasisDirection.assemble,PaperIndexedArrayConstruction.run_data]
  congr 1
  funext k
  split
  · rfl
  · split <;> rfl

theorem direction_work {j d : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W s : ℕ)
    (hW : 1≤W) (hD : binaryWordWidth (d+1)≤W) (hs : 1≤s)
    (first : GeneralPaperBasisRationalSolve.RatVector j) (hf : ∀ i,RationalHeight (first.read i) s) :
    (directionRun (d:=d) primitive W first).2≤128*(d+1)*(W+primitive (1+2*s)) := by
  have hSum := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => direction_scalar_work primitive hMono W s hs first hf (k : Fin d))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hSum
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W (directionScalar primitive W first : Fin d → ℚ × ℕ)
  change (directionRun (d:=d) primitive W first).2≤_ at hh
  have hO : 6*W+10*1*binaryWordWidth (d+1)+28≤44*W := by omega
  have ho := Nat.mul_le_mul_left (d+1) hO
  nlinarith only [hSum,hh,ho,Nat.zero_le (d*W),Nat.zero_le (d*primitive (1+2*s))]

end Blotto.GeneralPaperBasisAssemblyBits
