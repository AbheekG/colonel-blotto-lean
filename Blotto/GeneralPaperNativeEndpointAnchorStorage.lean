import Blotto.GeneralPaperSourceCompilerBranchReachedRates

/-! Actual endpoint-anchor read and offset arithmetic. Borrowed packed
point ownership remains with the caller. Five constant-count integer
primitive prices bound scratch; no traversal price is used as scratch. -/
namespace Blotto.GeneralPaperNativeEndpointAnchorStorage
open GeneralPaperEncodedScalarStorage GeneralPaperSourceEndpointBranch
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384

def zero {d : ℕ} : Choice d → Bool
  | .zero => true
  | .endpoint _ _ => false

def callbackPrice (model : RationalCostModel) (W m K : ℕ) : ℕ :=
  9*model.rat (GeneralPaperNativeEndpointAnchor.width m K)+128*W
def scalarCap (model : RationalCostModel) (W m K : ℕ) : ℕ := m*K+K+m+2+callbackPrice model W m K+1

def controls {m K : ℕ} (model : RationalCostModel) (W : ℕ) (choice : Choice (m*(K-1))) (j : Fin m) (l : Fin K) : List ℕ :=
  let test := GeneralPaperIntegerWordPrice.compare model.rat l.val 0
  let stride := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a-b) K 1
  let label := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a-b) l.val 1
  let product := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) j.val (K-1)
  let offset := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (j.val*(K-1)) (l.val-1)
  [m,K,j.val,l.val,K-1,l.val-1,j.val*(K-1),j.val*(K-1)+(l.val-1),test,stride,label,product,offset,
    (GeneralPaperNativeEndpointAnchor.run model.rat W choice j l).2,128*W,
    test+stride,test+stride+label,test+stride+label+product,test+stride+label+product+offset,
    GeneralPaperFinalStaticLoopStorage.bit (decide (l.val=0)),GeneralPaperFinalStaticLoopStorage.bit (zero choice)]

def scratch {m K : ℕ} (model : RationalCostModel) (choice : Choice (m*(K-1))) (l : Fin K) (j : Fin m) : ℕ :=
  if zero choice then 0 else
    GeneralPaperIntegerWordPrice.compare model.rat l.val 0+
      if l.val=0 then 0 else
        GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a-b) K 1+
        GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a-b) l.val 1+
        GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) j.val (K-1)+
        GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (j.val*(K-1)) (l.val-1)

def window {m K : ℕ} (model : RationalCostModel) (W : ℕ) (choice : Choice (m*(K-1))) (j : Fin m) (l : Fin K) : ℕ :=
  rationalWordWidth (GeneralPaperNativeEndpointAnchor.run model.rat W choice j l).1+scratch model choice l j+
    fields W (controls model W choice j l)+128*W

def profile (model : RationalCostModel) (W m K R : ℕ) : ℕ :=
  R+9*model.rat (GeneralPaperNativeEndpointAnchor.width m K)+21*(natBits (scalarCap model W m K)+W)+160*W

theorem array_entry {d : ℕ} (W : ℕ) (point : GeneralPaperBasisRationalSolve.RatVector d) (i : Fin d) :
    rationalWordWidth (point.read i)≤GeneralPaperEncodedBasisStorage.arrayFootprint W rationalWordWidth point := by
  have h := Finset.single_le_sum (s:=Finset.univ) (f:=fun a : Fin d => W+rationalWordWidth (point.read a))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  unfold GeneralPaperEncodedBasisStorage.arrayFootprint
  omega

theorem entry_word {m K : ℕ} (model : RationalCostModel) (W : ℕ) (choice : Choice (m*(K-1))) (j : Fin m) (l : Fin K) :
    rationalWordWidth (GeneralPaperNativeEndpointAnchor.run model.rat W choice j l).1≤3+GeneralPaperRetainedCompilerBranchStorage.choiceFoot W choice := by
  cases choice with
  | zero => exact (show rationalWordWidth (0:ℚ)=3 by decide).le.trans (by simp only [GeneralPaperRetainedCompilerBranchStorage.choiceFoot];omega)
  | endpoint gamma point =>
    simp only [GeneralPaperNativeEndpointAnchor.run]
    split
    · exact (show rationalWordWidth (0:ℚ)=3 by decide).le.trans (by simp only [GeneralPaperRetainedCompilerBranchStorage.choiceFoot];omega)
    · apply (array_entry W point _).trans
      simp only [GeneralPaperRetainedCompilerBranchStorage.choiceFoot]
      omega

theorem bounded {m K : ℕ} (model : RationalCostModel) (W R : ℕ) (choice : Choice (m*(K-1))) (j : Fin m) (l : Fin K)
    (hValue : rationalWordWidth (GeneralPaperNativeEndpointAnchor.run model.rat W choice j l).1≤R) :
    window model W choice j l≤profile model W m K R := by
  let M := m*K+K+m+2
  have hK : K≤M := by unfold M;omega
  have hM : m≤M := by unfold M;omega
  have hj : j.val≤M := by unfold M;have h:=j.isLt;omega
  have hl : l.val≤M := by unfold M;have h:=l.isLt;omega
  have hOne : 1≤M := by unfold M;omega
  have hStride : K-1≤M := by omega
  have hLabel : l.val-1≤M := by omega
  have hProduct : j.val*(K-1)≤m*K := Nat.mul_le_mul j.isLt.le (Nat.sub_le K 1)
  have hProductM : j.val*(K-1)≤M := by unfold M;omega
  have hOffset : j.val*(K-1)+(l.val-1)≤M := by unfold M;have h:=l.isLt;omega
  have ht := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone l.val 0 (GeneralPaperNativeEndpointAnchor.width m K)
    (Nat.add_le_add_left (binaryWordWidth_mono hl) 1) (Nat.add_le_add_left (binaryWordWidth_mono (Nat.zero_le M)) 1)
  change GeneralPaperIntegerWordPrice.compare model.rat l.val 0≤model.rat (1+binaryWordWidth M) at ht
  have hs := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a-b) K 1 M hK hOne hStride
  have hl' := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a-b) l.val 1 M hl hOne hLabel
  have hm := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b) j.val (K-1) M hj hStride hProductM
  have ha := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b) (j.val*(K-1)) (l.val-1) M hProductM hLabel hOffset
  have hScratch : scratch model choice l j≤9*model.rat (GeneralPaperNativeEndpointAnchor.width m K) := by
    unfold scratch
    split
    · exact Nat.zero_le _
    · split <;> change _≤9*model.rat (1+binaryWordWidth M) <;> omega
  have hWork := GeneralPaperNativeEndpointAnchor.work model.rat model.monotone W choice j l
  change (GeneralPaperNativeEndpointAnchor.run model.rat W choice j l).2≤9*model.rat (1+binaryWordWidth M)+128*W at hWork
  have hL := GeneralPaperFinalStaticLoopStorage.bit_bound (decide (l.val=0))
  have hZ := GeneralPaperFinalStaticLoopStorage.bit_bound (zero choice)
  have hf := fields_bound W (natBits (scalarCap model W m K)) (controls model W choice j l) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    unfold controls at hz
    dsimp only at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold scalarCap callbackPrice; change _≤M+(9*model.rat (1+binaryWordWidth M)+128*W)+1;omega)
  change fields W _≤21*(natBits (scalarCap model W m K)+W)+32*W at hf
  unfold window profile
  omega

end Blotto.GeneralPaperNativeEndpointAnchorStorage
