import Blotto.PlayerSpecificRationalPrecisionSourceCost
import Blotto.PlayerSpecificFiniteAccuracyExecution

/-! All three computed scalar/coin/output precision calls have one
schoolbook source bound, including the coin scale, final sum, and metadata. -/
namespace Blotto.PlayerSpecificFiniteAccuracySourceCost
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def scale (N : ℕ) : ℕ := 32*(N+1000)
def size (N s : ℕ) (epsilon : ℚ) : ℕ :=
  s+scale N+PlayerSpecificRationalPrecisionSourceSizes.inputWidth (scale N) epsilon+100
def width (N s : ℕ) (epsilon : ℚ) : ℕ := 4*size N s epsilon+40
def work (N s : ℕ) (epsilon : ℚ) : ℕ :=
  4000*(size N s epsilon+1)*RationalCostModel.schoolbook.rat (width N s epsilon)

theorem cost (N s : ℕ) (epsilon : ℚ) (he : 0<epsilon) :
    (PlayerSpecificFiniteAccuracyExecution.run N s epsilon).2≤work N s epsilon := by
  let model:=RationalCostModel.schoolbook
  let C:=scale N
  let L:=PlayerSpecificRationalPrecisionSourceSizes.inputWidth C epsilon
  let S:=size N s epsilon
  let W:=width N s epsilon
  let R:=model.rat W
  let nplus:=PlayerSpecificNaturalExecution.binary model (fun a b=>a+b) N 1000
  let c:=PlayerSpecificNaturalExecution.binary model (fun a b=>a*b) 32 nplus.1
  let scalar:=PlayerSpecificRationalPrecisionExecution.run 48 epsilon
  let coin:=PlayerSpecificRationalPrecisionExecution.run c.1 epsilon
  let output:=PlayerSpecificRationalPrecisionExecution.run 32 epsilon
  let rounded:=PlayerSpecificNaturalExecution.binary model (fun a b=>a+b) s output.1
  let words:List ℕ:=[N,s,c.1,scalar.1,coin.1,output.1,rounded.1]
  have hC : 0<C := by dsimp [C,scale]; omega
  have hc : c.1=C := by
    simp only [c,nplus,PlayerSpecificNaturalExecution.binary_value,C,scale]
  have hnplus : nplus.1=N+1000 := PlayerSpecificNaturalExecution.binary_value _ _ _ _
  have h48 : PlayerSpecificRationalPrecisionSourceSizes.inputWidth 48 epsilon≤L := by
    have hb:=binaryWordWidth_mono (by dsimp [C,scale]; omega : 48≤C)
    dsimp only [L,PlayerSpecificRationalPrecisionSourceSizes.inputWidth]
    omega
  have h32 : PlayerSpecificRationalPrecisionSourceSizes.inputWidth 32 epsilon≤L := by
    have hb:=binaryWordWidth_mono (by dsimp [C,scale]; omega : 32≤C)
    dsimp only [L,PlayerSpecificRationalPrecisionSourceSizes.inputWidth]
    omega
  have hSshape : S=s+C+L+100 := rfl
  have hLS : L≤S := by omega
  have hsmall : ∀ n≤S,1+binaryWordWidth n≤W := by
    intro n hn
    have hw:=control_width n
    dsimp only [W,width]
    omega
  have hN : N≤S := by
    have hCN : N≤C := by dsimp [C,scale]; omega
    omega
  have hs : s≤S := by omega
  have hC' : C≤S := by omega
  have hn : nplus.1≤S := by
    rw [hnplus]
    have hNC : N+1000≤C := by dsimp [C,scale]; omega
    omega
  have hscalar' : scalar.1≤L+1 := by
    rw [PlayerSpecificRationalPrecisionExecution.value 48 epsilon (by decide) he]
    have hb:=PlayerSpecificRationalPrecisionSourceSizes.precision_bound 48 epsilon (by decide) he
    omega
  have hcoin' : coin.1≤L+1 := by
    dsimp only [coin]
    rw [hc,PlayerSpecificRationalPrecisionExecution.value C epsilon hC he]
    exact PlayerSpecificRationalPrecisionSourceSizes.precision_bound C epsilon hC he
  have houtput' : output.1≤L+1 := by
    rw [PlayerSpecificRationalPrecisionExecution.value 32 epsilon (by decide) he]
    have hb:=PlayerSpecificRationalPrecisionSourceSizes.precision_bound 32 epsilon (by decide) he
    omega
  have hscalar : scalar.1≤S := by
    omega
  have hcoin : coin.1≤S := by omega
  have houtput : output.1≤S := by omega
  have hrounded : rounded.1≤S := by
    rw [PlayerSpecificNaturalExecution.binary_value]
    omega
  have hW : 1≤W := by dsimp [W,width]; omega
  have hWS : S+1≤W := by dsimp [W,width]; omega
  have hnplusCost:=PlayerSpecificNaturalExecution.binary_cost model (fun a b=>a+b)
    N 1000 W (hsmall N hN) (hsmall 1000 (by dsimp [S,size,C,scale]; omega))
    (hsmall (N+1000) (by rw [←hnplus]; exact hn))
  have hcCost:=PlayerSpecificNaturalExecution.binary_cost model (fun a b=>a*b)
    32 nplus.1 W (hsmall 32 (by dsimp [S,size,C,scale]; omega))
    (hsmall nplus.1 hn)
    (by rw [hnplus]; change 1+binaryWordWidth C≤W; exact hsmall C hC')
  have hroundCost:=PlayerSpecificNaturalExecution.binary_cost model (fun a b=>a+b)
    s output.1 W (hsmall s hs) (hsmall output.1 houtput)
    (hsmall _ hrounded)
  have hprecision (D : ℕ) (hD : PlayerSpecificRationalPrecisionSourceSizes.inputWidth D epsilon≤L) :
      (PlayerSpecificRationalPrecisionExecution.run D epsilon).2≤1000*(S+1)*R := by
    have h:=PlayerSpecificRationalPrecisionSourceCost.cost D epsilon
    have hwidth : PlayerSpecificRationalPrecisionSourceSizes.width D epsilon≤W := by
      dsimp only [PlayerSpecificRationalPrecisionSourceSizes.width,W,width]
      omega
    have hr:=model.monotone hwidth
    have hmult:=Nat.mul_le_mul (by omega :
      PlayerSpecificRationalPrecisionSourceSizes.inputWidth D epsilon+1≤S+1) hr
    have hscale:=Nat.mul_le_mul_left 1000 hmult
    have heq : PlayerSpecificRationalPrecisionSourceCost.work D epsilon =
        1000*(PlayerSpecificRationalPrecisionSourceSizes.inputWidth D epsilon+1)*
          model.rat (PlayerSpecificRationalPrecisionSourceSizes.width D epsilon) := rfl
    have hwork : PlayerSpecificRationalPrecisionSourceCost.work D epsilon≤
        1000*(S+1)*R := by
      rw [heq]
      simpa only [mul_assoc] using hscale
    exact h.trans hwork
  have hscalarCost : scalar.2≤1000*(S+1)*R := hprecision 48 h48
  have hcoinCost : coin.2≤1000*(S+1)*R := by
    dsimp only [coin]
    rw [hc]
    exact hprecision C (le_rfl)
  have houtputCost : output.2≤1000*(S+1)*R := hprecision 32 h32
  have hwords : ∀ word∈words,binaryWordWidth word≤W := by
    intro word hw
    simp only [words,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with hw|hw|hw|hw|hw|hw|hw
    · simpa only [hw] using (control_width N).trans (by omega : N+1≤W)
    · simpa only [hw] using (control_width s).trans (by omega : s+1≤W)
    · simpa only [hw] using (control_width c.1).trans (by rw [hc]; omega : c.1+1≤W)
    · simpa only [hw] using (control_width scalar.1).trans (by omega : scalar.1+1≤W)
    · simpa only [hw] using (control_width coin.1).trans (by omega : coin.1+1≤W)
    · simpa only [hw] using (control_width output.1).trans (by omega : output.1+1≤W)
    · simpa only [hw] using (control_width rounded.1).trans (by omega : rounded.1+1≤W)
  have hctrl:=PlayerSpecificAlgebraicCallerFrame.controls_cost model words W hwords hW
  have hctrl' : price model (words.map Event.control)≤21*R := by
    have hl : words.length=7 := rfl
    rw [hl] at hctrl
    norm_num at hctrl
    exact hctrl
  have hcopyFits : Fits W (copyRow [epsilon]) := by
    intro e he0
    simp only [copyRow,List.map_cons,List.map_nil,List.mem_cons,
      List.not_mem_nil,or_false] at he0
    rcases he0 with rfl|rfl
    · exact (control_width 1).trans (by omega)
    · dsimp only [Event.Fits]
      have heW : rationalWordWidth epsilon≤L := by
        dsimp only [L,PlayerSpecificRationalPrecisionSourceSizes.inputWidth]
        omega
      omega
  have hcopy:=price_bound model W hW (copyRow [epsilon]) hcopyFits
  have hcopy' : price model (copyRow [epsilon])≤6*R := by
    simpa only [copyRow,List.length_cons,List.length_map,List.length_nil,
      Nat.reduceAdd,Nat.reduceMul] using hcopy
  have hframe : price model (PlayerSpecificFiniteAccuracyExecution.frame N s epsilon
      c.1 scalar.1 coin.1 output.1 rounded.1)≤27*R := by
    change price model (copyRow [epsilon]++words.map Event.control)≤_
    rw [price_append]
    omega
  change nplus.2+c.2+scalar.2+coin.2+output.2+rounded.2+
    price model (PlayerSpecificFiniteAccuracyExecution.frame N s epsilon
      c.1 scalar.1 coin.1 output.1 rounded.1)≤_
  have hsum:=Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add hnplusCost hcCost) hscalarCost) hcoinCost)
          houtputCost) hroundCost) hframe
  have hshape : 64*R+64*R+1000*(S+1)*R+1000*(S+1)*R+
      1000*(S+1)*R+64*R+27*R≤work N s epsilon := by
    change _≤4000*(S+1)*R
    calc
      _ = (3000*(S+1)+219)*R := by ring
      _ ≤ 4000*(S+1)*R := Nat.mul_le_mul_right R (by omega)
  exact hsum.trans hshape

end Blotto.PlayerSpecificFiniteAccuracySourceCost
