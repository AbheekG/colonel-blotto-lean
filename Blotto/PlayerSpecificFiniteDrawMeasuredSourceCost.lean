import Blotto.PlayerSpecificFiniteDrawMeasuredExecution

/-! From an accepted rational input, the same finite packet pays for its
two address slices, the measured resource entry, and the reached measured
original-coordinate terminal leaf. The returned algebraic array equals
the native finite draw on every packet. -/
namespace Blotto.PlayerSpecificFiniteDrawMeasuredSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work {N : ℕ} (i : RationalPlayerSpecificInput N) (H K : ℕ) : ℕ :=
  2*PlayerSpecificBitSlicePolynomial.coefficient*
    (PlayerSpecificAlgebraicFiniteDraw.bitCount N H K+1)^3+
  PlayerSpecificResourceEntryPriceProfile.coefficient*(N+1)^7*
    (PlayerSpecificInitialPositivePrecision.inputSize i+H+1)^3+
  PlayerSpecificTerminalLeafMeasuredSourceCost.work N
    (PlayerSpecificResourceEntryInput.height N (PlayerSpecificInitialPositivePrecision.inputSize i)) H K+2

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N)
    (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∀ (player : Bool) (H K : ℕ)
      (bits : Fin (PlayerSpecificAlgebraicFiniteDraw.bitCount N H K) → Bool),
      (PlayerSpecificFiniteDrawMeasuredExecution.run p i.budget player H K bits).1 =
        PlayerSpecificAlgebraicFiniteDraw.draw p i.budget player H K bits ∧
      (PlayerSpecificFiniteDrawMeasuredExecution.run p i.budget player H K bits).2≤work i H K := by
  dsimp only
  let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
  let model:=RationalCostModel.schoolbook
  let L:=PlayerSpecificInitialPositivePrecision.inputSize i
  let T:=PlayerSpecificResourceEntryInput.height N L
  obtain ⟨x,hx,hc,hml,hroot,hends,hsize,_,_⟩:=PlayerSpecificResourceEntryInput.original_input i r hr
  obtain ⟨z,hz,hpaths⟩:=PlayerSpecificFiniteResourceContract.original_input i r hr
  have hez : z=x := hx.2.2 z hz.1 hz.2.1
  subst z
  obtain ⟨w,hw,_,_,hinit,_,_⟩:=PlayerSpecificAlgebraicInitialContract.actual_coupling_input i r hr
  have hew : w=x := hx.2.2 w hw.1 hw.2.1
  subst w
  have hTL : L≤T := by
    dsimp [T,PlayerSpecificResourceEntryInput.height,PlayerSpecificOriginalResourceSourceCost.size,
      PlayerSpecificAlgebraicFiniteDrawContract.base]
    omega
  have hRT : PlayerSpecificAlgebraicPathContract.height N L≤T := by
    dsimp [T,PlayerSpecificResourceEntryInput.height,PlayerSpecificOriginalResourceSourceCost.size,
      PlayerSpecificAlgebraicFiniteDrawContract.base]
    omega
  have hT : 2≤T := by
    dsimp [T,PlayerSpecificResourceEntryInput.height,PlayerSpecificOriginalResourceSourceCost.size,
      PlayerSpecificAlgebraicFiniteDrawContract.base]
    omega
  intro player H K bits
  let R:=(N-1)*H
  let F:=PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K
  let M:=PlayerSpecificAlgebraicFiniteDraw.bitCount N H K
  let first:=PlayerSpecificBitSliceExecution.run model (R+F) 0 R (by omega) bits
  let second:=PlayerSpecificBitSliceExecution.run model (R+F) R F (Nat.le_refl _) bits
  let resource:=PlayerSpecificFiniteResourceEntryExecution.draw p player H first.1
  let s:=(PlayerSpecificFiniteResourceLoop.draw p player H first.1).1
  let b:ℚ:=if player then 1 else i.budget
  let leaf:=PlayerSpecificTerminalLeafMeasuredExecution.run p resource.1.1 b H K second.1
  have hfirst:=PlayerSpecificBitSlicePolynomial.cost M 0 R (by dsimp [M,PlayerSpecificAlgebraicFiniteDraw.bitCount,R,F]; omega) bits
  have hsecond:=PlayerSpecificBitSlicePolynomial.cost M R F (by
    dsimp [M,PlayerSpecificAlgebraicFiniteDraw.bitCount,R,F]
    omega) bits
  have hresource:=PlayerSpecificFiniteResourceEntryCost.original_input i r hr player H first.1
  have hpath:=hpaths player H first.1
  have hB : 0<b := by cases player; exact i.budget_pos; exact zero_lt_one
  have hBH : RationalHeight b T := by
    cases player
    · exact (PlayerSpecificRecognitionInputHeights.original_fields i).1.mono hTL
    · exact one_height.mono (by omega)
  have hends' : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] T := hends
  have heB : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi,b] T := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|hq|hq
    · rw [hq]; exact hends' _ (by simp)
    · rw [hq]; exact hends' _ (by simp)
    · rw [hq]; exact hBH
  have hL : ∀ j,0<lengths p x j ∧ lengths p x j≤(b:ℝ) := by
    intro j
    refine ⟨(hinit j).1.1,?_⟩
    cases player
    · exact (hinit j).1.2
    · exact (hinit j).1.2.trans (by exact_mod_cast i.budget_le)
  have hmass : (∑ j,eval s x j)=2*(b:ℝ) := by
    cases player
    · exact hpath.2.2.1
    · simpa [b] using hpath.2.2.1
  have hresourceRows : ∀ j,HasHeight (s.data.read j) T :=
    fun j => mono (hpath.2.2.2.2.2.2 j) hRT
  have hleaf : leaf.2≤PlayerSpecificTerminalLeafMeasuredSourceCost.work N T H K := by
    dsimp only [leaf]
    rw [PlayerSpecificFiniteResourceEntryExecution.value]
    exact PlayerSpecificTerminalLeafMeasuredSourceCost.cost p s b x hc hpath.1 hB hL
      hpath.2.1 hmass hpath.2.2.2.2.1 T hroot hml heB hBH hsize hresourceRows hT H K second.1
  have hslices : first.2+second.2≤2*PlayerSpecificBitSlicePolynomial.coefficient*(M+1)^3 := by
    have hsum := Nat.add_le_add hfirst hsecond
    exact hsum.trans_eq (by ring)
  refine ⟨PlayerSpecificFiniteDrawMeasuredExecution.value p i.budget player H K bits,?_⟩
  change first.2+second.2+resource.2+leaf.2+price model [.control 1]≤_
  rw [show price model [.control 1]=2 by rfl]
  have hsum:=Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hslices hresource) hleaf) 2
  exact hsum

theorem original_input_full_budget_and_cost {N : ℕ} (i : RationalPlayerSpecificInput N)
    (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
      ∀ (player : Bool) (H K : ℕ)
        (bits : Fin (PlayerSpecificAlgebraicFiniteDraw.bitCount N H K) → Bool),
        FullBudget (if player then 1 else (i.budget:ℝ))
          (values (PlayerSpecificFiniteDrawMeasuredExecution.run p i.budget player H K bits).1 x) ∧
        (PlayerSpecificFiniteDrawMeasuredExecution.run p i.budget player H K bits).2≤work i H K := by
  dsimp only
  obtain ⟨x,hx,hpath⟩:=PlayerSpecificAlgebraicFiniteDrawContract.original_input i r hr
  refine ⟨x,hx,?_⟩
  intro player H K bits
  have h:=original_input i r hr player H K bits
  rw [h.1]
  exact ⟨(hpath player H K bits).1,h.2⟩

end Blotto.PlayerSpecificFiniteDrawMeasuredSourceCost
