import Blotto.PlayerSpecificAlgebraicFiniteDraw

/-! Every accepted original rational input has one selected real root at
which every actual finite-bit allocation is feasible with full spending,
and every output field row has an original-input coefficient-size bound. -/
namespace Blotto.PlayerSpecificAlgebraicFiniteDrawContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicFiniteDraw PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def base (N L : ℕ) : ℕ := PlayerSpecificFiniteParameterSizes.height N L+
  PlayerSpecificAlgebraicInitialInputSizes.height N L+PlayerSpecificAlgebraicPathContract.height N L+L+2

def height (N L K : ℕ) : ℕ := PlayerSpecificAlgebraicTerminalLeafBounds.height N (base N L) K

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p := PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
      ∀ (player : Bool) (H K : ℕ) (bits : Fin (bitCount N H K) → Bool),
        FullBudget (if player then 1 else (i.budget:ℝ)) (values (draw p i.budget player H K bits) x) ∧
          ∀ j,PlayerSpecificAlgebraicReduction.Reduced r.root.polynomial ((draw p i.budget player H K bits).read j) ∧
            HasHeight ((draw p i.budget player H K bits).read j) (height N (PlayerSpecificInitialPositivePrecision.inputSize i) K) := by
  let p := PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
  obtain ⟨x,hx,_,hred,hinit,_,_⟩ := PlayerSpecificAlgebraicInitialContract.actual_coupling_input i r hr
  obtain ⟨z,hz,hpaths⟩ := PlayerSpecificFiniteResourceContract.original_input i r hr
  have he : z=x := hx.2.2 z hz.1 hz.2.1
  subst z
  have hs := PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hroot0 := (PlayerSpecificFiniteParameterDescriptionContract.accepted_sizes i r hr).1
  have hsize0 := (PlayerSpecificAlgebraicInitialInputSizes.actual_sizes i r hr).2
  let L := PlayerSpecificInitialPositivePrecision.inputSize i
  let T := base N L
  have hFT : PlayerSpecificFiniteParameterSizes.height N L ≤ T := by dsimp [T,base]; omega
  have hIT : PlayerSpecificAlgebraicInitialInputSizes.height N L ≤ T := by dsimp [T,base]; omega
  have hRT : PlayerSpecificAlgebraicPathContract.height N L ≤ T := by dsimp [T,base]; omega
  have hLT : L ≤ T := by dsimp [T,base]; omega
  have hT : 1 ≤ T := by dsimp [T,base]; omega
  have hc : PlayerSpecificAlgebraicResourceLoop.Context p x := by
    refine ⟨hs.1,hs.2.1,?_,hx,fun j => (hred j).1⟩
    have hv : (r.root.interval.lo:ℝ) < r.root.interval.hi := lt_of_lt_of_le hx.2.1.1 hx.2.1.2
    exact_mod_cast hv
  have hroot : HasHeight p.parameters.root.polynomial T := PlayerSpecificPolynomialHeights.mono hroot0 hFT
  have hsize : ∀ j,HasHeight (p.rows.read j).length T := fun j => PlayerSpecificPolynomialHeights.mono (hsize0 j).1 hIT
  refine ⟨x,hx,?_⟩
  intro player H K bits
  let s := (PlayerSpecificFiniteResourceLoop.draw p player H (resourceBits N H K bits)).1
  let b : ℚ := if player then 1 else i.budget
  have hpath := hpaths player H (resourceBits N H K bits)
  have hpos : 0 < b := by cases player; exact i.budget_pos; exact zero_lt_one
  have hBH : RationalHeight b T := by
    cases player
    · exact (PlayerSpecificRecognitionInputHeights.original_fields i).1.mono hLT
    · exact one_height.mono hT
  have hL : ∀ j,0 < lengths p x j ∧ lengths p x j ≤ (b:ℝ) := by
    intro j
    refine ⟨(hinit j).1.1,?_⟩
    cases player
    · exact (hinit j).1.2
    · exact (hinit j).1.2.trans (by exact_mod_cast i.budget_le)
  have hmass : (∑ j,eval s x j)=2*(b:ℝ) := by
    cases player
    · exact hpath.2.2.1
    · simpa [b] using hpath.2.2.1
  have hresource : ∀ j,HasHeight (s.data.read j) T :=
    fun j => PlayerSpecificPolynomialHeights.mono (hpath.2.2.2.2.2.2 j) hRT
  have hbudget := PlayerSpecificAlgebraicTerminalLeafExecution.every_path p s b x hc hpath.1 hpos hL
    hpath.2.1 hmass hpath.2.2.2.2.1 T hroot hs.2.2.1 hBH hsize hresource H K (terminalBits N H K bits)
  have hbounds := PlayerSpecificAlgebraicTerminalLeafBounds.bounds p s b x hc hpath.1 hpos hL
    hpath.2.1 hmass hpath.2.2.2.2.1 T hroot hs.2.2.1 hBH hsize hresource H K (terminalBits N H K bits)
  have hcast : (b:ℝ)=(if player then 1 else (i.budget:ℝ)) := by cases player <;> simp [b]
  rw [hcast] at hbudget
  exact ⟨hbudget,hbounds⟩

end Blotto.PlayerSpecificAlgebraicFiniteDrawContract
