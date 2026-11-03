import Blotto.PlayerSpecificAlgebraicLoopHeights

/-! Original accepted rational inputs, actual prepared arrays and every
finite branch string share one pathwise contract. This is the resource
phase, prior to terminal coupling, fair-bit laws and allocation rounding. -/
namespace Blotto.PlayerSpecificAlgebraicPathContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
open PlayerSpecificAlgebraicResourceLoop PlayerSpecificAlgebraicResourceLineage
set_option autoImplicit false
set_option maxHeartbeats 2500000

def height (N L : ℕ) : ℕ := 3*(PlayerSpecificInitialLineageBound.height N L+1)

theorem height_profile (N L : ℕ) :
    PlayerSpecificAlgebraicLoopHeights.storedHeight N (PlayerSpecificAlgebraicInitialInputSizes.height N L)≤height N L := by
  have h:=PlayerSpecificInitialLineageBound.profile PlayerSpecificInitialPositivePrecision.initialCoefficient N L _
    (PlayerSpecificAlgebraicInitialInputSizes.polynomial_height N L)
  exact Nat.mul_le_mul_left 3 (Nat.add_le_add_right h 1)

def drawPath {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (player : Bool) (choices : List Bool) : State N × ℕ :=
  run RationalCostModel.schoolbook p (N-1) (start RationalCostModel.schoolbook p player) choices

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
      ∀ (player : Bool) (choices : List Bool),
        let result:=drawPath p player choices
        Valid p x result.1 ∧ InBox (lengths p x) (eval result.1 x) ∧
          (∑ j,eval result.1 x j)=(if player then 2 else 2*(i.budget:ℝ)) ∧
          result.2≤N-1 ∧ result.1.active.length≤1 ∧
          Nonempty (Certificate p player result.1) ∧
          (∀ k,HasHeight (result.1.data.read k) (height N (PlayerSpecificInitialPositivePrecision.inputSize i))) := by
  let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
  obtain ⟨x,hx,_,hred,hbox,hA,hB⟩:=PlayerSpecificAlgebraicInitialContract.actual_coupling_input i r hr
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hc : Context p x := by
    refine ⟨hs.1,hs.2.1,?_,hx,fun j => (hred j).1⟩
    have hv : (r.root.interval.lo:ℝ)<r.root.interval.hi := lt_of_lt_of_le hx.2.1.1 hx.2.1.2
    exact_mod_cast hv
  let H:=PlayerSpecificAlgebraicInitialInputSizes.height N (PlayerSpecificInitialPositivePrecision.inputSize i)
  have hsize:=(PlayerSpecificAlgebraicInitialInputSizes.actual_sizes i r hr).2
  refine ⟨x,hx,?_⟩
  intro player choices
  have hv : ∀ j,Reduced p.parameters.root.polynomial (PlayerSpecificInitialLineageBound.means p player j) ∧
      HasHeight (PlayerSpecificInitialLineageBound.means p player j) H := by
    intro j
    cases player
    · exact ⟨(hred j).2.2,(hsize j).2.2⟩
    · exact ⟨(hred j).2.1,(hsize j).2.1⟩
  have hL : ∀ j,Reduced p.parameters.root.polynomial (p.rows.read j).length ∧ HasHeight (p.rows.read j).length H :=
    fun j => ⟨(hred j).1,(hsize j).1⟩
  have hb : InBox (lengths p x) (eval (start RationalCostModel.schoolbook p player) x) := by
    intro j
    change 0≤realEvaluate ((start RationalCostModel.schoolbook p player).data.read j) x ∧
      realEvaluate ((start RationalCostModel.schoolbook p player).data.read j) x≤realEvaluate (p.rows.read j).length x
    rw [start_read]
    cases player
    · exact (hbox j).2.2
    · exact (hbox j).2.1
  have hsum : (∑ j,eval (start RationalCostModel.schoolbook p player) x j)=(if player then 2 else 2*(i.budget:ℝ)) := by
    cases player
    · simpa only [eval,start_read,PlayerSpecificInitialLineageBound.means,Bool.false_eq_true,ite_false] using hB
    · simpa only [eval,start_read,PlayerSpecificInitialLineageBound.means,ite_true] using hA
  have hstart:=start_valid RationalCostModel.schoolbook p player hc.normalized hc.irreducible hc.interval x hc.root (fun j => (hv j).1)
  let c:=start_certificate RationalCostModel.schoolbook p player
  have ht:=complete_path RationalCostModel.schoolbook p x hc player choices (fun j => (hv j).1) hb
  have hcert:=(PlayerSpecificAlgebraicLoopLineage.invariant RationalCostModel.schoolbook p player x hc (N-1)
    (start RationalCostModel.schoolbook p player) choices hstart c).2
  have hheight:=PlayerSpecificAlgebraicLoopHeights.run_heights RationalCostModel.schoolbook p player x hc (N-1)
    (start RationalCostModel.schoolbook p player) choices hstart c H hv hL (by
      intro j
      rw [start_read]
      apply mono (hv j).2
      have hHA:=PlayerSpecificAlgebraicLoopHeights.leaf_le_active N H (by have h:=j.isLt; omega)
      unfold PlayerSpecificAlgebraicLoopHeights.storedHeight PlayerSpecificAlgebraicPairHeights.resourceHeight
      omega)
  refine ⟨ht.1,ht.2.1,ht.2.2.1.trans hsum,ht.2.2.2.1,ht.2.2.2.2,hcert,?_⟩
  intro j
  exact mono (hheight j) (height_profile N (PlayerSpecificInitialPositivePrecision.inputSize i))

end Blotto.PlayerSpecificAlgebraicPathContract
