import Blotto.PlayerSpecificTerminalCoreInputExecution

/-! Complete source price for converting retained terminal groups to the
six-field core input, with a quotient only when a fractional row exists. -/
namespace Blotto.PlayerSpecificTerminalCoreInputSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicTerminalPreparation
open PlayerSpecificAlgebraicTerminalCoreInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def extraWork (T U N : ℕ) : ℕ :=
  2*(8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(T+1)^3+
  (2618*PlayerSpecificResourceCostProfile.rationalCoefficient)*(U+N+7)^3+2

theorem result_rows_bounds (root : Candidate) (a : Input) (U : ℕ)
    (hm0 : root.polynomial ≠ [])
    (ha : PlayerSpecificAlgebraicTerminalCoreFits.Fits root a U) :
    ∀ j,Reduced root.polynomial ((PlayerSpecificTerminalCoreInputExecution.resultRows a).read j) ∧
      HasHeight ((PlayerSpecificTerminalCoreInputExecution.resultRows a).read j) U := by
  intro j
  fin_cases j
  · simpa [PlayerSpecificTerminalCoreInputExecution.resultRows,FixedArrayTable.read_ofFn] using ha.budget
  · simpa [PlayerSpecificTerminalCoreInputExecution.resultRows,FixedArrayTable.read_ofFn] using ha.lengths 0
  · simpa [PlayerSpecificTerminalCoreInputExecution.resultRows,FixedArrayTable.read_ofFn] using ha.lengths 1
  · simpa [PlayerSpecificTerminalCoreInputExecution.resultRows,FixedArrayTable.read_ofFn] using ha.lengths 2
  · cases hf : a.fractional with
    | none =>
      simp [PlayerSpecificTerminalCoreInputExecution.resultRows,FixedArrayTable.read_ofFn,hf]
      exact ⟨nil_reduced _ hm0,nil_height _⟩
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      simpa [PlayerSpecificTerminalCoreInputExecution.resultRows,FixedArrayTable.read_ofFn,hf] using
        (ha.fractional ell probability hf).1
  · cases hf : a.fractional with
    | none =>
      simp [PlayerSpecificTerminalCoreInputExecution.resultRows,FixedArrayTable.read_ofFn,hf]
      exact ⟨nil_reduced _ hm0,nil_height _⟩
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      simpa [PlayerSpecificTerminalCoreInputExecution.resultRows,FixedArrayTable.read_ofFn,hf] using
        (ha.fractional ell probability hf).2

theorem fromPrepared_cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (g : Prepared N) (T U : ℕ)
    (hm : Normalized p.parameters.root.polynomial) (hm0 : p.parameters.root.polynomial ≠ [])
    (hml : p.parameters.root.polynomial.length ≤ 4)
    (hmT : HasHeight p.parameters.root.polynomial T)
    (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] T)
    (_hv : p.parameters.root.interval.lo < p.parameters.root.interval.hi)
    (hT : 2 ≤ T) (hTU : T ≤ U) (hB : RationalHeight B T)
    (hl : ∀ j,Reduced p.parameters.root.polynomial (p.rows.read j).length ∧
      HasHeight (p.rows.read j).length T)
    (hs : ∀ j,Reduced p.parameters.root.polynomial (s.data.read j) ∧
      HasHeight (s.data.read j) T)
    (hgroups : g.groups.length ≤ N)
    (hfit : PlayerSpecificAlgebraicTerminalCoreFits.Fits p.parameters.root
      (PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g) U) :
    (PlayerSpecificTerminalCoreInputExecution.fromPrepared p s B g).2 ≤ extraWork T U N := by
  let model := RationalCostModel.schoolbook
  let root := p.parameters.root
  let S := U+N+6
  let W := PlayerSpecificAlgebraicComparisonExecution.width S
  let budget := PlayerSpecificFieldCombinationContract.constant root.polynomial B
  let fraction : Option (Data×Data)×ℕ :=
    match g.fractional with
    | none => (none,0)
    | some j =>
      let ell := (p.rows.read j).length
      let divided := PlayerSpecificAlgebraicExpressionExecution.binary model root .divide
        (s.data.read j) ell
      (some (ell,divided.1),divided.2)
  let a : Input := ⟨budget.1,FixedArrayTable.ofFn (fun j =>
    ((g.groups[j.val]?).map (fun h => h.total)).getD []),g.groups.length,fraction.1⟩
  let rows := PlayerSpecificTerminalCoreInputExecution.resultRows a
  have hbudget := PlayerSpecificAlgebraicExpressionPrimitiveCost.constant_cost model root B T
    hm hm0 hml hmT hB (by omega)
  have hbudget' := hbudget.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 T)
  have hfraction : fraction.2 ≤
      (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(T+1)^3 := by
    dsimp only [fraction]
    cases hf : g.fractional with
    | none =>
      simp only
      exact Nat.zero_le _
    | some j =>
      simp only
      have hd := PlayerSpecificAlgebraicExpressionPrimitiveCost.binary_cost model root .divide
        (s.data.read j) (p.rows.read j).length T hm hm0 hml (hs j).1 (hl j).1
        hmT (hs j).2 (hl j).2 (by omega)
      exact hd.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 T)
  have hfitA : PlayerSpecificAlgebraicTerminalCoreFits.Fits root a U := by
    change PlayerSpecificAlgebraicTerminalCoreFits.Fits root
      (PlayerSpecificTerminalCoreInputExecution.fromPrepared p s B g).1 U
    rw [PlayerSpecificTerminalCoreInputExecution.fromPrepared_value]
    exact hfit
  have hrows : ∀ j,Reduced root.polynomial (rows.read j) ∧ HasHeight (rows.read j) U :=
    result_rows_bounds root a U hm0 hfitA
  have hUS : U ≤ S := by dsimp [S]; omega
  have hTS : T ≤ S := hTU.trans hUS
  have hframe := PlayerSpecificExpressionVectorFrameCost.cost model root rows rows S
    (mono hmT hTS) hml (mono he hTS)
    (fun j => ⟨mono (hrows j).2 hUS,by
      have h := (hrows j).1.2
      dsimp only [root] at h
      omega⟩)
    (fun j => ⟨mono (hrows j).2 hUS,by
      have h := (hrows j).1.2
      dsimp only [root] at h
      omega⟩)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hframe' : price model (PlayerSpecificExpressionVectorExecution.frame root rows rows) ≤
      (2600*PlayerSpecificResourceCostProfile.rationalCoefficient)*(S+1)^3 :=
    hframe.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 2600 S)
  let flag := if g.fractional.isSome then 1 else 0
  let words := [N,g.groups.length,flag,0,1,2]
  have hwords : ∀ word ∈ words, binaryWordWidth word ≤ W := by
    intro word hw
    have hsize : word ≤ S := by
      simp only [words,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with h|h|h|h|h|h <;> rw [h]
      · dsimp [S]; omega
      · dsimp [S]; omega
      · dsimp [flag,S]; split <;> omega
      · dsimp [S]; omega
      · dsimp [S]; omega
      · dsimp [S]; omega
    exact (control_width word).trans
      ((Nat.add_le_add_right hsize 1).trans
        (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
  have hc := PlayerSpecificAlgebraicCallerFrame.controls_cost model words W hwords
    (by have h := (PlayerSpecificAlgebraicActiveListCost.width_large S).1; omega)
  have hc' : price model [Event.control N,Event.control g.groups.length,Event.control flag,
      Event.control 0,Event.control 1,Event.control 2] ≤
      (18*PlayerSpecificResourceCostProfile.rationalCoefficient)*(S+1)^3 := by
    change price model (words.map Event.control) ≤ _
    simpa only [words,List.length_cons,List.length_nil] using
      hc.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 18 S)
  change price model budget.2+fraction.2+
    price model (PlayerSpecificTerminalCoreInputExecution.frame root g a)+
    price model [.control 1] ≤ _
  rw [PlayerSpecificTerminalCoreInputExecution.frame,price_append,
    show price model [.control 1]=2 by rfl]
  have hsum := Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add hbudget' hfraction) (Nat.add_le_add hframe' hc')) 2
  apply hsum.trans_eq
  dsimp only [S]
  unfold extraWork
  ring

def work (N T : ℕ) : ℕ :=
  PlayerSpecificTerminalPreparationPolynomial.coefficient*(N+1)^4*(T+1)^3+
  extraWork T (PlayerSpecificAlgebraicTerminalCorePreparationSizes.height N T) N+2

theorem cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0 < B)
    (hL : ∀ k,0 < lengths p x k ∧ lengths p x k ≤ B)
    (hb : InBox (lengths p x) (eval s x))
    (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length ≤ 1)
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T)
    (hml : p.parameters.root.polynomial.length ≤ 4)
    (heB : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi,B] T)
    (hBH : RationalHeight B T)
    (hsize : ∀ k,HasHeight (p.rows.read k).length T)
    (hresource : ∀ k,HasHeight (s.data.read k) T) (hT : 2 ≤ T) :
    (PlayerSpecificTerminalCoreInputExecution.run p s B).2 ≤ work N T := by
  let model := RationalCostModel.schoolbook
  let g := PlayerSpecificTerminalPreparationExecution.run model p s B
  let U := PlayerSpecificAlgebraicTerminalCorePreparationSizes.height N T
  let a := PlayerSpecificTerminalCoreInputExecution.fromPrepared p s B g.1
  have hm0 : p.parameters.root.polynomial ≠ [] := by
    intro hz
    exact hc.irreducible.ne_zero (by rw [hz]; rfl)
  have hactive : s.active.length ≤ N := by
    simpa only [Fintype.card_fin] using hs.nodup.length_le_card
  have hlengths : ∀ j,Reduced p.parameters.root.polynomial (p.rows.read j).length ∧
      HasHeight (p.rows.read j).length T := fun j => ⟨hc.lengths j,hsize j⟩
  have hstate : ∀ j,Reduced p.parameters.root.polynomial (s.data.read j) ∧
      HasHeight (s.data.read j) T := fun j => ⟨hs.reduced j,hresource j⟩
  have hprep := PlayerSpecificTerminalPreparationPolynomial.cost p s B T
    hc.normalized hm0 hml hroot heB hc.interval hlengths hstate hactive
  have hends : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] T := by
    intro q hq
    apply heB
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have hTU : T ≤ U := by
    have h0 : T ≤ ((T+1)*(N+N)+3)+T+1 := by omega
    exact h0.trans ((Nat.le_succ _).trans
      (PlayerSpecificAlgebraicHeightEnvelope.large _))
  have hfit : PlayerSpecificAlgebraicTerminalCoreFits.Fits p.parameters.root
      (PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g.1) U := by
    dsimp only [g]
    rw [PlayerSpecificTerminalPreparationExecution.value]
    exact PlayerSpecificAlgebraicTerminalCorePreparationSizes.fits model p s B x hc hs hB hL hb hmass hend
      T hroot hml hBH hsize hresource
  have hgroups : g.1.groups.length ≤ N :=
    (PlayerSpecificTerminalPreparationExecution.groups_partition model p s B).2
  have hconvert := fromPrepared_cost p s B g.1 T U hc.normalized hm0 hml hroot hends
    hc.interval hT hTU hBH hlengths hstate hgroups hfit
  change g.2+a.2+price model [.control 1] ≤ _
  rw [show price model [.control 1]=2 by rfl]
  have hsum := Nat.add_le_add_right (Nat.add_le_add hprep hconvert) 2
  exact hsum

theorem same_return_and_cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0 < B)
    (hL : ∀ k,0 < lengths p x k ∧ lengths p x k ≤ B)
    (hb : InBox (lengths p x) (eval s x))
    (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length ≤ 1)
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T)
    (hml : p.parameters.root.polynomial.length ≤ 4)
    (heB : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi,B] T)
    (hBH : RationalHeight B T)
    (hsize : ∀ k,HasHeight (p.rows.read k).length T)
    (hresource : ∀ k,HasHeight (s.data.read k) T) (hT : 2 ≤ T) :
    (PlayerSpecificTerminalCoreInputExecution.run p s B).1 =
      PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B
        (PlayerSpecificAlgebraicTerminalPreparation.prepare RationalCostModel.schoolbook p s B) ∧
    (PlayerSpecificTerminalCoreInputExecution.run p s B).2 ≤ work N T :=
  ⟨PlayerSpecificTerminalCoreInputExecution.value p s B,
    cost p s B x hc hs hB hL hb hmass hend T hroot hml heB hBH hsize hresource hT⟩

end Blotto.PlayerSpecificTerminalCoreInputSourceCost
