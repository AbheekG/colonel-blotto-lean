import Blotto.PlayerSpecificTerminalPreparationPolynomial
import Blotto.PlayerSpecificFiniteResourceEntryCost

/-! Original-input terminal preparation bound for every actual finite
resource packet. The reached state, all coefficient sizes and both
player budgets are derived from the accepted rational input. -/
namespace Blotto.PlayerSpecificOriginalTerminalPreparationCost
open PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := PlayerSpecificTerminalPreparationPolynomial.coefficient*(PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1)^3

theorem transfer (C D N L T : ℕ) (hT : T+1≤D*(N+1)^2*(L+1)) :
    C*(N+1)^4*(T+1)^3≤(C*D^3)*(N+1)^10*(L+1)^3 := by
  calc
    _≤C*(N+1)^4*(D*(N+1)^2*(L+1))^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT 3)
    _=_ := by ring

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∀ (player : Bool) (H : ℕ) (bits : Fin ((N-1)*H) → Bool),
      (PlayerSpecificTerminalPreparationExecution.run RationalCostModel.schoolbook p
        (PlayerSpecificFiniteResourceLoop.draw p player H bits).1 (if player then 1 else i.budget)).2≤
          coefficient*(N+1)^10*(PlayerSpecificInitialPositivePrecision.inputSize i+1)^3 := by
  dsimp only
  let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
  let model:=RationalCostModel.schoolbook
  let L:=PlayerSpecificInitialPositivePrecision.inputSize i
  let T:=PlayerSpecificResourceEntryInput.height N L
  obtain ⟨x,_hx,hc,hml,hm,he,hl,_hmean,hvisited⟩:=PlayerSpecificResourceEntryInput.original_input i r hr
  have hm0 : p.parameters.root.polynomial≠[] := by intro h; exact hc.irreducible.ne_zero (by rw [h]; rfl)
  have hLT : L≤T := by
    dsimp [T,PlayerSpecificResourceEntryInput.height,PlayerSpecificOriginalResourceSourceCost.size,PlayerSpecificAlgebraicFiniteDrawContract.base]
    omega
  have hT : 1≤T := (PlayerSpecificResourceEntryInput.size_lower N L).2
  have hsize : T+1≤(PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1)*(N+1)^2*(L+1) := by
    change PlayerSpecificOriginalResourceSourceCost.size N L 0+1≤_
    simpa only [Nat.add_zero] using PlayerSpecificResourceSourcePolynomial.size_bound N L 0
  intro player H bits
  let s:=(PlayerSpecificFiniteResourceLoop.draw p player H bits).1
  let B : ℚ:=if player then 1 else i.budget
  have hs : PlayerSpecificFiniteResourceSourceCost.StateFits p x T s :=
    PlayerSpecificResourceVisitedStates.output model p _ H (N-1) (start model p player)
      (hvisited player (N-1)) (PlayerSpecificFiniteResourceLoop.blocks (N-1) H bits)
  have hB : RationalHeight B T := by
    cases player
    · exact (PlayerSpecificRecognitionInputHeights.original_fields i).1.mono hLT
    · exact one_height.mono hT
  have heB : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi,B] T := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|hq|hq
    · rw [hq]; exact he _ List.mem_cons_self
    · rw [hq]; exact he _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · rw [hq]; exact hB
  have ha : s.active.length≤N := by simpa only [Fintype.card_fin] using hs.1.nodup.length_le_card
  have ht:=PlayerSpecificTerminalPreparationPolynomial.cost p s B T hc.normalized hm0 hml hm heB hc.interval
    (fun j => ⟨hc.lengths j,hl j⟩) (fun j => ⟨hs.1.reduced j,hs.2 j⟩) ha
  exact ht.trans (transfer _ _ N L T hsize)

theorem same_return_and_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∀ (player : Bool) (H : ℕ) (bits : Fin ((N-1)*H) → Bool),
      let s:=(PlayerSpecificFiniteResourceEntryExecution.draw p player H bits).1.1
      (PlayerSpecificTerminalPreparationExecution.run RationalCostModel.schoolbook p s (if player then 1 else i.budget)).1=
        PlayerSpecificAlgebraicTerminalPreparation.prepare RationalCostModel.schoolbook p s (if player then 1 else i.budget) ∧
      (PlayerSpecificTerminalPreparationExecution.run RationalCostModel.schoolbook p s (if player then 1 else i.budget)).2≤
        coefficient*(N+1)^10*(PlayerSpecificInitialPositivePrecision.inputSize i+1)^3 := by
  dsimp only
  intro player H bits
  rw [PlayerSpecificFiniteResourceEntryExecution.value]
  exact ⟨PlayerSpecificTerminalPreparationExecution.value _ _ _ _,original_input i r hr player H bits⟩

end Blotto.PlayerSpecificOriginalTerminalPreparationCost
