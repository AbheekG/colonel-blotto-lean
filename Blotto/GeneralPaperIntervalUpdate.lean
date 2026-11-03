import Blotto.GeneralPaperIntervalGeometry

/-! The actual sparse contiguous-range traversal. Endpoints are passed on
the traversal stack, rather than retained as large keys in every node.
Midpoint division is exact rational arithmetic. Integer grid correspondence,
global level/path bounds and the complete address/bit-space join remain
separate obligations.
-/
namespace Blotto.GeneralPaperIntervalUpdate
open GeneralPaperIntervalCache GeneralPaperIntervalGeometry GeneralPaperPreparedPowers
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result (height : ℕ) where
  node : Node height
  visits : ℕ
  work : ℕ

def run (prepared : Prepared) (lo hi : ℚ) (amount height : ℕ) (node : Node height)
    (start span : ℚ) : Result height :=
  if Disjoint start span lo hi then ⟨node,1,8⟩ else
    if Covered start span lo hi then ⟨raiseRoot amount node,1,16⟩ else
      match height,node with
        | 0,zeroNode => ⟨zeroNode,1,8⟩
        | height+1,.uniform _ level =>
          let left := run prepared lo hi amount height (.uniform height 0) start (span/2)
          let right := run prepared lo hi amount height (.uniform height 0) (start+span/2) (span/2)
          let joined := GeneralPaperCachedMassJoin.recompute prepared (offset left.node) (mass prepared left.node)
            (offset right.node) (mass prepared right.node)
          ⟨.branch level joined.number left.node right.node,1+left.visits+right.visits,left.work+right.work+joined.work+48⟩
        | height+1,.branch level _ leftNode rightNode =>
          let left := run prepared lo hi amount height leftNode start (span/2)
          let right := run prepared lo hi amount height rightNode (start+span/2) (span/2)
          let joined := GeneralPaperCachedMassJoin.recompute prepared (offset left.node) (mass prepared left.node)
            (offset right.node) (mass prepared right.node)
          ⟨.branch level joined.number left.node right.node,1+left.visits+right.visits,left.work+right.work+joined.work+48⟩
termination_by height
decreasing_by all_goals omega

def CanRaise (cap amount : ℕ) : {height : ℕ} → Node height → Prop
  | _,.uniform _ level => level+amount≤cap
  | _,.branch level _ left right => level+amount≤cap ∧ CanRaise cap amount left ∧ CanRaise cap amount right

theorem can_raise_root (cap amount : ℕ) {height : ℕ} (node : Node height) (h : CanRaise cap amount node) :
    offset node+amount≤cap := by cases node with
  | uniform height level => exact h
  | branch level cached left right => exact h.1

theorem run_valid (lambda k : ℕ) (lo hi : ℚ) (amount height : ℕ) (node : Node height) (start span : ℚ)
    (hValid : Valid lambda k node) (hCap : CanRaise (GeneralPaperPowerPrecision.levelBound lambda k) amount node) :
    Valid lambda k (run (prepare lambda k) lo hi amount height node start span).node := by
  induction height generalizing start span with
  | zero =>
    rw [run.eq_def]
    split
    · exact hValid
    · split
      · exact raised_valid lambda k amount node hValid (can_raise_root _ _ node hCap)
      · exact hValid
  | succ height ih =>
    rw [run.eq_def]
    split
    · exact hValid
    · split
      · exact raised_valid lambda k amount node hValid (can_raise_root _ _ node hCap)
      · cases node with
        | uniform h level =>
          have ha : amount≤GeneralPaperPowerPrecision.levelBound lambda k := by change level+amount≤_ at hCap; omega
          have hChild : CanRaise (GeneralPaperPowerPrecision.levelBound lambda k) amount (.uniform height 0) := by
            simpa only [CanRaise,Nat.zero_add] using ha
          have hl := ih (.uniform height 0) start (span/2) (Nat.zero_le _) hChild
          have hr := ih (.uniform height 0) (start+span/2) (span/2) (Nat.zero_le _) hChild
          exact rebuild_valid lambda k level _ _ hValid hl hr
        | branch level cached left right =>
          have hl := ih left start (span/2) hValid.2.1 hCap.2.1
          have hr := ih right (start+span/2) (span/2) hValid.2.2.1 hCap.2.2
          exact rebuild_valid lambda k level _ _ hValid.1 hl hr

theorem visits_bound (prepared : Prepared) (lo hi : ℚ) (amount height : ℕ) (node : Node height) (start span : ℚ)
    (hSpan : 0<span) : (run prepared lo hi amount height node start span).visits≤
      1+2*height*boundaries start span lo hi := by
  induction height generalizing start span with
  | zero => rw [run.eq_def]; split <;> (try split) <;> dsimp only <;> omega
  | succ height ih =>
    rw [run.eq_def]
    split
    · dsimp only; omega
    · rename_i hD
      split
      · dsimp only; omega
      · rename_i hC
        have hb := partial_has_boundary start span lo hi hD hC
        have hs := child_boundaries start span lo hi hSpan
        have hp : 0<span/2 := by linarith
        cases node with
        | uniform h level =>
          have hl := ih (.uniform height 0) start (span/2) hp
          have hr := ih (.uniform height 0) (start+span/2) (span/2) hp
          dsimp only
          nlinarith
        | branch level cached left right =>
          have hl := ih left start (span/2) hp
          have hr := ih right (start+span/2) (span/2) hp
          dsimp only
          nlinarith

theorem visits_linear (prepared : Prepared) (lo hi : ℚ) (amount height : ℕ) (node : Node height) (start span : ℚ)
    (hSpan : 0<span) : (run prepared lo hi amount height node start span).visits≤1+4*height := by
  have he := visits_bound prepared lo hi amount height node start span hSpan
  have hb := boundaries_le_two start span lo hi
  nlinarith

theorem nodes_bound (prepared : Prepared) (lo hi : ℚ) (amount height : ℕ) (node : Node height) (start span : ℚ)
    (hSpan : 0<span) : nodes (run prepared lo hi amount height node start span).node≤
      nodes node+2*height*boundaries start span lo hi := by
  induction height generalizing start span with
  | zero =>
    rw [run.eq_def]
    split
    · dsimp only; omega
    · split
      · rw [raised_nodes]; omega
      · dsimp only; omega
  | succ height ih =>
    rw [run.eq_def]
    split
    · dsimp only; omega
    · rename_i hD
      split
      · rw [raised_nodes]; omega
      · rename_i hC
        have hb := partial_has_boundary start span lo hi hD hC
        have hs := child_boundaries start span lo hi hSpan
        have hp : 0<span/2 := by linarith
        cases node with
        | uniform h level =>
          have hl := ih (.uniform height 0) start (span/2) hp
          have hr := ih (.uniform height 0) (start+span/2) (span/2) hp
          dsimp only [nodes] at *
          nlinarith
        | branch level cached left right =>
          have hl := ih left start (span/2) hp
          have hr := ih right (start+span/2) (span/2) hp
          change 1+nodes (run prepared lo hi amount height left start (span/2)).node+
            nodes (run prepared lo hi amount height right (start+span/2) (span/2)).node≤
              (1+nodes left+nodes right)+2*(height+1)*boundaries start span lo hi
          nlinarith

theorem nodes_linear (prepared : Prepared) (lo hi : ℚ) (amount height : ℕ) (node : Node height) (start span : ℚ)
    (hSpan : 0<span) : nodes (run prepared lo hi amount height node start span).node≤nodes node+4*height := by
  have he := nodes_bound prepared lo hi amount height node start span hSpan
  have hb := boundaries_le_two start span lo hi
  nlinarith

end Blotto.GeneralPaperIntervalUpdate
