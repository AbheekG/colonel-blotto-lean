import Blotto.PlayerSpecificTerminalLeafMemberSourceCost

/-! The actual original-coordinate emitter pays once per uniform member,
then copies its complete input and output arrays and finite controls.
Disjoint group membership caps the number of field-operation pairs by N. -/
namespace Blotto.PlayerSpecificTerminalLeafEmissionSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicGrouping
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicTerminalPreparation
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frameHeight (N T K : ℕ) : ℕ :=
  max (PlayerSpecificAlgebraicTerminalLeafBounds.height N T K) N+6

def work (N T K : ℕ) : ℕ :=
  N*PlayerSpecificTerminalLeafMemberSourceCost.work RationalCostModel.schoolbook N T K+
  (200*(N+N+1)+9)*RationalCostModel.schoolbook.rat
    (PlayerSpecificAlgebraicComparisonExecution.width (frameHeight N T K))

theorem measured_length {N : ℕ} (root : PlayerSpecificAlgebraicCandidates.Candidate)
    (length : Fin N → Data) (groups : List (Group N)) (y : FixedArrayTable 4 Data) :
    (PlayerSpecificTerminalLeafEmissionExecution.measured RationalCostModel.schoolbook root length groups y).length =
      (groups.map Group.members).flatten.length := by
  simp only [PlayerSpecificTerminalLeafEmissionExecution.measured,List.length_flatMap,
    List.length_map,List.length_flatten,List.map_map,Function.comp_def]
  have he : (List.finRange groups.length).map (fun g => (groups.get g).members.length) =
      groups.map (fun h => h.members.length) := by
    conv_rhs => rw [← List.map_get_finRange groups]
    simp only [List.map_map,Function.comp_def]
  exact congrArg List.sum he

theorem cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0<B)
    (hL : ∀ k,0<lengths p x k ∧ lengths p x k≤B)
    (hb : InBox (lengths p x) (eval s x))
    (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length≤1)
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T)
    (hml : p.parameters.root.polynomial.length≤4)
    (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] T)
    (hBH : RationalHeight B T)
    (hsize : ∀ k,HasHeight (p.rows.read k).length T)
    (hresource : ∀ k,HasHeight (s.data.read k) T)
    (H K : ℕ) (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    (PlayerSpecificTerminalLeafEmissionExecution.fromCore RationalCostModel.schoolbook
      p.parameters.root (fun j => (p.rows.read j).length)
      (prepare RationalCostModel.schoolbook p s B).groups
      (prepare RationalCostModel.schoolbook p s B).fractional
      (PlayerSpecificAlgebraicTerminalCoreExecution.run p s B H K bits)).2≤work N T K := by
  let model:=RationalCostModel.schoolbook
  let root:=p.parameters.root
  let g:=prepare model p s B
  let length:Fin N→Data:=fun j => (p.rows.read j).length
  let y:=PlayerSpecificAlgebraicTerminalCoreExecution.run p s B H K bits
  let entries:=PlayerSpecificTerminalLeafEmissionExecution.measured model root length g.groups y
  let result:=(PlayerSpecificTerminalLeafEmissionExecution.fromCore model root length g.groups g.fractional y).1
  let S:=frameHeight N T K
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  let M:=PlayerSpecificTerminalLeafMemberSourceCost.work model N T K
  have hm0 : root.polynomial≠[] := by
    intro hz
    exact hc.irreducible.ne_zero (by rw [hz]; rfl)
  have hgcount : g.groups.length≤3 :=
    (groups_count model p s B x hc hs hB hL hb hmass hend).2
  have hgn:=PlayerSpecificAlgebraicTerminalGroupBounds.members_nodup model p s B x hc
  have hlen : entries.length≤N := by
    rw [measured_length]
    simpa only [Fintype.card_fin] using hgn.length_le_card
  have hGS:=PlayerSpecificAlgebraicTerminalGroupBounds.cached_bounds model p s B x hc hs hB hL hb hmass hend T hsize
  have hG : ∀ z∈g.groups,Reduced root.polynomial z.total ∧
      HasHeight z.total ((T+1)*(N+N)+3) := by
    intro z hz
    exact ⟨(hGS z hz).2.2.1,(hGS z hz).2.2.2.2.2⟩
  have hY := (PlayerSpecificAlgebraicTerminalCoreExecution.every_path p s B x hc hs hB hL hb hmass hend
    T hroot hml hBH hsize hresource H K bits).2
  have hEach : ∀ entry∈entries,entry.2≤M := by
    intro entry he0
    simp only [entries,PlayerSpecificTerminalLeafEmissionExecution.measured,List.mem_flatMap] at he0
    obtain ⟨gi,_,he0⟩:=he0
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp he0
    exact PlayerSpecificTerminalLeafMemberSourceCost.cost model root length g.groups y gi j T K
      hc.normalized hm0 hml hroot (fun j=>⟨hc.lengths j,hsize j⟩) hG hY hgcount
  have hsum : (entries.map Prod.snd).sum≤N*M := by
    calc
      _ ≤ (entries.map (fun _ => M)).sum := List.sum_le_sum (fun entry he0 => hEach entry he0)
      _ = entries.length*M := by simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
      _ ≤ N*M := Nat.mul_le_mul_right M hlen
  have hTS : T≤S := by
    have hbase : T≤PlayerSpecificAlgebraicTerminalLeafBounds.base N T K := by
      change T≤PlayerSpecificAlgebraicTerminalCoreExecution.height N T K+
        ((T+1)*(N+N)+3)+T+1
      exact (Nat.le_add_left T _).trans (Nat.le_succ _)
    have hleaf : PlayerSpecificAlgebraicTerminalLeafBounds.base N T K≤
        PlayerSpecificAlgebraicTerminalLeafBounds.height N T K :=
      PlayerSpecificAlgebraicExpressionBudget.initial_le 2 _
    change T≤max (PlayerSpecificAlgebraicTerminalLeafBounds.height N T K) N+6
    exact hbase.trans (hleaf.trans ((le_max_left _ _).trans (Nat.le_add_right _ _)))
  have hLeafS : PlayerSpecificAlgebraicTerminalLeafBounds.height N T K≤S := by
    change PlayerSpecificAlgebraicTerminalLeafBounds.height N T K≤
      max (PlayerSpecificAlgebraicTerminalLeafBounds.height N T K) N+6
    exact (le_max_left _ _).trans (Nat.le_add_right _ _)
  have hNS : N≤S := by
    change N≤max (PlayerSpecificAlgebraicTerminalLeafBounds.height N T K) N+6
    exact (le_max_right _ _).trans (Nat.le_add_right _ _)
  have hS : 1≤S := by
    change 1≤max (PlayerSpecificAlgebraicTerminalLeafBounds.height N T K) N+6
    exact (by decide : 1≤6).trans (Nat.le_add_left _ _)
  have hresult : ∀ j,Reduced root.polynomial (result.read j) ∧
      HasHeight (result.read j) (PlayerSpecificAlgebraicTerminalLeafBounds.height N T K) := by
    intro j
    dsimp only [result]
    rw [PlayerSpecificTerminalLeafEmissionExecution.fromCore_value]
    exact PlayerSpecificAlgebraicTerminalLeafBounds.bounds p s B x hc hs hB hL hb hmass hend
      T hroot hml hBH hsize hresource H K bits j
  have hf := PlayerSpecificExpressionVectorFrameCost.cost model root
    (FixedArrayTable.ofFn length) result S (mono hroot hTS) hml (mono he hTS)
    (fun j => ⟨by rw [FixedArrayTable.read_ofFn]; exact mono (hsize j) hTS,
      by rw [FixedArrayTable.read_ofFn]; have h := (hc.lengths j).2;
         change (length j).length < root.polynomial.length at h
         have hm : root.polynomial.length≤4 := hml
         omega⟩)
    (fun j => ⟨mono (hresult j).2 hLeafS,by
      have h := (hresult j).1.2
      have hm : root.polynomial.length≤4 := hml
      omega⟩)
    hNS hNS hS
  let flag:=if g.fractional.isSome then 1 else 0
  have hwords : ∀ word∈[N,g.groups.length,flag],binaryWordWidth word≤W := by
    intro word hw
    have hsmall : word≤S := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with hw|hw|hw
      · rw [hw]; exact hNS
      · rw [hw]
        have h3 : 3≤S := by
          change 3≤max (PlayerSpecificAlgebraicTerminalLeafBounds.height N T K) N+6
          exact (by decide : 3≤6).trans (Nat.le_add_left _ _)
        omega
      · rw [hw]; dsimp only [flag]; split <;> omega
    exact (control_width word).trans ((Nat.add_le_add_right hsmall 1).trans
      (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
  have hctrl := PlayerSpecificAlgebraicCallerFrame.controls_cost model [N,g.groups.length,flag] W hwords
    (by have h := (PlayerSpecificAlgebraicActiveListCost.width_large S).1; omega)
  have hctrl' : price model [.control N,.control g.groups.length,.control flag]≤9*model.rat W := by
    change price model ([N,g.groups.length,flag].map Event.control)≤9*model.rat W
    simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul] using hctrl
  change (entries.map Prod.snd).sum+
    price model (PlayerSpecificExpressionVectorExecution.frame root (FixedArrayTable.ofFn length) result)+
    price model [.control N,.control g.groups.length,.control flag]≤
      N*M+(200*(N+N+1)+9)*model.rat W
  have hf' : price model (PlayerSpecificExpressionVectorExecution.frame root
      (FixedArrayTable.ofFn length) result)≤200*(N+N+1)*model.rat W := hf
  calc
    _ ≤ N*M+200*(N+N+1)*model.rat W+9*model.rat W :=
      Nat.add_le_add (Nat.add_le_add hsum hf') hctrl'
    _ = _ := by ring

end Blotto.PlayerSpecificTerminalLeafEmissionSourceCost
