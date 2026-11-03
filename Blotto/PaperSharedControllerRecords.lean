import Blotto.PaperPRGCachedDraw
import Blotto.SharedResourceControlRefinement

/-! Source cursor/return records follow the actual ready/request/coin guards.
The fixed source callback has seven arithmetic instructions and twelve
registers; its rational operations stay in the preceding ledger. This source
profile charges its bounded reference/index fields and cursor/result fields,
not a native allocator or a copy of an arbitrary state payload.
-/

namespace Blotto.PaperSharedControllerRecords
set_option autoImplicit false
set_option maxHeartbeats 2000000

def unitWork (primitive : ℕ → ℕ) (W : ℕ) : ℕ := 1024*(W+primitive W+1)

theorem fixed_source_shape (p : RationalRoundingPair) :
    RealPairProgram.code.length=7 ∧ (RationalPairProgram.inputs p).size=5 ∧
      (RationalPairProgram.run p).size=12 :=
  ⟨rfl,rfl,RationalPairProgram.run_size p⟩

theorem unitWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w)
    (W : ℕ) (hW : 1 ≤ W) : unitWork primitive W ≤ 2048*(c+1)*W := by
  have hp := hPrimitive W
  unfold unitWork
  nlinarith only [hp,hW]

theorem source_count_bound {n : ℕ} {L : Fin n → ℚ} (N : ℕ) (bits : Fin N → Bool)
    (cursor : SharedResourceCursor L) (pos : ℕ) (hpos : pos ≤ N) :
    SharedResourceCursor.controlWork (fun _ => 1) (fun _ => 1) N bits cursor pos hpos ≤
      cursor.rank+(N-pos)+1 := by
  cases hCursor : cursor with
  | ready state =>
      conv_lhs => unfold SharedResourceCursor.controlWork
      split
      · exact Nat.zero_le _
      · rename_i p hp
        have ih := source_count_bound N bits (SharedResourceCursor.prepared p) pos hpos
        have hr := SharedResourceCursor.prepared_rank_lt state p hp
        omega
  | @coin w choice a b hb hab =>
      conv_lhs => unfold SharedResourceCursor.controlWork
      by_cases hz : a.isZero=true
      · simp only [dite_eq_left hz]
        have ih := source_count_bound N bits (.ready (choice.select false)) pos hpos
        have hr := SharedResourceCursor.selected_rank_lt choice a b hb hab false
        omega
      · simp only [dite_eq_right hz]
        by_cases he : a.same b=true
        · simp only [dite_eq_left he]
          have ih := source_count_bound N bits (.ready (choice.select true)) pos hpos
          have hr := SharedResourceCursor.selected_rank_lt choice a b hb hab true
          omega
        · simp only [dite_eq_right he]
          by_cases hRead : pos<N
          · simp only [dite_eq_left hRead]
            have hlt : a.value<b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
            by_cases hd : bits ⟨pos,hRead⟩=(a.coinStep b).1
            · simp only [ite_eq_left hd]
              have ih := source_count_bound N bits
                (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le) (pos+1) (by omega)
              have hr : (SharedResourceCursor.coin choice (a.coinStep b).2 b hb
                  (a.coinStep_normalized b hlt).le).rank=(SharedResourceCursor.coin choice a b hb hab).rank := rfl
              omega
            · simp only [ite_eq_right hd]
              have ih := source_count_bound N bits (.ready (choice.select (!bits ⟨pos,hRead⟩))) (pos+1) (by omega)
              have hr := SharedResourceCursor.selected_rank_lt choice a b hb hab (!bits ⟨pos,hRead⟩)
              omega
          · simp only [dite_eq_right hRead]
            omega
termination_by (N-pos,cursor.rank)
decreasing_by
  all_goals try simp only [hCursor]
  all_goals first
    | (apply Prod.Lex.right; apply SharedResourceCursor.prepared_rank_lt; assumption)
    | (apply Prod.Lex.right; exact SharedResourceCursor.selected_rank_lt choice a b hb hab false)
    | (apply Prod.Lex.right; exact SharedResourceCursor.selected_rank_lt choice a b hb hab true)
    | (apply Prod.Lex.left; omega)

def sourceWork {n : ℕ} (i : RationalLottoResourceSystem n) (primitive : ℕ → ℕ) (W N : ℕ)
    (bits : Fin N → Bool) : ℕ :=
  unitWork primitive W*(SharedResourceCursor.controlWork (fun _ => 1) (fun _ => 1)
    N bits (.ready i.initialState) 0 (Nat.zero_le _)+1)

theorem sourceWork_bound {n : ℕ} (i : RationalLottoResourceSystem n) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) (W N : ℕ) (hW : 1 ≤ W) (bits : Fin N → Bool) :
    sourceWork i primitive W N bits ≤ 2048*(c+1)*W*(2*n+N+3) := by
  have hCount := source_count_bound N bits (.ready i.initialState) 0 (Nat.zero_le _)
  have hRank := rationalResourceMachine_initial_rank i.length i.initial
  change (rationalResourceMachine i.length).rank (.ready i.initialState) ≤ n-1 at hRank
  have hInitial : (SharedResourceCursor.ready i.initialState).rank ≤ 2*n+1 := by
    change 2*(rationalResourceMachine i.length).rank (.ready i.initialState)+1 ≤ 2*n+1
    have hn := Nat.sub_le n 1
    omega
  have hUnit := unitWork_bound primitive c hPrimitive W hW
  unfold sourceWork
  exact Nat.mul_le_mul hUnit (by omega)

noncomputable def terminalWork {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : ℕ :=
  i.sharedTerminalWindowWork N bits
    (fun value pos hpos =>
      let p := PaperStoredTerminalConstruction.program (i.terminalData value) model primitive W K outer scalar
      unitWork primitive W*(p.machine.cachedCounts N bits (.state p.start) pos hpos).visits)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le _)

theorem OnLattice_terminalWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w,primitive w ≤ c*w) (W K N : ℕ) (hW : 1 ≤ W)
    (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    terminalWork i model primitive W K N outer scalar bits ≤ 2048*(c+1)*W*(162+2*N) := by
  have hInitial : (SharedResourceCursor.ready i.initialState).OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  have hUnit := unitWork_bound primitive c hPrimitive W hW
  have hTerminal (value : i.PhaseResult) (_hValue : value.1.resource.OnLattice D) (pos : ℕ) (hpos : pos ≤ N) :
      let p := PaperStoredTerminalConstruction.program (i.terminalData value) model primitive W K outer scalar
      unitWork primitive W*(p.machine.cachedCounts N bits (.state p.start) pos hpos).visits ≤
        2048*(c+1)*W*(162+2*N)+0*(N-pos) := by
    dsimp only
    let p := PaperStoredTerminalConstruction.program (i.terminalData value) model primitive W K outer scalar
    have hCount := (p.machine.indexedCounts_bounds N bits (CachedWordCursor.state p.start).reference pos hpos).2
    rw [←p.machine.cachedCounts_refines] at hCount
    have hRank := p.rank_le
    change _ ≤ 2*p.machine.rank p.start+1+2*(N-pos)+1 at hCount
    simp only [Nat.zero_mul,Nat.add_zero]
    change unitWork primitive W*(p.machine.cachedCounts N bits (.state p.start) pos hpos).visits ≤
      2048*(c+1)*W*(162+2*N)
    exact Nat.mul_le_mul hUnit (by omega)
  have hBound := i.sharedTerminalWindowWork_bound D h.1 N bits
    (fun value pos hpos =>
      let p := PaperStoredTerminalConstruction.program (i.terminalData value) model primitive W K outer scalar
      unitWork primitive W*(p.machine.cachedCounts N bits (.state p.start) pos hpos).visits)
    (2048*(c+1)*W*(162+2*N)) 0 hTerminal (.ready i.initialState) i.initial_invariant hInitial 0 (Nat.zero_le _)
  simpa only [terminalWork,Nat.zero_mul,Nat.add_zero] using hBound

end Blotto.PaperSharedControllerRecords
