import Blotto.RationalTerminalBitRouteProgram

/-! Route coefficients depend on original lengths and group totals, so their
slot bound requires only the length lattice. Resource coordinates need no
additional lattice promise; all old stronger-hypothesis statements remain. -/

namespace Blotto.RationalTerminalPacking

theorem assignmentPayloadWidth_of_length_lattice {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1) (hLength : ∀ j, OnRationalLattice D (i.length j))
    (hWidth : binaryWordWidth D ≤ s) (e : Fin n × GroupRoute i.groups.length) (he : e ∈ p.routeAssignments) :
    routePayloadWordWidth e.2 ≤ routePayloadWidth n s := by
  rcases (p.mem_routeAssignments e).mp he with ⟨g, _, hEq⟩
  have hCount : i.groups.length ≤ 3 := by rcases i.groups_count with h | h <;> omega
  have hLabel := binaryWordWidth_mono (show g.val ≤ n + 4 by omega)
  have hRatio := rationalWordWidth_of_height ((i.partition.ratio_height_lattice D hD hLength
    (fun j => (i.length_le j).trans hB) (fun g => (i.partition_total_le g).trans hB) e.1 g).mono hWidth)
  change rationalWordWidth (i.length e.1 / i.partition.total g) ≤ 1 + 2 * s at hRatio
  rw [hEq]
  change 1 + binaryWordWidth g.val + rationalWordWidth (i.length e.1 / i.partition.total g) ≤ routePayloadWidth n s
  unfold routePayloadWidth
  omega

theorem routeStoreProgram_frameFit_of_lengths {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1) (hLength : ∀ j, OnRationalLattice D (i.length j))
    (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s) :
    ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ 2 * routePayloadWidth n s + 1 := by
  intro e he
  apply BinaryRouteSlot.frame_fit_of_payload
  rw [routeStoreProgram, List.mem_append] at he
  rcases he with he | he
  · rcases List.mem_ofFn.mp he with ⟨j, rfl⟩
    have hZero := rationalWordWidth_of_height ((show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs)
    change 1 + 0 + rationalWordWidth (0 : ℚ) ≤ 1 + binaryWordWidth (n + 4) + (1 + 2 * s)
    omega
  · exact p.assignmentPayloadWidth_of_length_lattice D s hD hB hLength hWidth e he

end Blotto.RationalTerminalPacking

namespace Blotto.RationalLottoResourceSystem

theorem terminal_route_frameFit {n : ℕ} (i : RationalLottoResourceSystem n) (D s : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hLength : ∀ j, OnRationalLattice D (i.length j)) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (value : i.PhaseResult) :
    ∀ e ∈ (RationalTerminalPacking.prepare (i.terminalData value)).routeStoreProgram,
      (BinaryRouteFrame.encode e.2).length ≤ 2 * RationalTerminalPacking.routePayloadWidth n s + 1 :=
  (RationalTerminalPacking.prepare (i.terminalData value)).routeStoreProgram_frameFit_of_lengths D s hD hB hLength hs hWidth

end Blotto.RationalLottoResourceSystem
