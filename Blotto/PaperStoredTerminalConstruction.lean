import Blotto.PaperStoredGroupEmission

/-! The actual terminal program uses the priced cached-group and whole-row
constructors. Whole programs and complete bounded results equal the stored
producer, including consumed cursors and refusals. Their additional source
array/descriptor work is bounded at the actual primary-source handoff.
-/

namespace Blotto.PaperStoredTerminalConstruction
set_option autoImplicit false
set_option maxHeartbeats 2000000

def addressWidth {n : ℕ} (i : RationalTerminalLotto n) (W : ℕ) : ℕ :=
  StoredArrayReferenceList.poolAddressWidth (n+i.groups.length+2) W

def program {n : ℕ} (i : RationalTerminalLotto n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    RationalStoredAllocationProgram n 80 :=
  let packed := RationalTerminalPacking.prepare i
  let output := packed.prepareOutput
  match h : i.pivot with
  | none =>
      (RationalStoredAllocationProgram.ofProgram
        ((packed.uniformSpec (i.pivot_none h)).program i.groups_count K scalarBits)
        (fun y => (PaperStoredGroupEmission.emit output model primitive (addressWidth i W) y).1)).widen (by decide)
  | some pivot =>
      RationalStoredAllocationProgram.ofProgram
        ((packed.mixedSpec pivot (i.pivot_some h)).program i.groups_count K outerBits scalarBits)
        (fun y => (PaperStoredGroupEmission.emitMixed output model primitive (addressWidth i W) pivot y).1)

theorem program_data {n : ℕ} (i : RationalTerminalLotto n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    program i model primitive W K outerBits scalarBits = i.storedProgram K outerBits scalarBits := by
  unfold program
  simp only [PaperStoredGroupEmission.emit_data,PaperStoredGroupEmission.emitMixed_data]
  rfl

def constructorWork (primitive : ℕ → ℕ) (A n m : ℕ) : ℕ :=
  PaperIndexedArrayConstruction.overhead primitive A m m+
    PaperIndexedArrayConstruction.overhead primitive A n n+PaperStoredGroupEmission.wrapperWork primitive A n m

def metadata {n : ℕ} (i : RationalTerminalLotto n) (primitive : ℕ → ℕ) (W : ℕ) : ℕ :=
  match i.pivot with
  | none => constructorWork primitive (addressWidth i W) n i.groups.length
  | some _ => constructorWork primitive (addressWidth i W) n (i.groups.length+1)

theorem metadata_bound {n : ℕ} (i : RationalTerminalLotto n) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w,primitive w ≤ c*w) (W : ℕ) (hCount : n+4 ≤ W) :
    metadata i primitive W ≤ 2048*(c+1)*(n+1)*(binaryWordWidth (W+2)+1) := by
  have hm := i.groups_count
  have ha := StoredArrayReferenceList.poolAddressWidth_log_bound (n+i.groups.length+2) W
  have hIndex := binaryWordWidth_mono (show (n+i.groups.length+2)+1 ≤ W+2 by omega)
  have hWord := binaryWordWidth_mono (show W+1 ≤ W+2 by omega)
  have hA : addressWidth i W ≤ 2*(binaryWordWidth (W+2)+1) := by unfold addressWidth; omega
  have hUniform := PaperStoredGroupEmission.constructor_metadata_bound primitive c hPrimitive
    (addressWidth i W) n i.groups.length W (by omega) hA
  have hMixed := PaperStoredGroupEmission.constructor_metadata_bound primitive c hPrimitive
    (addressWidth i W) n (i.groups.length+1) W (by omega) hA
  have hu := Nat.mul_le_mul_right (binaryWordWidth (W+2)+1)
    (Nat.mul_le_mul_left (128*(c+1)) (show n+i.groups.length+3 ≤ 7*(n+1) by omega))
  have hx := Nat.mul_le_mul_right (binaryWordWidth (W+2)+1)
    (Nat.mul_le_mul_left (128*(c+1)) (show n+(i.groups.length+1)+3 ≤ 7*(n+1) by omega))
  unfold metadata constructorWork PaperStoredGroupEmission.metadataBound at *
  split <;> nlinarith only [hUniform,hMixed,hu,hx]

end Blotto.PaperStoredTerminalConstruction

namespace Blotto.RationalLottoResourceSystem
set_option autoImplicit false

def paperConstructedFixedRun {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K R : ℕ) (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    Option (RationalResourceArray n) × ℕ :=
  i.runStoredWithTerminalIndexed
    (fun value => PaperStoredTerminalConstruction.program (i.terminalData value) model primitive W K outer scalar)
    R choice (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

theorem paperConstructedFixedRun_data {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K R : ℕ) (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    i.paperConstructedFixedRun model primitive W K R outer scalar choice = i.storedFixedRun K R outer scalar choice := by
  simp only [paperConstructedFixedRun,PaperStoredTerminalConstruction.program_data,storedFixedRun]

noncomputable def paperConstructorWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (primitive : ℕ → ℕ) (W K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.sharedTerminalWindowWork (coinBitBudget n K) (firstBitBlock (coinBitBudget n K) K inner)
    (fun value _ _ => PaperStoredTerminalConstruction.metadata (i.terminalData value) primitive W)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le _)

theorem OnLattice.paperConstructorWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w)
    (W : ℕ) (hCount : n+4 ≤ W) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    i.paperConstructorWork primitive W K bits ≤ 2048*(c+1)*(n+1)*(binaryWordWidth (W+2)+1) := by
  have hInitial : (SharedResourceCursor.ready i.initialState).OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  let inner := firstBitBlock (innerBitBudget n K) K bits
  have hp := i.sharedTerminalWindowWork_bound D h.1 (coinBitBudget n K)
    (firstBitBlock (coinBitBudget n K) K inner)
    (fun value _ _ => PaperStoredTerminalConstruction.metadata (i.terminalData value) primitive W)
    (2048*(c+1)*(n+1)*(binaryWordWidth (W+2)+1)) 0
    (fun value _ _ _ => by
      simpa only [Nat.zero_mul,Nat.add_zero] using
        PaperStoredTerminalConstruction.metadata_bound (i.terminalData value) primitive c hPrimitive W hCount)
    (.ready i.initialState) i.initial_invariant hInitial 0 (Nat.zero_le _)
  simpa only [paperConstructorWork,Nat.zero_mul,Nat.add_zero] using hp

end Blotto.RationalLottoResourceSystem

namespace Blotto.PaperStoredTerminalConstruction
set_option autoImplicit false

noncomputable def originalWork {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ)
    (rich : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  if rich then i.normalizedInput.richNativeSystem.paperConstructorWork primitive (PRGPaperDrawCost.width i K) K bits
  else i.normalizedInput.poorNativeSystem.paperConstructorWork primitive (PRGPaperDrawCost.width i K) K bits

theorem originalWork_bound {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w,primitive w ≤ c*w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    originalWork i primitive rich K bits ≤ 2048*(c+1)*(n+1)*PRGPaperDrawCost.width i K := by
  have hn := RationalPRGLinearFramingWork.count_le_inputWidth i
  have hCount : n+4 ≤ PRGPaperDrawCost.width i K := by
    unfold PRGPaperDrawCost.width RationalPRGLinearFramingWork.uniformWidth
    omega
  have hRich := i.normalizedInput.richNativeSystem_on_lattice.paperConstructorWork_bound
    primitive c hPrimitive (PRGPaperDrawCost.width i K) hCount K bits
  have hPoor := i.normalizedInput.poorNativeSystem_on_lattice.paperConstructorWork_bound
    primitive c hPrimitive (PRGPaperDrawCost.width i K) hCount K bits
  have hWord := Nat.mul_le_mul_left (2048*(c+1)*(n+1)) (PRGPaperSharpDrawCost.logFactor_le_width i K)
  unfold PRGPaperDrawCost.logFactor at hWord
  unfold originalWork
  cases rich <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

end Blotto.PaperStoredTerminalConstruction
