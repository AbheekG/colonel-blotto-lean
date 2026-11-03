import Blotto.BinaryRouteEncodingWork
import Blotto.RationalRouteBitStore

/-! The complete route bit-build component retains each slot encoder,
assignment-cell construction, both iterators and the bit-store observer.
Full address/backend implementations and physical allocator costs stay separate. -/

namespace Blotto.RationalTerminalPacking

def routeSlotPreparationWork {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (W : ℕ) : ℕ :=
  (p.routeStoreProgram.map (fun e => BinaryRouteSlot.preparationWork primitive e.2 W)).sum

theorem routeSlotPreparationWork_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c W : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    p.routeSlotPreparationWork primitive W ≤ 2 * n * BinaryRouteSlot.preparationBound c (routePayloadWidth n s) W := by
  have hp : (p.routeStoreProgram.map (fun e => BinaryRouteSlot.preparationWork primitive e.2 W)).sum ≤
      p.routeStoreProgram.length * BinaryRouteSlot.preparationBound c (routePayloadWidth n s) W := by
    calc
      _ ≤ (p.routeStoreProgram.map (fun _ => BinaryRouteSlot.preparationBound c (routePayloadWidth n s) W)).sum :=
        List.sum_le_sum (fun e he => BinaryRouteSlot.preparationWork_bound primitive c hPrimitive e.2 _ W
          (p.routeStoreProgram_words D s h hD hB hs hWidth e he))
      _ = _ := by simp
  have hCount : p.routeStoreProgram.length ≤ 2 * n := by rw [← TableStoreRAM.writeCount_eq]; exact p.routeStoreProgram_writes
  exact hp.trans (Nat.mul_le_mul_right _ hCount)

def routeBitBuildWork {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (W : ℕ) (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (addressPrice : Fin (n * W) → ℕ) : ℕ :=
  p.routeSlotPreparationWork primitive W +
    (p.routeBitStoreProgram W hFit).length * (FixedWordRegion.addressWidth 0 n W + 2) +
      indexedLoopMetadataBitWork primitive 0 p.routeStoreProgram.length +
        indexedLoopMetadataBitWork primitive 0 (p.routeBitStoreProgram W hFit).length +
          TableStoreRAM.writeWordWork (fun _ : Bool => 1) addressPrice (p.routeBitStoreProgram W hFit)

def routeBitBuildBound (c n s W A : ℕ) : ℕ :=
  2 * n * BinaryRouteSlot.preparationBound c (routePayloadWidth n s) W +
    2 * n * W * (FixedWordRegion.addressWidth 0 n W + 2) + indexedLoopMetadataBound c (2 * n) +
      indexedLoopMetadataBound c (2 * n * W) + 2 * n * W * (2 + A)

theorem routeBitBuildWork_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c W : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (addressPrice : Fin (n * W) → ℕ) (A : ℕ) (hAddress : ∀ address, addressPrice address ≤ A) :
    p.routeBitBuildWork primitive W hFit addressPrice ≤ routeBitBuildBound c n s W A := by
  have hEncode := p.routeSlotPreparationWork_bound D s h hD hB hs hWidth primitive c W hPrimitive
  have hBits := p.routeBitStoreProgram_length_bound W hFit
  have hCopy := Nat.mul_le_mul_right (FixedWordRegion.addressWidth 0 n W + 2) hBits
  have hCount : p.routeStoreProgram.length ≤ 2 * n := by rw [← TableStoreRAM.writeCount_eq]; exact p.routeStoreProgram_writes
  have hRecords := (indexedLoopMetadataBitWork_bound primitive c hPrimitive p.routeStoreProgram.length).trans
    (indexedLoopMetadataBound_mono c hCount)
  have hBitLoop := (indexedLoopMetadataBitWork_bound primitive c hPrimitive (p.routeBitStoreProgram W hFit).length).trans
    (indexedLoopMetadataBound_mono c hBits)
  have hStores := p.routeBitStoreProgram_wordWork_bound W hFit addressPrice A hAddress
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hEncode hCopy) hRecords) hBitLoop) hStores

end Blotto.RationalTerminalPacking
