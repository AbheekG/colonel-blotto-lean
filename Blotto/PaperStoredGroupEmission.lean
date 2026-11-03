import Blotto.PaperStoredRowConstruction

/-! Priced source construction of the cached small group array and the
complete emitted row. Both constructors preserve the actual stored producers.
Rational coordinate work is exactly the existing uniform/mixed emission
ledger, with source array/index/descriptor and wrapper costs added explicitly.
-/

namespace Blotto.PaperStoredGroupEmission
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

def wrapperWork (primitive : ℕ → ℕ) (addressWidth n m : ℕ) : ℕ :=
  8*addressWidth+4*primitive (binaryWordWidth (n+m+1))+20

def emit {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (y : Fin m → ℚ) : RationalResourceArray n × ℕ :=
  let sampled := PaperIndexedArrayConstruction.run primitive addressWidth
    (fun g => (y g,rationalWordWidth (y g)))
  let returned := PaperIndexedArrayConstruction.run primitive addressWidth
    (fun j => (p.routedValue sampled.1.read j,p.routedBitCost model sampled.1.read j))
  (PaperStoredRowConstruction.resourceArray returned.1,
    sampled.2+returned.2+wrapperWork primitive addressWidth n m)

def emitMixed {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (pivot : Fin n) (y : Fin (m+1) → ℚ) : RationalResourceArray n × ℕ :=
  let sampled := PaperIndexedArrayConstruction.run primitive addressWidth
    (fun g => (y g,rationalWordWidth (y g)))
  let returned := PaperIndexedArrayConstruction.run primitive addressWidth
    (fun j => (p.routedValue (fun g => sampled.1.read g.castSucc) j+
      if j=pivot then sampled.1.read (Fin.last m) else 0,
      p.mixedCoordinateBitCost model pivot sampled.1.read j))
  (PaperStoredRowConstruction.resourceArray returned.1,
    sampled.2+returned.2+wrapperWork primitive addressWidth n (m+1))

theorem emit_data {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (addressWidth : ℕ) (y : Fin m → ℚ) :
    (emit p model primitive addressWidth y).1 = p.emit y := by
  have hRead : (FixedArrayTable.ofFn y).read = y := funext (FixedArrayTable.read_ofFn y)
  unfold emit
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
  simp only [hRead]
  unfold PaperStoredRowConstruction.resourceArray
    PreparedGroupOutput.emit RationalProportionalGroups.emit RationalResourceArray.ofAllocation
    PreparedGroupOutput.routedValue
  simp only [hRead,FixedArrayTable.read_ofFn]
  rfl

theorem emitMixed_data {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (pivot : Fin n) (y : Fin (m+1) → ℚ) :
    (emitMixed p model primitive addressWidth pivot y).1 = p.emitMixed pivot y := by
  have hRead : (FixedArrayTable.ofFn y).read = y := funext (FixedArrayTable.read_ofFn y)
  unfold emitMixed
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
  simp only [hRead]
  unfold PaperStoredRowConstruction.resourceArray
    PreparedGroupOutput.emitMixed RationalProportionalGroups.emitMixed RationalResourceArray.ofAllocation
    PreparedGroupOutput.routedValue
  simp only [hRead,FixedArrayTable.read_ofFn]
  rfl

theorem emit_work {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (addressWidth : ℕ) (y : Fin m → ℚ) :
    (emit p model primitive addressWidth y).2 = p.emitBitCost model y+
      PaperIndexedArrayConstruction.overhead primitive addressWidth m m+
      PaperIndexedArrayConstruction.overhead primitive addressWidth n n+
      wrapperWork primitive addressWidth n m := by
  have hRead : (FixedArrayTable.ofFn y).read = y := funext (FixedArrayTable.read_ofFn y)
  unfold emit
  dsimp only
  rw [PaperIndexedArrayConstruction.run_work,PaperIndexedArrayConstruction.run_work,
    PaperIndexedArrayConstruction.run_data]
  simp only [hRead]
  unfold PreparedGroupOutput.emitBitCost
  ring

theorem emitMixed_work {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (pivot : Fin n) (y : Fin (m+1) → ℚ) :
    (emitMixed p model primitive addressWidth pivot y).2 = p.emitMixedBitCost model pivot y+
      PaperIndexedArrayConstruction.overhead primitive addressWidth (m+1) (m+1)+
      PaperIndexedArrayConstruction.overhead primitive addressWidth n n+
      wrapperWork primitive addressWidth n (m+1) := by
  have hRead : (FixedArrayTable.ofFn y).read = y := funext (FixedArrayTable.read_ofFn y)
  unfold emitMixed
  dsimp only
  rw [PaperIndexedArrayConstruction.run_work,PaperIndexedArrayConstruction.run_work,
    PaperIndexedArrayConstruction.run_data]
  simp only [hRead]
  unfold PreparedGroupOutput.emitMixedBitCost
  ring

theorem overhead_at_word (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w)
    (A count Q : ℕ) (hA : A ≤ 2*Q) (hIndex : binaryWordWidth (count+1) ≤ Q) (hQ : 1 ≤ Q) :
    PaperIndexedArrayConstruction.overhead primitive A count count ≤ 64*(c+1)*(count+1)*Q := by
  have hPay := Nat.mul_le_mul_left (10*c) hIndex
  have hStep : 6*A+10*c*binaryWordWidth (count+1)+28 ≤ 64*(c+1)*Q := by
    nlinarith only [hA,hPay,hQ]
  have hTotal := Nat.mul_le_mul_left (count+1) hStep
  exact (PaperIndexedArrayConstruction.overhead_bound primitive c hPrimitive A count count le_rfl).trans
    (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hTotal)

def metadataBound (c n m W : ℕ) : ℕ :=
  128*(c+1)*(n+m+3)*(binaryWordWidth (W+2)+1)

theorem constructor_metadata_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w)
    (A n m W : ℕ) (hCount : n+m ≤ W)
    (hAddress : A ≤
      2*(binaryWordWidth (W+2)+1)) :
    PaperIndexedArrayConstruction.overhead primitive A m m+
      PaperIndexedArrayConstruction.overhead primitive A n n+
      wrapperWork primitive A n m ≤
        metadataBound c n m W := by
  let Q := binaryWordWidth (W+2)+1
  change A ≤ 2*Q at hAddress
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hm : binaryWordWidth (m+1) ≤ Q :=
    (binaryWordWidth_mono (by omega : m+1 ≤ W+2)).trans (Nat.le_succ _)
  have hn : binaryWordWidth (n+1) ≤ Q :=
    (binaryWordWidth_mono (by omega : n+1 ≤ W+2)).trans (Nat.le_succ _)
  have hnm : binaryWordWidth (n+m+1) ≤ Q :=
    (binaryWordWidth_mono (by omega : n+m+1 ≤ W+2)).trans (Nat.le_succ _)
  have hSmall := overhead_at_word primitive c hPrimitive _ m Q hAddress hm hQ
  have hLarge := overhead_at_word primitive c hPrimitive _ n Q hAddress hn hQ
  have hWord := (hPrimitive (binaryWordWidth (n+m+1))).trans (Nat.mul_le_mul_left c hnm)
  unfold wrapperWork metadataBound
  change _ ≤ 128*(c+1)*(n+m+3)*Q
  nlinarith only [hSmall,hLarge,hWord,hAddress,hQ]

theorem emit_work_bound {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w)
    (y : Fin m → ℚ) (W : ℕ) (hCount : n+m ≤ W) :
    (emit p model primitive (StoredArrayReferenceList.poolAddressWidth (n+m+1) W) y).2 ≤
      p.emitBitCost model y+metadataBound c n m W := by
  have hIndex : binaryWordWidth ((n+m+1)+1) ≤ binaryWordWidth (W+2)+1 :=
    (binaryWordWidth_mono (by omega : (n+m+1)+1 ≤ W+2)).trans (Nat.le_succ _)
  have hWord : binaryWordWidth (W+1) ≤ binaryWordWidth (W+2)+1 :=
    (binaryWordWidth_mono (by omega : W+1 ≤ W+2)).trans (Nat.le_succ _)
  have hAddress := StoredArrayReferenceList.poolAddressWidth_log_bound (n+m+1) W
  rw [emit_work]
  have hMeta := constructor_metadata_bound primitive c hPrimitive
    (StoredArrayReferenceList.poolAddressWidth (n+m+1) W) n m W hCount (by omega)
  omega

theorem emitMixed_work_bound {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w)
    (pivot : Fin n) (y : Fin (m+1) → ℚ) (W : ℕ) (hCount : n+(m+1) ≤ W) :
    (emitMixed p model primitive (StoredArrayReferenceList.poolAddressWidth (n+(m+1)+1) W) pivot y).2 ≤
      p.emitMixedBitCost model pivot y+metadataBound c n (m+1) W := by
  have hIndex : binaryWordWidth ((n+(m+1)+1)+1) ≤ binaryWordWidth (W+2)+1 :=
    (binaryWordWidth_mono (by omega : (n+(m+1)+1)+1 ≤ W+2)).trans (Nat.le_succ _)
  have hWord : binaryWordWidth (W+1) ≤ binaryWordWidth (W+2)+1 :=
    (binaryWordWidth_mono (by omega : W+1 ≤ W+2)).trans (Nat.le_succ _)
  have hAddress := StoredArrayReferenceList.poolAddressWidth_log_bound (n+(m+1)+1) W
  rw [emitMixed_work]
  have hMeta := constructor_metadata_bound primitive c hPrimitive
    (StoredArrayReferenceList.poolAddressWidth (n+(m+1)+1) W) n (m+1) W hCount (by omega)
  omega

end Blotto.PaperStoredGroupEmission
