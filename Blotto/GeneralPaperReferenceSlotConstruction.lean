import Blotto.GeneralPaperMeasuredLayoutDistinct

/-! Construct an actual raw-reference write entry inside an array/list
header. Slot arithmetic and address encoding are executed and priced. The
stored target is an existing fixed-width raw word in the paper indexed model.
No generated-C representation or allocator calibration is asserted. -/
namespace Blotto.GeneralPaperReferenceSlotConstruction
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

structure Entry (A : ℕ) where
  position : ℕ
  location : FixedBinaryWord A
  target : FixedBinaryWord A

def run (model : RationalCostModel) (S A base fixed stride index cell : ℕ) (target : FixedBinaryWord A) : Entry A × ℕ :=
  let scaled := GeneralPaperNaturalScalarStep.run model S .mul stride index
  let prefixed := GeneralPaperNaturalScalarStep.run model S .add fixed scaled.1
  let offset := GeneralPaperNaturalScalarStep.run model S .add prefixed.1 cell
  let bits := GeneralPaperNaturalScalarStep.run model S .mul A offset.1
  let position := GeneralPaperNaturalScalarStep.run model S .add base bits.1
  let location := GeneralPaperStoredWordEncoding.word model S A position.1
  (⟨position.1,location.1,target⟩,
    scaled.2 + prefixed.2 + offset.2 + bits.2 + position.2 + location.2 + A + 64 * (S + A + 1))

theorem position (model : RationalCostModel) (S A base fixed stride index cell : ℕ) (target : FixedBinaryWord A) :
    (run model S A base fixed stride index cell target).1.position = base + A * (fixed + stride * index + cell) := rfl

theorem location (model : RationalCostModel) (S A base fixed stride index cell : ℕ) (target : FixedBinaryWord A) :
    (run model S A base fixed stride index cell target).1.location =
      FixedBinaryWord.ofNat A (base + A * (fixed + stride * index + cell)) := by
  simp only [run,GeneralPaperStoredWordEncoding.word_data,GeneralPaperNaturalScalarStep.run,GeneralPaperNaturalScalarStep.Op.apply]

theorem target (model : RationalCostModel) (S A base fixed stride index cell : ℕ) (value : FixedBinaryWord A) :
    (run model S A base fixed stride index cell value).1.target = value := rfl

theorem within (model : RationalCostModel) (S A base fixed stride count index cell : ℕ) (value : FixedBinaryWord A)
    (hIndex : index < count) (hCell : cell < stride) :
    base ≤ (run model S A base fixed stride index cell value).1.position ∧
      (run model S A base fixed stride index cell value).1.position + A ≤ base + A * (fixed + stride * count) := by
  rw [position]
  have hm := Nat.mul_le_mul_left stride (Nat.succ_le_of_lt hIndex)
  have hOffset : fixed + stride * index + cell + 1 ≤ fixed + stride * count := by nlinarith only [hm,hCell]
  have h := Nat.mul_le_mul_left A hOffset
  constructor
  · omega
  · nlinarith only [h]

theorem fits (model : RationalCostModel) (S A base fixed stride count index cell : ℕ) (value : FixedBinaryWord A)
    (hIndex : index < count) (hCell : cell < stride) (hCap : base + A * (fixed + stride * count) < 2 ^ A) :
    (run model S A base fixed stride index cell value).1.position < 2 ^ A := by
  have h := within model S A base fixed stride count index cell value hIndex hCell
  omega

theorem location_value (model : RationalCostModel) (S A base fixed stride count index cell : ℕ) (value : FixedBinaryWord A)
    (hIndex : index < count) (hCell : cell < stride) (hCap : base + A * (fixed + stride * count) < 2 ^ A) :
    (run model S A base fixed stride index cell value).1.location.value =
      (run model S A base fixed stride index cell value).1.position := by
  rw [location,position]
  apply FixedBinaryWord.value_ofNat
  simpa only [position] using fits model S A base fixed stride count index cell value hIndex hCell hCap

theorem ordered (model : RationalCostModel) (S A base fixed stride i c j d : ℕ) (x y : FixedBinaryWord A)
    (hOrder : stride * i + c < stride * j + d) :
    (run model S A base fixed stride i c x).1.position + A ≤
      (run model S A base fixed stride j d y).1.position := by
  rw [position,position]
  have h := Nat.mul_le_mul_left A (Nat.succ_le_of_lt hOrder)
  nlinarith only [h]

theorem disjoint (model : RationalCostModel) (S A base fixed stride i c j d : ℕ) (x y : FixedBinaryWord A)
    (hOrder : stride * i + c < stride * j + d) :
    Disjoint (Set.Ico (run model S A base fixed stride i c x).1.position
      ((run model S A base fixed stride i c x).1.position + A))
      (Set.Ico (run model S A base fixed stride j d y).1.position
      ((run model S A base fixed stride j d y).1.position + A)) := by
  have h := ordered model S A base fixed stride i c j d x y hOrder
  apply Set.disjoint_left.mpr
  intro z hz hi
  simp only [Set.mem_Ico] at hz hi
  omega

end Blotto.GeneralPaperReferenceSlotConstruction
