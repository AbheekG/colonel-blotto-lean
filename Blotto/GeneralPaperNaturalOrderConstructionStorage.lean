import Blotto.GeneralPaperNaturalListConstructionStorage

/-! Complete native natural ordering: clipping, endpoint augmentation,
stable sorting, adjacent deduplication and returned lists. All five list
buffers, recursion controls and the constructed sort-depth loop coexist
in this conservative reservation. Primitive scratch uses the complete
operation allowance under the paper convention. -/
namespace Blotto.GeneralPaperNaturalOrderConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def clipped (primitive : ℕ → ℕ) (W U : ℕ) (xs : List ℕ) : List ℕ :=
  (GeneralPaperPricedListMap.run W (GeneralPaperNaturalOrderPrice.clip primitive W U) xs).1
def augmented (primitive : ℕ → ℕ) (W U : ℕ) (xs : List ℕ) : List ℕ := 0::U::clipped primitive W U xs
def sorted (primitive : ℕ → ℕ) (W U : ℕ) (xs : List ℕ) : List ℕ :=
  (GeneralPaperPricedSort.run (GeneralPaperNaturalOrderPrice.leRun primitive) W (augmented primitive W U xs)).1

theorem clip_properties (primitive : ℕ → ℕ) (W U : ℕ) (xs : List ℕ) :
    (clipped primitive W U xs).length=xs.length ∧ ∀ x∈clipped primitive W U xs,x≤U := by
  constructor
  · exact GeneralPaperPricedListMap.length W _ xs
  · intro x hx
    rw [clipped,GeneralPaperPricedListMap.data] at hx
    obtain ⟨y,_,hy⟩ := List.mem_map.mp hx
    rw [←hy]
    exact Nat.min_le_right _ _

theorem augmented_properties (primitive : ℕ → ℕ) (W U : ℕ) (xs : List ℕ) :
    (augmented primitive W U xs).length=xs.length+2 ∧ ∀ x∈augmented primitive W U xs,x≤U := by
  have h := clip_properties primitive W U xs
  constructor
  · change (clipped primitive W U xs).length+1+1=xs.length+2
    omega
  · intro x hx
    rcases List.mem_cons.mp hx with hx|hx
    · rw [hx]; exact Nat.zero_le _
    · rcases List.mem_cons.mp hx with hx|hx
      · rw [hx]
      · exact h.2 x hx

theorem sorted_properties (primitive : ℕ → ℕ) (W U : ℕ) (xs : List ℕ) :
    (sorted primitive W U xs).length=xs.length+2 ∧ ∀ x∈sorted primitive W U xs,x≤U := by
  have h := augmented_properties primitive W U xs
  exact ⟨(GeneralPaperPricedSort.length (GeneralPaperNaturalOrderPrice.leRun primitive) W _).trans h.1,
    fun x hx => h.2 x ((GeneralPaperPricedSort.mem (GeneralPaperNaturalOrderPrice.leRun primitive) W _ x).mp hx)⟩

def depth (n : ℕ) : ℕ := GeneralPaperRaySearchControls.depth (n+3)
def sortPeak (model : RationalCostModel) (W U : ℕ) (xs : List ℕ) : ℕ :=
  let input := augmented model.rat W U xs
  let d := GeneralPaperRaySearchControls.depth (input.length+1)
  GeneralPaperSortConstructionStorage.peak W natBits (GeneralPaperNaturalOrderPrice.leRun model.rat) d d input
def sortProfile (model : RationalCostModel) (W U n : ℕ) : ℕ :=
  (depth n+1)*GeneralPaperSortConstructionStorage.coefficient W (natBits U) (model.rat (natBits U)) (depth n) (n+2)

theorem sort_bound (model : RationalCostModel) (W U : ℕ) (xs : List ℕ) :
    sortPeak model W U xs≤sortProfile model W U xs.length := by
  let input := augmented model.rat W U xs
  let d := GeneralPaperRaySearchControls.depth (input.length+1)
  have h := augmented_properties model.rat W U xs
  have hEncode : ∀ x∈input,natBits x≤natBits U := fun x hx => Nat.add_le_add_left (binaryWordWidth_mono (h.2 x hx)) 1
  have hCompare : ∀ x∈input,∀ y∈input,(GeneralPaperNaturalOrderPrice.leRun model.rat x y).2≤model.rat (natBits U) := by
    intro x hx y hy
    exact GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone x y (natBits U) (hEncode x hx) (hEncode y hy)
  have hb := GeneralPaperSortConstructionStorage.bounded W (natBits U) (model.rat (natBits U)) d d input.length natBits
    (GeneralPaperNaturalOrderPrice.leRun model.rat) input (Nat.le_refl _) (Nat.le_refl _)
    (GeneralPaperRaySearchControls.size_cap (input.length+1)) hEncode hCompare
  have hn : input.length=xs.length+2 := h.1
  have hd : d=depth xs.length := by dsimp [d,depth]; rw [hn]
  change sortPeak model W U xs≤_ at hb
  rw [hd,hn] at hb
  exact hb

def window (model : RationalCostModel) (W U : ℕ) (xs : List ℕ) : ℕ :=
  listFootprint W natBits xs+listFootprint W natBits (clipped model.rat W U xs)+
    listFootprint W natBits (augmented model.rat W U xs)+listFootprint W natBits (sorted model.rat W U xs)+
    listFootprint W natBits (GeneralPaperNaturalOrderPrice.unique model.rat W (sorted model.rat W U xs)).1+
    GeneralPaperNaturalListConstructionStorage.clipPeak W U xs+sortPeak model W U xs+
    GeneralPaperCeilingConstructionStorage.peak W (xs.length+3) 1 (by decide)+
    GeneralPaperNaturalListConstructionStorage.uniquePeak W (sorted model.rat W U xs)+
    (GeneralPaperNaturalOrderPrice.run model.rat W U xs).2+256*W

def profile (model : RationalCostModel) (W U n : ℕ) : ℕ :=
  let P := natBits U
  let N := n+2
  5*(N*(P+2*W)+32*W)+(n*(2*P+64*W)+64*W)+sortProfile model W U n+
    (binaryWordWidth (n+3)+1)*(5*GeneralPaperCeilingConstructionStorage.word (n+3)+192*W)+
    (N*(2*P+64*W)+P+128*W)+GeneralPaperNaturalOrderPrice.profile n W (model.rat P)+256*W

theorem bounded (model : RationalCostModel) (W U : ℕ) (xs : List ℕ) (hx : ∀ x∈xs,x≤U) :
    window model W U xs≤profile model W U xs.length := by
  have hClip := clip_properties model.rat W U xs
  have hAug := augmented_properties model.rat W U xs
  have hSort := sorted_properties model.rat W U xs
  have hUnique := GeneralPaperNaturalListConstructionStorage.unique_properties model.rat W (sorted model.rat W U xs)
  have own (ys : List ℕ) (hn : ys.length≤xs.length+2) (hy : ∀ y∈ys,y≤U) :
      listFootprint W natBits ys≤(xs.length+2)*(natBits U+2*W)+32*W :=
    (list_bound W (natBits U) natBits ys (fun y hy' => Nat.add_le_add_left (binaryWordWidth_mono (hy y hy')) 1)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have a := own xs (by omega) hx
  have b := own (clipped model.rat W U xs) (by omega) hClip.2
  have c := own (augmented model.rat W U xs) hAug.1.le hAug.2
  have d := own (sorted model.rat W U xs) hSort.1.le hSort.2
  have e := own (GeneralPaperNaturalOrderPrice.unique model.rat W (sorted model.rat W U xs)).1
    (hUnique.1.trans_eq hSort.1) (fun y hy => hSort.2 y (hUnique.2 y hy))
  have hBuffers := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add a b) c) d) e
  have hMap := GeneralPaperNaturalListConstructionStorage.clip_bound W U xs hx
  have hSortPeak := sort_bound model W U xs
  have hCeil := GeneralPaperCeilingConstructionStorage.bounded W (xs.length+3) 1 (by decide) (by omega)
  have hDepth := GeneralPaperPowerCeiling.loop_depth (xs.length+3) 1 (by decide)
  have hC := hCeil.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hDepth 1))
  have hD := GeneralPaperNaturalListConstructionStorage.unique_bound W U (sorted model.rat W U xs) hSort.2
  rw [hSort.1] at hD
  have hScratch := GeneralPaperNaturalOrderPrice.work model.rat model.monotone W U xs hx
  change _≤GeneralPaperNaturalOrderPrice.profile xs.length W (model.rat (natBits U)) at hScratch
  have h0 := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hBuffers hMap) hSortPeak) hC) hD
  have hSum := Nat.add_le_add_right (Nat.add_le_add h0 hScratch) (256*W)
  exact hSum.trans_eq (by unfold profile; ring)

end Blotto.GeneralPaperNaturalOrderConstructionStorage
