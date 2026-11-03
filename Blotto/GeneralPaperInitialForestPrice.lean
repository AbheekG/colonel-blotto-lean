import Blotto.GeneralPaperPreparedSharedExecution

/-! Construct the native four-tree initial forest in the reference-array
model. Height arithmetic, each uniform node and all array index/reference
operations are charged. The local word is derived from m and lambda.
-/
namespace Blotto.GeneralPaperInitialForestPrice
open GeneralPaperIntervalCache GeneralPaperCatalogueTreeCache
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def arrayRun (index : ℕ → ℕ) (W m height : ℕ) : FixedArrayTable m (Node height) × ℕ :=
  PaperIndexedArrayConstruction.run index W (fun _ => (.uniform height 0,16*W))

theorem array_data (index : ℕ → ℕ) (W m height : ℕ) :
    (arrayRun index W m height).1=FixedArrayTable.ofFn (fun _ => Node.uniform height 0) :=
  PaperIndexedArrayConstruction.run_data _ _ _

theorem array_work (index : ℕ → ℕ) (W m height : ℕ) (hW : 1≤W)
    (hIndex : ∀ i≤m,index (binaryWordWidth (i+1))≤W) :
    (arrayRun index W m height).2≤m*(16*W)+44*(m+1)*W :=
  GeneralPaperControlArrayPrice.indexed_work index W (16*W) _ hW hIndex (fun _ => Nat.le_refl _)

def run (index primitive : ℕ → ℕ) (W m depth : ℕ) : Trees m depth × ℕ :=
  let signedHeight := depth+1
  let p := arrayRun index W m depth
  let q := arrayRun index W m depth
  let lambda := arrayRun index W m signedHeight
  let mu := arrayRun index W m signedHeight
  (⟨p.1,q.1,lambda.1,mu.1⟩,p.2+q.2+lambda.2+mu.2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) depth 1+128*W)

theorem data (index primitive : ℕ → ℕ) (W m depth : ℕ) :
    (run index primitive W m depth).1=initial m depth := by
  simp only [run,array_data,initial]

theorem work (index primitive : ℕ → ℕ) (W m depth : ℕ) (hW : 1≤W)
    (hIndex : ∀ i≤m,index (binaryWordWidth (i+1))≤W) :
    (run index primitive W m depth).2≤512*(m+1)*W+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) depth 1 := by
  have hU := array_work index W m depth hW hIndex
  have hS := array_work index W m (depth+1) hW hIndex
  change (arrayRun index W m depth).2+(arrayRun index W m depth).2+
    (arrayRun index W m (depth+1)).2+(arrayRun index W m (depth+1)).2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) depth 1+128*W≤_
  nlinarith only [hU,hS]

def word (m depth : ℕ) : ℕ := 128+8*(binaryWordWidth (m+1)+binaryWordWidth (depth+1))

theorem bit_work (model : RationalCostModel) (m depth : ℕ) :
    (run (fun a => a) model.rat (word m depth) m depth).2≤1024*(m+1)*model.rat (2*word m depth) := by
  let W := word m depth
  let P := model.rat (2*W)
  have hW : 1≤W := by dsimp [W,word]; omega
  have hi : ∀ i≤m,binaryWordWidth (i+1)≤W := by
    intro i hi
    have hh := binaryWordWidth_mono (Nat.add_le_add_right hi 1)
    dsimp [W,word]
    omega
  have h := work (fun a => a) model.rat W m depth hW hi
  have hDepth := binaryWordWidth_mono (show depth≤depth+1 by omega)
  have h1 : binaryWordWidth 1=1 := by decide
  have hRaw := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b) depth 1 (2*W)
    (by dsimp [W,word]; omega) (by omega) (by dsimp [W,word]; omega)
  have hPrice : W≤P := (show W≤2*W by omega).trans (model.word_le (2*W))
  have hRecord := Nat.mul_le_mul_left (512*(m+1)) hPrice
  change _≤2*P at hRaw
  change _≤1024*(m+1)*P
  nlinarith only [h,hRaw,hRecord,Nat.zero_le (m*P)]

theorem arithmetic_work (m depth : ℕ) : (run (fun _ => 1) (fun _ => 1) 1 m depth).2≤1024*(m+1) := by
  have h := work (fun _ => 1) (fun _ => 1) 1 m depth (Nat.le_refl 1) (fun _ _ => Nat.le_refl 1)
  change _≤512*(m+1)*1+2 at h
  omega

theorem valid (index primitive : ℕ → ℕ) (W m k : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) :
    Valid a k (run index primitive W m a.lambda).1 := by rw [data]; exact initial_valid m a k

theorem paths (index primitive : ℕ → ℕ) (W m k : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) :
    Paths a k (run index primitive W m a.lambda).1 := by rw [data]; exact initial_paths m a k

theorem every_array_prefix (index : ℕ → ℕ) (W m height j : ℕ) (hj : j≤m) :
    (PaperIndexedArrayConstruction.fill index W (fun _ : Fin m => (Node.uniform height 0,16*W)) j hj).1.size=j := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperInitialForestPrice
