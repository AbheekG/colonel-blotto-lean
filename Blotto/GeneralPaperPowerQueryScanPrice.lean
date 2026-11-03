import Blotto.GeneralPaperPowerQueryBounds

/-! Full bit-priced scan on a retained power table. Every chosen product
is computed once. Guards, subtraction, native metadata sums and all writes
are charged, including skipped columns and the empty return. The budget
invariant covers every recursively reached accumulator exponent.
-/
namespace Blotto.GeneralPaperPowerQueryScanPrice
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable GeneralPaperPowerQueryBounds
open GeneralPaperPowerTableBounds
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def run (primitive : ℕ → ℕ) (W unit p : ℕ) : List Entry → ℕ → Number → GeneralPaperRoundedPowerQuery.Result × ℕ
  | [],remaining,acc => (⟨acc,remaining,2⟩,16*W)
  | entry::rest,remaining,acc =>
    let test := GeneralPaperIntegerWordPrice.compare primitive entry.degree remaining
    if entry.degree≤remaining then
      let product := GeneralPaperDyadicMultiplyPrice.run primitive W unit p acc entry.number
      let later := run primitive W unit p rest (remaining-entry.degree) product.1.number
      (⟨later.1.number,later.1.remaining,product.1.work+later.1.work+16⟩,
        product.2+later.2+test+
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) remaining entry.degree+
        metadataCost primitive product.1.work later.1.work 16+96*W)
    else
      let later := run primitive W unit p rest remaining acc
      (⟨later.1.number,later.1.remaining,later.1.work+8⟩,
        later.2+test+metadataCost primitive later.1.work 0 8+32*W)

theorem data (primitive : ℕ → ℕ) (W unit p : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (entries : List Entry) (hEntries : ∀ e∈entries,Normal unit e.number) (remaining : ℕ) (acc : Number)
    (hAcc : Normal unit acc) :
    (run primitive W unit p entries remaining acc).1=GeneralPaperRoundedPowerQuery.scan unit p entries remaining acc := by
  induction entries generalizing remaining acc with
  | nil => rfl
  | cons entry rest ih =>
    have hEntry := hEntries entry List.mem_cons_self
    have hRest : ∀ e∈rest,Normal unit e.number := fun e he => hEntries e (List.mem_cons_of_mem _ he)
    rw [run,GeneralPaperRoundedPowerQuery.scan]
    dsimp only
    split
    · rw [GeneralPaperDyadicMultiplyPrice.data primitive W unit p hUnit hPower acc entry.number hAcc hEntry]
      rw [ih hRest _ _ (GeneralPaperDyadicMultiply.multiply_normal unit p hUnit hPower acc entry.number hAcc hEntry)]
    · rw [ih hRest remaining acc hAcc]

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W unit p columns D E R : ℕ)
    (hUnit : 0<unit) (hPower : unit=2^p) (entries : List Entry) (hEntries : Entries unit D E entries)
    (hLen : entries.length≤columns) (remaining : ℕ) (hRemaining : remaining≤D) (acc : Number)
    (hAcc : Normal unit acc) (hBudget : acc.exponent.natAbs+entries.length*(E+p+1)≤R) :
    (run primitive W unit p entries remaining acc).2≤1024*(entries.length+1)*
      (W+primitive (GeneralPaperPowerQueryBounds.width p columns D R)) := by
  let L := GeneralPaperPowerQueryBounds.width p columns D R
  let P := primitive L
  let F := W+P
  induction entries generalizing remaining acc with
  | nil => change 16*W≤1024*(0+1)*F; dsimp only [F]; omega
  | cons entry rest ih =>
    have hn := hEntries.normal entry List.mem_cons_self
    have hd := hEntries.degree entry List.mem_cons_self
    have he := hEntries.exponent entry List.mem_cons_self
    have hRest := tail unit D E entry rest hEntries
    have hRestLen : rest.length≤columns := by simp only [List.length_cons] at hLen; omega
    have hR := hBudget
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hR
    have hE : E≤R := by omega
    have hA : acc.exponent.natAbs≤R := by omega
    have hTest := GeneralPaperIntegerWordPrice.compare_le primitive hMono entry.degree remaining L
      ((Nat.add_le_add_left (binaryWordWidth_mono hd) 1).trans (by dsimp [L,GeneralPaperPowerQueryBounds.width]; omega))
      ((Nat.add_le_add_left (binaryWordWidth_mono hRemaining) 1).trans (by dsimp [L,GeneralPaperPowerQueryBounds.width]; omega))
    have hMetaWord := metadata_word p columns D R
    change 1+binaryWordWidth (metadataCap p columns)≤L at hMetaWord
    have hW : W≤F := Nat.le_add_right _ _
    have hP : P≤F := Nat.le_add_left _ _
    rw [run]
    dsimp only
    change _≤1024*(rest.length+1+1)*F
    split
    · have hNextNormal := GeneralPaperDyadicMultiply.multiply_normal unit p hUnit hPower acc entry.number hAcc hn
      have hNext := GeneralPaperDyadicFastMultiply.exponent_bound unit p acc entry.number
      have hNextBudget : (GeneralPaperDyadicMultiply.multiply unit p acc entry.number).number.exponent.natAbs+
          rest.length*(E+p+1)≤R := by omega
      have hi := ih hRest hRestLen (remaining-entry.degree) (by omega) _ hNextNormal hNextBudget
      have hMult := (GeneralPaperDyadicMultiplyPrice.work primitive hMono W unit p acc entry.number hAcc hn).trans
        (Nat.mul_le_mul_left 256 (Nat.add_le_add_left
          (hMono (GeneralPaperPowerQueryBounds.multiply_width unit p columns D R hPower acc entry.number hA (he.trans hE))) W))
      have hSub := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a-b) remaining entry.degree D hRemaining hd (by omega)
      have hSP := hMono (show 1+binaryWordWidth D≤L by dsimp [L,GeneralPaperPowerQueryBounds.width]; omega)
      have hSubCost := hSub.trans (Nat.mul_le_mul_left 2 hSP)
      have hNative := GeneralPaperRoundedPowerQuery.scan_work unit p rest (remaining-entry.degree)
        (GeneralPaperDyadicMultiply.multiply unit p acc entry.number).number
      have hProd := GeneralPaperDyadicMultiply.multiply_work unit p acc entry.number
      have hMeta := metadata_work primitive hMono
        (GeneralPaperDyadicMultiply.multiply unit p acc entry.number).work
        (GeneralPaperRoundedPowerQuery.scan unit p rest (remaining-entry.degree)
          (GeneralPaperDyadicMultiply.multiply unit p acc entry.number).number).work
        16 (metadataCap p columns) L (by unfold metadataCap; nlinarith only [hNative,hProd,hRestLen]) hMetaWord
      rw [GeneralPaperDyadicMultiplyPrice.data primitive W unit p hUnit hPower acc entry.number hAcc hn]
      rw [data primitive W unit p hUnit hPower rest hRest.normal _ _ hNextNormal]
      change _≤1024*(rest.length+1)*F at hi
      change _≤256*F at hMult
      change _≤2*P at hSubCost
      change _≤4*P at hMeta
      change _≤P at hTest
      nlinarith only [hi,hMult,hSubCost,hMeta,hTest,hW,hP]
    · have hRestBudget : acc.exponent.natAbs+rest.length*(E+p+1)≤R := by omega
      have hi := ih hRest hRestLen remaining hRemaining acc hAcc hRestBudget
      have hNative := GeneralPaperRoundedPowerQuery.scan_work unit p rest remaining acc
      have hMeta := metadata_work primitive hMono
        (GeneralPaperRoundedPowerQuery.scan unit p rest remaining acc).work 0 8
        (metadataCap p columns) L (by unfold metadataCap; nlinarith only [hNative,hRestLen]) hMetaWord
      rw [data primitive W unit p hUnit hPower rest hRest.normal remaining acc hAcc]
      change _≤1024*(rest.length+1)*F at hi
      change _≤4*P at hMeta
      change _≤P at hTest
      nlinarith only [hi,hMeta,hTest,hW,hP]

end Blotto.GeneralPaperPowerQueryScanPrice
