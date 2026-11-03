import Blotto.GeneralPaperCodeMinimumScan

/-! The paper's least-valid lookup inspects four codes in the starting
bucket and the next grid code. Its exactness follows from actual decoding
and the fact that the next closed grid code is always valid. No alphabet
enumeration, Farey enumeration, or externally supplied lookup is used.
-/
namespace Blotto.GeneralPaperLeastValid
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperCodeDecodeSound
open GeneralPaperCodeMinimumScan
open GeneralPaperOrderedMinimum (Best)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 2048

def points (t : ℕ) : List ℕ := [4*t,4*t+1,4*t+2,4*t+3,4*t+4]

def run (a : Alphabet) (response : Bool) (lo hi : ℕ) : GeneralPaperCodeMinimumScan.Result :=
  if lo≤4*a.C then
    let split := GeneralPaperCodeSplit.run lo a.lambda
    let found := scan a response lo hi (points split.bucket)
    ⟨found.selected,split.work+found.work+32⟩
  else ⟨none,16⟩

theorem points_length (t : ℕ) : (points t).length=5 := rfl

theorem points_mem (t code : ℕ) (hLo : 4*t≤code) (hHi : code≤4*t+4) : code∈points t := by
  have he : code=4*t ∨ code=4*t+1 ∨ code=4*t+2 ∨ code=4*t+3 ∨ code=4*t+4 := by omega
  simpa only [points,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using he

theorem cover (a : Alphabet) (response : Bool) (lo hi t : ℕ)
    (hBase : 4*t≤lo) (hTop : lo≤4*t+3) (entry : Entry) (hPossible : Possible a response lo hi entry) :
    ∃ listed, Listed a response lo hi (points t) listed ∧ listed.cost≤entry.cost := by
  by_cases hNear : entry.cost≤4*t+4
  · exact ⟨entry,⟨entry.cost,points_mem t entry.cost (hBase.trans hPossible.1) hNear,
      (evaluate_iff a response lo hi entry.cost entry).mpr ⟨rfl,hPossible⟩⟩,le_rfl⟩
  · have hValid := decode_valid a response entry.cost entry.predecessor hPossible.2.2
    have hCap := valid_code_bound a response entry.cost hValid
    have hHi := hPossible.2.1
    have ht : t+1≤a.C := by omega
    let next : Entry := ⟨4*t+4,⟨grid a (t+1),false⟩⟩
    have hNext : Possible a response lo hi next := by
      refine ⟨by dsimp only [next]; omega,by dsimp only [next]; omega,?_⟩
      change (decode a response (4*t+4)).choice=some ⟨grid a (t+1),false⟩
      have he : 4*t+4=4*(t+1) := by omega
      rw [he]
      exact decode_grid a response (t+1) ht
    refine ⟨next,⟨4*t+4,points_mem t _ (by omega) le_rfl,?_⟩,by dsimp only [next]; omega⟩
    exact (evaluate_iff a response lo hi (4*t+4) next).mpr ⟨rfl,hNext⟩

theorem points_best (a : Alphabet) (response : Bool) (lo hi t : ℕ)
    (hBase : 4*t≤lo) (hTop : lo≤4*t+3) :
    Best (Possible a response lo hi) (scan a response lo hi (points t)).selected := by
  have hb := scan_best a response lo hi (points t)
  cases hs : (scan a response lo hi (points t)).selected with
  | none =>
    rw [hs] at hb
    intro entry he
    obtain ⟨listed,hListed,_⟩ := cover a response lo hi t hBase hTop entry he
    exact hb listed hListed
  | some chosen =>
    rw [hs] at hb
    refine ⟨listed_possible a response lo hi (points t) chosen hb.1,?_⟩
    intro entry he
    obtain ⟨listed,hListed,hLe⟩ := cover a response lo hi t hBase hTop entry he
    exact (hb.2 listed hListed).trans hLe

theorem run_best (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    Best (Possible a response lo hi) (run a response lo hi).selected := by
  dsimp only [run]
  split
  · rename_i hLo
    have he := GeneralPaperCodeSplit.run_spec a lo hLo
    exact points_best a response lo hi (GeneralPaperCodeSplit.run lo a.lambda).bucket (by omega) (by omega)
  · rename_i hLo
    intro entry he
    have hCap := valid_code_bound a response entry.cost (decode_valid a response entry.cost entry.predecessor he.2.2)
    have hRange := he.1
    omega

theorem run_work (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    (run a response lo hi).work≤934*a.lambda+2702 := by
  dsimp only [run]
  split
  · have hs := GeneralPaperCodeSplit.run_work lo a.lambda
    have hw := scan_work a response lo hi (points (GeneralPaperCodeSplit.run lo a.lambda).bucket)
    rw [points_length] at hw
    dsimp only
    omega
  · dsimp only
    omega

end Blotto.GeneralPaperLeastValid
