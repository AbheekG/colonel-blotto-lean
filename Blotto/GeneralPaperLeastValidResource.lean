import Blotto.GeneralPaperCodeOrder

/-! A cell's executed least-valid representative can only decrease the
paper's exact symbolic resource. This joins lookup minimality to tag order
for both candidate and response catalogues, including mixed-mode decoding.
-/
namespace Blotto.GeneralPaperLeastValidResource
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperCodeMinimumScan
set_option autoImplicit false

theorem inclusive_domination (a : Alphabet) (response : Bool) (lo hi : ℕ) (entry : Entry)
    (hSome : (GeneralPaperLeastValid.run a response lo hi).selected=some entry)
    (code : ℕ) (choice : Choice) (hLo : lo≤code) (hHi : code≤hi)
    (hDecode : (decode a response code).choice=some choice) : entry.predecessor.tag≤choice.tag := by
  have hCost := GeneralPaperLeastValidSpec.run_minimal a response lo hi entry hSome code hLo hHi
    (GeneralPaperCodeDecodeSound.decode_valid a response code choice hDecode)
  exact GeneralPaperCodeOrder.decode_monotone a response response entry.cost code entry.predecessor choice
    (GeneralPaperLeastValidSpec.run_sound a response lo hi entry hSome).2.2 hDecode hCost

theorem cell_domination (a : Alphabet) (response : Bool) (lo hi : ℕ) (entry : Entry)
    (hSome : (GeneralPaperLeastValidCell.run a response lo hi).selected=some entry)
    (code : ℕ) (choice : Choice) (hLo : lo≤code) (hHi : code<hi)
    (hDecode : (decode a response code).choice=some choice) : entry.predecessor.tag≤choice.tag := by
  have hCost := GeneralPaperLeastValidCell.run_minimal a response lo hi entry hSome ⟨code,choice⟩ ⟨hLo,hHi,hDecode⟩
  exact GeneralPaperCodeOrder.decode_monotone a response response entry.cost code entry.predecessor choice
    (GeneralPaperLeastValidCell.run_sound a response lo hi entry hSome).2.2 hDecode hCost

end Blotto.GeneralPaperLeastValidResource
