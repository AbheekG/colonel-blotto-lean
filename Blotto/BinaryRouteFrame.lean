import Blotto.BinaryRatFrame
import Blotto.RationalRouteStoreRAM

/-! Route records store an option tag, bounded group index and rational
coefficient. Exact readback retains the suffix; out-of-range indices are
rejected. Fixed-slot padding and the RAM bridge are handled separately. -/

namespace Blotto.BinaryRouteFrame

def encode {m : ℕ} (route : GroupRoute m) : List Bool :=
  match route.1 with
  | none => false :: BinaryRatFrame.encode route.2
  | some g => true :: (BinaryNatFrame.encode g.val ++ BinaryRatFrame.encode route.2)

def read (m : ℕ) : List Bool → Option (GroupRoute m × List Bool)
  | [] => none
  | false :: rest => (BinaryRatFrame.read rest).map (fun parsed => ((none, parsed.1), parsed.2))
  | true :: rest => (BinaryNatFrame.read rest).bind (fun parsed =>
      if h : parsed.1 < m then (BinaryRatFrame.read parsed.2).map
        (fun coeff => ((some ⟨parsed.1, h⟩, coeff.1), coeff.2)) else none)

theorem read_encode_append {m : ℕ} (route : GroupRoute m) (suffix : List Bool) :
    read m (encode route ++ suffix) = some (route, suffix) := by
  rcases route with ⟨group, coeff⟩
  cases group with
  | none => simp only [encode, List.cons_append, read, BinaryRatFrame.read_encode_append, Option.map_some]
  | some g =>
    simp only [encode, List.cons_append, List.append_assoc, read, BinaryNatFrame.read_encode_append,
      Option.bind_some, dite_eq_left g.isLt, BinaryRatFrame.read_encode_append, Option.map_some]

theorem encode_length_bound {m : ℕ} (route : GroupRoute m) :
    (encode route).length ≤ 2 * routePayloadWordWidth route + 1 := by
  rcases route with ⟨group, coeff⟩
  cases group <;> simp only [encode, List.length_cons, List.length_append, BinaryNatFrame.encode_length,
    BinaryRatFrame.encode_length, routePayloadWordWidth] <;> omega

theorem read_index_out_of_range (m index : ℕ) (h : m ≤ index) (tail : List Bool) :
    read m (true :: (BinaryNatFrame.encode index ++ tail)) = none := by
  simp only [read, BinaryNatFrame.read_encode_append, Option.bind_some, dite_eq_right (by omega : ¬index < m)]

theorem read_empty (m : ℕ) : read m [] = none := rfl

end Blotto.BinaryRouteFrame
