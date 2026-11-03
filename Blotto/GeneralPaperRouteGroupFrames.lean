import Blotto.GeneralPaperRouteMemberFrames

/-! Outer stored-group traversal and the actual member recursions. Scalar
charges add once across the source; table payload stays outside these frames.
Packed provenance bounds each member list, and native groups number at most
three when the generic reserve is instantiated. -/
namespace Blotto.GeneralPaperRouteGroupFrames
open GeneralPaperEqualRouteConstruction (groups)
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

def frameProfile (A n m F s : ℕ) : ℕ := 1 + 2 * s + 8 * (natBits (n + m + F + A + 1) + A) + 160 * A

def baseFoot (A n m : ℕ) : ℕ := fields A [n, m, 32 * A + 32] + 64 * A

def stepFoot {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) (g : Fin i.groups.length)
    (rest : List (Fin i.groups.length)) (table : FixedArrayTable n (GroupRoute i.groups.length)) : ℕ :=
  let made := GeneralPaperEqualRouteMembers.run model A values g (p.groups.read g).2 (p.groups.read g).1 table
  let child := groups p model A values rest made.1
  let H := 64 * (A + binaryWordWidth (g.val + 1) + 1)
  let actual := groups p model A values (g :: rest) table
  rationalWordWidth (p.groups.read g).2 + fields A [n, i.groups.length, g.val, made.2, child.2, H, made.2 + child.2, actual.2] + 128 * A

theorem member_length {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) (g : Fin i.groups.length) :
    (p.groups.read g).1.length ≤ n := by
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun g => (p.groups.read g).1.length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
  exact h.trans (GeneralPaperEqualPackedOwner.members_le p)

theorem base_bound (A n m F s : ℕ) (hF : 32 * A + 32 ≤ F) : baseFoot A n m ≤ frameProfile A n m F s := by
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (n + m + F + A + 1) [n, m, 32 * A + 32] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 3 * (natBits (n + m + F + A + 1) + A) + 32 * A at hFields
  unfold baseFoot frameProfile
  omega

theorem step_bound {n s : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A F : ℕ) (values : FixedArrayTable n ℚ) (g : Fin i.groups.length)
    (rest : List (Fin i.groups.length)) (table : FixedArrayTable n (GroupRoute i.groups.length))
    (hTotal : RationalHeight (p.groups.read g).2 s) (hF : (groups p model A values (g :: rest) table).2 ≤ F) :
    stepFoot p model A values g rest table ≤ frameProfile A n i.groups.length F s := by
  let made := GeneralPaperEqualRouteMembers.run model A values g (p.groups.read g).2 (p.groups.read g).1 table
  let child := groups p model A values rest made.1
  let H := 64 * (A + binaryWordWidth (g.val + 1) + 1)
  let C := (groups p model A values (g :: rest) table).2
  have hC : C = made.2 + child.2 + H := rfl
  have hWord := rationalWordWidth_of_height hTotal
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (n + i.groups.length + F + A + 1)
    [n, i.groups.length, g.val, made.2, child.2, H, made.2 + child.2, C] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 8 * (natBits (n + i.groups.length + F + A + 1) + A) + 32 * A at hFields
  change rationalWordWidth (p.groups.read g).2 + fields A [n, i.groups.length, g.val, made.2, child.2, H, made.2 + child.2, C] + 128 * A ≤ _
  unfold frameProfile
  omega

def frames {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) :
    List (Fin i.groups.length) → FixedArrayTable n (GroupRoute i.groups.length) → ℕ
  | [], _ => baseFoot A n i.groups.length
  | g :: rest, table =>
      let made := GeneralPaperEqualRouteMembers.run model A values g (p.groups.read g).2 (p.groups.read g).1 table
      stepFoot p model A values g rest table +
        GeneralPaperRouteMemberFrames.frames model A values g (p.groups.read g).2 (p.groups.read g).1 table +
        frames p model A values rest made.1

def profile (A n m F s : ℕ) : ℕ := 32 * F + m * (n + 1) * GeneralPaperRouteMemberFrames.frameProfile A n m F +
  (m + 1) * frameProfile A n m F s

theorem bounded {n s : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A F : ℕ) (values : FixedArrayTable n ℚ)
    (gs : List (Fin i.groups.length)) (table : FixedArrayTable n (GroupRoute i.groups.length))
    (ht : ∀ g, RationalHeight (p.groups.read g).2 s) (hF : (groups p model A values gs table).2 ≤ F) :
    frames p model A values gs table ≤ 32 * (groups p model A values gs table).2 +
      gs.length * (n + 1) * GeneralPaperRouteMemberFrames.frameProfile A n i.groups.length F +
      (gs.length + 1) * frameProfile A n i.groups.length F s := by
  induction gs generalizing table with
  | nil =>
    have hBase := base_bound A n i.groups.length F s hF
    simp only [frames, groups, List.length_nil, Nat.zero_mul, Nat.zero_add, one_mul]
    omega
  | cons g rest ih =>
    let made := GeneralPaperEqualRouteMembers.run model A values g (p.groups.read g).2 (p.groups.read g).1 table
    let child := groups p model A values rest made.1
    have hShape : (groups p model A values (g :: rest) table).2 = made.2 + child.2 + 64 * (A + binaryWordWidth (g.val + 1) + 1) := rfl
    have hStep := step_bound p model A F values g rest table (ht g) hF
    have hMember := GeneralPaperRouteMemberFrames.bounded model A F values g (p.groups.read g).2 (p.groups.read g).1 table (by change made.2 ≤ F; omega)
    have hMemberSize := Nat.mul_le_mul_right (GeneralPaperRouteMemberFrames.frameProfile A n i.groups.length F)
      (Nat.add_le_add_right (member_length p g) 1)
    have hChild : child.2 ≤ F := by omega
    have hRest := ih made.1 hChild
    simp only [frames, List.length_cons]
    nlinarith only [hStep, hMember, hMemberSize, hRest, hShape]

end Blotto.GeneralPaperRouteGroupFrames
