import checkpoints.shen_extension.ThinSuppliers
import checkpoints.shen_extension.CollarBound
import checkpoints.shen_extension.ShapeClimbAvoid

/-!
# The thin bound: an order bound at degree `r ≤ 2q - 1` from floors for roots that are not tight

`ThinSuppliers.no_tight_thin` excludes tight roots (`ThinSuppliers.TightR`: second layer
`r - 1`, third layer at most `r - 1`) from an out-regular digraph of degree `r`, `r ≤ 2q - 1`,
once the floors pay for it: tight roots are the savers, classes go by second layer, the bank of a
class is the set of complete heads of its root (at least `2q + 2 - r`), and `π = 1`. Here that is
turned into an order bound for every digraph of minimum out-degree `r`, as
`TightBound.tight_bound` does for `CollarTwo.no_tight`.

* `tightAt q r k`: what a tight root has within radius `k` beyond the global floors: `2r` at
  radius two, `3r - 1` at radius three (`ThinSuppliers.tight_third`), `4r - 2` from radius four
  on when `4 ≤ q` and `3r ≤ 5q + 2` (`ThinSuppliers.tight_ball_four`). `tightAt_le`.
* `ThinOK q r fs g m`: the arithmetic test of `no_tight_thin` at order `m`, at the middle radii
  `i = q/2`, `j = q - q/2` and the radii `i + 1`, `j + 1`, with `fs` the floors of every root
  (raised by `tightAt` at tight roots) and `g` the floors of roots that avoid
  `ShapeClimbAvoid.tightA r`.
* `thin_bound`: if `ThinOK q r fs g m` and `m ≤ boundOf q r g`, every `q`-free digraph of
  minimum out-degree `r` has more than `m` labels (`4 ≤ q`, so that `2 ≤ i`; `r ≤ 2q - 1`).

The floors are hypotheses here. Everything is generic in `q` and `r`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.ThinBound
open Finset BRq2 BRq3 FifthStripAll RigidHost
open DotTwoPassShellTransport (layer)
open MixedRadiusCompletion (Floor)
open ShapeClimbAvoid (AvoidFloor tightA)
open ThinSuppliers (TightR)

/-- Ball floors of a tight root at radius `k`, beyond the global floors. -/
def tightAt (q r k : ℕ) : ℕ :=
  if k = 2 then 2 * r
  else if k = 3 then 3 * r - 1
  else if 4 ≤ k then (if 4 ≤ q ∧ 3 * r ≤ 5 * q + 2 then 4 * r - 2 else 3 * r - 1)
  else 0

theorem tightAt_le {D : CH.Digraph} {V : Finset ℕ} {q r u : ℕ} (free : QFree D V q)
    (hq : 3 ≤ q) (hr : r + 1 ≤ 2 * q) (reg : ∀ v ∈ V, (outN D V v).card = r) (hu : u ∈ V)
    (tight : TightR D V r u) (k : ℕ) : tightAt q r k ≤ (ball D V u k).card := by
  have L := ThinSuppliers.balls_by_layers free (by omega) reg hu
  have z3 := ThinSuppliers.tight_third free hq reg hu tight hr
  have y := tight.1
  unfold tightAt
  split_ifs with h2 h3 h4 hc
  · subst h2; omega
  · subst h3; omega
  · have := (ThinSuppliers.tight_ball_four free hc.1 reg hu tight hr hc.2).2
    have := card_le_card (ball_mono_radius (D := D) (W := V) (u := u) h4)
    omega
  · have := card_le_card (ball_mono_radius (D := D) (W := V) (u := u) (show 3 ≤ k by omega))
    omega
  · omega

/-- Floors of a tight root: the global floor or `tightAt`, whichever is larger. -/
def tightF (q r : ℕ) (fs : List ℕ) (k : ℕ) : ℕ := max (fs.getD k 0) (tightAt q r k)

/-- The arithmetic test of the thin-supplier count at order `m`, at the middle radii. `fs` are
the floors of every root, `g` the floors of roots that are not tight. -/
def ThinOK (q r : ℕ) (fs g : List ℕ) (m : ℕ) : Prop :=
  let i := q / 2
  let j := q - q / 2
  let δ := m + 1 - (tightF q r fs i + tightF q r fs j)
  m + 1 ≤ g.getD i 0 + g.getD j 0 ∧
    m + 1 + 2 * r ≤ tightF q r fs (i + 1) + tightF q r fs (j + 1) + 1 + j ∧
    ∀ k ∈ range (δ + 2), k * (δ + 1) < k * k + (2 * q + 2 - r)

instance {q r fs g m} : Decidable (ThinOK q r fs g m) := by unfold ThinOK; infer_instance

/-- **The thin bound.** -/
theorem thin_bound {q r m : ℕ} {fs g : List ℕ} (hq : 4 ≤ q) (hr : r + 1 ≤ 2 * q)
    (floors : ∀ i, Floor q r i (fs.getD i 0))
    (loose : ∀ i, AvoidFloor q r (tightA r) i (g.getD i 0))
    (ok : ThinOK q r fs g m) (le : m ≤ ShapeClimbMono.boundOf q r g)
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V q) (ne : V.Nonempty)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card) : m < V.card := by
  by_contra small
  obtain ⟨E, freeE, regE⟩ := CollarBound.exists_regular free deg
  have degE : ∀ v ∈ V, r ≤ (outN E V v).card := fun v hv => (regE v hv).ge
  obtain ⟨loosepay, bankrow, pay⟩ := ok
  have tf : ∀ k, ∀ v ∈ V, TightR E V r v → tightF q r fs k ≤ (ball E V v k).card :=
    fun k v hv t => max_le (floors k E V freeE degE v hv)
      (tightAt_le freeE (by omega) hr regE hv t k)
  have payAll : ∀ k, k * (m + 1 - (tightF q r fs (q/2) + tightF q r fs (q - q/2)) + 1) <
      k * k + (2 * q + 2 - r) := by
    intro k
    by_cases hk : k ∈ range (m + 1 - (tightF q r fs (q/2) + tightF q r fs (q - q/2)) + 2)
    · exact pay k hk
    · have big : m + 1 - (tightF q r fs (q/2) + tightF q r fs (q - q/2)) + 1 < k := by
        have := mem_range.not.mp hk
        omega
      have : k * (m + 1 - (tightF q r fs (q/2) + tightF q r fs (q - q/2)) + 1) < k * k :=
        (Nat.mul_lt_mul_left (by omega : 0 < k)).mpr big
      omega
  have nt : ∀ v ∈ V, ¬ TightR E V r v :=
    ThinSuppliers.no_tight_thin (i := q/2) (j := q - q/2)
      (a := tightF q r fs (q/2)) (b := tightF q r fs (q - q/2))
      (a' := tightF q r fs (q/2 + 1)) (b' := tightF q r fs (q - q/2 + 1))
      (A := g.getD (q/2) 0 + g.getD (q - q/2) 0)
      (δ := m + 1 - (tightF q r fs (q/2) + tightF q r fs (q - q/2)))
      freeE (by omega) hr regE (by omega) (by omega) (by omega)
      (tf (q/2)) (tf (q - q/2)) (tf (q/2 + 1)) (tf (q - q/2 + 1))
      (fun v hv nt => Nat.add_le_add
        (ShapeClimbAvoid.ball_of_tight (loose (q/2)) freeE regE hv nt)
        (ShapeClimbAvoid.ball_of_tight (loose (q - q/2)) freeE regE hv nt))
      (by omega) (by omega) (by omega) payAll
  have bound := CollarBound.boundOf_local (fs := g) (by omega) freeE ne degE
    (fun k v hv => ShapeClimbAvoid.ball_of_tight (loose k) freeE regE hv (nt v hv))
  omega

#print axioms tightAt_le
#print axioms thin_bound
end LeanCH.BR.ThinBound
