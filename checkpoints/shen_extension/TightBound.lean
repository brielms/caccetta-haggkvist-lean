import checkpoints.shen_extension.CollarBound
import checkpoints.shen_extension.CollarTwo
import checkpoints.shen_extension.ShapeClimbAvoid

/-!
# The tight bound: an order bound at degree `q + 2` from floors for roots that are not tight

`CollarTwo.no_tight` excludes tight roots (`CollarTwo.Tight`: second layer `q + 1`, third layer
at most `q + 1`) from an out-regular digraph of degree `q + 2` once the floors pay for it. Here
that is turned into an order bound for every digraph of minimum out-degree `q + 2`, as
`CollarBound.collar_bound` does one row up.

* `TightOK q fs g m`: the arithmetic test of `no_tight` at order `m`, with `fs` the floors of
  every root and `g` the floors of roots that avoid `ShapeClimbAvoid.tightA (q+2)`, at the
  middle radii `i = q/2`, `j = q - q/2` and the radii `i + 2`, `j + 2`.
* `tight_bound`: if `TightOK q fs g m` and `m ≤ boundOf q (q+2) g`, every `q`-free digraph of
  minimum out-degree `q + 2` has more than `m` labels.

The floors are hypotheses here. Everything is generic in `q`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.TightBound
open Finset BRq2 BRq3 FifthStripAll RigidHost
open DotTwoPassShellTransport (layer)
open MixedRadiusCompletion (Floor)
open ShapeClimbAvoid (AvoidFloor tightA)

/-- The arithmetic test of the second collar at order `m`, at the middle radii. `fs` are the
floors of every root, `g` the floors of roots that are not tight. -/
def TightOK (q : ℕ) (fs g : List ℕ) (m : ℕ) : Prop :=
  let i := q / 2
  let j := q - q / 2
  let top := fs.getD (i+2) 0 + fs.getD (j+2) 0 + i + j
  let π := top - 2*(2*q+3) - (m+1)
  let δ := m + 1 - (fs.getD i 0 + fs.getD j 0)
  m + 1 ≤ g.getD i 0 + g.getD j 0 ∧ m + 1 + π + 2*(2*q+3) ≤ top ∧
    ∀ k ∈ range (δ + 2), k * (δ + 1) < k * k + (q+1) * π

instance {q fs g m} : Decidable (TightOK q fs g m) := by unfold TightOK; infer_instance

/-- **The tight bound.** -/
theorem tight_bound {q m : ℕ} {fs g : List ℕ} (hq : 3 ≤ q)
    (floors : ∀ i, Floor q (q+2) i (fs.getD i 0))
    (loose : ∀ i, AvoidFloor q (q+2) (tightA (q+2)) i (g.getD i 0))
    (ok : TightOK q fs g m) (le : m ≤ ShapeClimbMono.boundOf q (q+2) g)
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V q) (ne : V.Nonempty)
    (deg : ∀ v ∈ V, q + 2 ≤ (outN D V v).card) : m < V.card := by
  by_contra small
  obtain ⟨E, freeE, regE⟩ := CollarBound.exists_regular free deg
  have degE : ∀ v ∈ V, q + 2 ≤ (outN E V v).card := fun v hv => (regE v hv).ge
  obtain ⟨loosepay, heads, pay⟩ := ok
  have payAll : ∀ k, k * (m + 1 - (fs.getD (q/2) 0 + fs.getD (q - q/2) 0) + 1) <
      k * k + (q+1) * (fs.getD (q/2+2) 0 + fs.getD (q - q/2 + 2) 0 + q/2 + (q - q/2)
        - 2*(2*q+3) - (m+1)) := by
    intro k
    by_cases hk : k ∈ range (m + 1 - (fs.getD (q/2) 0 + fs.getD (q - q/2) 0) + 2)
    · exact pay k hk
    · have big : m + 1 - (fs.getD (q/2) 0 + fs.getD (q - q/2) 0) + 1 < k := by
        have := mem_range.not.mp hk
        omega
      have : k * (m + 1 - (fs.getD (q/2) 0 + fs.getD (q - q/2) 0) + 1) < k * k :=
        (Nat.mul_lt_mul_left (by omega : 0 < k)).mpr big
      omega
  have nt : ∀ v ∈ V, ¬ CollarTwo.Tight E V q v :=
    CollarTwo.no_tight (i := q/2) (j := q - q/2) freeE hq regE (by omega)
      (fun v hv _ => floors (q/2) E V freeE degE v hv)
      (fun v hv _ => floors (q - q/2) E V freeE degE v hv)
      (fun v hv _ => floors (q/2+2) E V freeE degE v hv)
      (fun v hv _ => floors (q - q/2 + 2) E V freeE degE v hv)
      (A := g.getD (q/2) 0) (B := g.getD (q - q/2) 0)
      (fun v hv hnt => Nat.add_le_add
        (ShapeClimbAvoid.ball_of_tight (loose (q/2)) freeE regE hv
          (fun h => hnt ⟨by omega, by omega⟩))
        (ShapeClimbAvoid.ball_of_tight (loose (q - q/2)) freeE regE hv
          (fun h => hnt ⟨by omega, by omega⟩)))
      (by omega) (by omega) (by omega) payAll
  have bound := CollarBound.boundOf_local (fs := g) (by omega) freeE ne degE
    (fun k v hv => ShapeClimbAvoid.ball_of_tight (loose k) freeE regE hv
      (fun h => nt v hv ⟨by omega, by omega⟩))
  omega

#print axioms tight_bound
end LeanCH.BR.TightBound
