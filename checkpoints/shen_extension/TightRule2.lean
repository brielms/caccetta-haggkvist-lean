import checkpoints.shen_extension.TightRule
import checkpoints.shen_extension.TightFloors

/-!
# The tight rule with the tight floors: an order bound on the row `r = q + 2`

`TightRule.tightBound` with the patterns of `TightFloors` added.

* Tight rows (`CollarTwo.Tight`) get their own floors `tightT2 q`, the climb of
  `ShapeClimbAvoid.layersA` for roots avoiding `notTightA (q+2)` and Q
  (`TightFloors.tight_avoids`): a tight root has second and third layers of exactly `q + 1`, and
  a fourth layer of `q + 1` forces a fifth of at least `q + 1` (`TightFloors.q_fifth`, `5 ≤ q`).
* Rows that are not tight get the floors `looseT2 q`, the climb for roots avoiding
  `tightA (q+2)`, P7a over the floors `floorsT q` (`TightFloors.p7a_fourth`, `6 ≤ q`, fires only
  when `TightFloors.P7aOK` holds for those floors) and P7b (`TightFloors.p7b_fourth`, `4 ≤ q`)
  (`loose_avoids`).
* `TightOK2 q t g m`: the arithmetic test of `CollarTwo.no_tight` at order `m` with tight-row
  floors `t` and loose floors `g` (`TightBound.TightOK` with `t` for the floors of every root).
* `tight_bound2`: if `TightOK2 q t g m` and `m ≤ boundOf q (q+2) g`, every `q`-free digraph of
  minimum out-degree `q + 2` has more than `m` labels. Generic in the two patterns.
* `tightBound2`, `tightBound2_sound`, `tight2_excluded`, and the pruned twin `tightBound2F`.

Generic in `q`; the rule applies from `q = 5` on.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.TightRule2
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion CHRuleCatalog ProjectedQuotaTransfer
open RecursivePrefixBudget FifthStripAll RigidHost
open ShapeClimbAt (library_bankAt)
open ShapeClimbAvoid (Avoids AvoidFloor tightA notTightA noX)
open TightRule (bankDegree floorsT floorsTF floorsTF_eq)
open TightFloors (orA)

/-- The arithmetic test of the second collar at order `m`, with floors `t` of tight rows and
floors `g` of the other rows, at the middle radii. -/
def TightOK2 (q : ℕ) (t g : List ℕ) (m : ℕ) : Prop :=
  let i := q / 2
  let j := q - q / 2
  let top := t.getD (i+2) 0 + t.getD (j+2) 0 + i + j
  let π := top - 2*(2*q+3) - (m+1)
  let δ := m + 1 - (t.getD i 0 + t.getD j 0)
  m + 1 ≤ g.getD i 0 + g.getD j 0 ∧ m + 1 + π + 2*(2*q+3) ≤ top ∧
    ∀ k ∈ range (δ + 2), k * (δ + 1) < k * k + (q+1) * π

instance {q t g m} : Decidable (TightOK2 q t g m) := by unfold TightOK2; infer_instance

/-- **The tight bound with tight-row floors.** `Pt` is avoided by every tight root, `Pl` by
every root that is not tight. -/
theorem tight_bound2 {q m : ℕ} {t g : List ℕ} {Pt Pl : List ℕ → ℕ → Bool} (hq : 3 ≤ q)
    (tightAv : ∀ (D : CH.Digraph) (V : Finset ℕ), QFree D V q →
      (∀ v ∈ V, (outN D V v).card = q + 2) → ∀ u ∈ V, CollarTwo.Tight D V q u → Avoids D V u Pt)
    (looseAv : ∀ (D : CH.Digraph) (V : Finset ℕ), QFree D V q →
      (∀ v ∈ V, (outN D V v).card = q + 2) → ∀ u ∈ V, ¬ CollarTwo.Tight D V q u →
        Avoids D V u Pl)
    (tf : ∀ i, AvoidFloor q (q+2) Pt i (t.getD i 0))
    (loose : ∀ i, AvoidFloor q (q+2) Pl i (g.getD i 0))
    (ok : TightOK2 q t g m) (le : m ≤ ShapeClimbMono.boundOf q (q+2) g)
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V q) (ne : V.Nonempty)
    (deg : ∀ v ∈ V, q + 2 ≤ (outN D V v).card) : m < V.card := by
  by_contra small
  obtain ⟨E, freeE, regE⟩ := CollarBound.exists_regular free deg
  have degE : ∀ v ∈ V, q + 2 ≤ (outN E V v).card := fun v hv => (regE v hv).ge
  obtain ⟨loosepay, heads, pay⟩ := ok
  have payAll : ∀ k, k * (m + 1 - (t.getD (q/2) 0 + t.getD (q - q/2) 0) + 1) <
      k * k + (q+1) * (t.getD (q/2+2) 0 + t.getD (q - q/2 + 2) 0 + q/2 + (q - q/2)
        - 2*(2*q+3) - (m+1)) := by
    intro k
    by_cases hk : k ∈ range (m + 1 - (t.getD (q/2) 0 + t.getD (q - q/2) 0) + 2)
    · exact pay k hk
    · have big : m + 1 - (t.getD (q/2) 0 + t.getD (q - q/2) 0) + 1 < k := by
        have := mem_range.not.mp hk
        omega
      have : k * (m + 1 - (t.getD (q/2) 0 + t.getD (q - q/2) 0) + 1) < k * k :=
        (Nat.mul_lt_mul_left (by omega : 0 < k)).mpr big
      omega
  have tb : ∀ i, ∀ v ∈ V, CollarTwo.Tight E V q v → t.getD i 0 ≤ (ball E V v i).card :=
    fun i v hv tv => tf i E V freeE regE v hv (tightAv E V freeE regE v hv tv)
  have lb : ∀ i, ∀ v ∈ V, ¬ CollarTwo.Tight E V q v → g.getD i 0 ≤ (ball E V v i).card :=
    fun i v hv nt => loose i E V freeE regE v hv (looseAv E V freeE regE v hv nt)
  have nt : ∀ v ∈ V, ¬ CollarTwo.Tight E V q v :=
    CollarTwo.no_tight (i := q/2) (j := q - q/2) freeE hq regE (by omega)
      (tb (q/2)) (tb (q - q/2)) (tb (q/2+2)) (tb (q - q/2 + 2))
      (A := g.getD (q/2) 0) (B := g.getD (q - q/2) 0)
      (fun v hv hnt => Nat.add_le_add (lb (q/2) v hv hnt) (lb (q - q/2) v hv hnt))
      (by omega) (by omega) (by omega) payAll
  have bound := CollarBound.boundOf_local (fs := g) (by omega) freeE ne degE
    (fun k v hv => lb k v hv (nt v hv))
  omega

/-! ### The patterns and the floors -/

/-- Avoided by every tight root (`5 ≤ q`). -/
def tightP (q : ℕ) : List ℕ → ℕ → Bool := orA (notTightA (q+2)) (TightFloors.qA (q+2))

/-- Avoided by every root that is not tight (`4 ≤ q`), over floors `fs` of every root. -/
def looseP (q : ℕ) (fs : List ℕ) : List ℕ → ℕ → Bool :=
  orA (tightA (q+2)) (orA (TightFloors.p7aA q fs) (TightFloors.p7bA (q+2)))

theorem loose_avoids {q : ℕ} (hq : 4 ≤ q) {fs : List ℕ} (floors : ∀ i, Floor q (q+2) i (fs.getD i 0))
    (D : CH.Digraph) (V : Finset ℕ) (free : QFree D V q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 2) (u : ℕ) (hu : u ∈ V)
    (nt : ¬ CollarTwo.Tight D V q u) : Avoids D V u (looseP q fs) :=
  TightFloors.avoids_or (ShapeClimbAvoid.avoids_tight (fun h => nt ⟨by omega, by omega⟩))
    (TightFloors.avoids_or (TightFloors.avoids_p7a free reg hu floors)
      (TightFloors.avoids_p7b free hq reg hu))

/-- Floors of tight rows at degree `q + 2`, radii `0 … q/2 + 3`. -/
def tightT2 (q : ℕ) : List ℕ :=
  ShapeClimbAvoid.layersA (tightP q) noX q (q+2) (library q (bankDegree q)) (floorsT q) (q/2+2)

/-- Floors of rows that are not tight at degree `q + 2`, radii `0 … q/2 + 3`. -/
def looseT2 (q : ℕ) : List ℕ :=
  ShapeClimbAvoid.layersA (looseP q (floorsT q)) noX q (q+2) (library q (bankDegree q)) (floorsT q) (q/2+2)

/-- The order bound of the tight rule with the tight floors, at cutoff `q`, degree `q + 2`. -/
def tightBound2 (q : ℕ) : ℕ :=
  if 5 ≤ q then
    max (ShapeClimbMono.boundOf q (q+2) (floorsT q))
      (Nat.findGreatest (fun m => TightOK2 q (tightT2 q) (looseT2 q) m)
        (ShapeClimbMono.boundOf q (q+2) (looseT2 q)))
  else 0

theorem tightBound2_sound {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V q)
    (ne : V.Nonempty) (deg : ∀ v ∈ V, q + 2 ≤ (outN D V v).card) : tightBound2 q < V.card := by
  unfold tightBound2
  split
  next hq =>
    have pf : 0 < projectionFloor := Nat.succ_pos _
    have known : ∀ q' t, t ≤ bankDegree q → NoHost q' t := fun q' t ht =>
      ShapeClimbMono.lower_hosts_every q' t (by
        have := ht.trans (min_le_right (q + 1) (projectionFloor - 1))
        omega)
    have cr : bankDegree q < q + 2 := lt_of_le_of_lt (min_le_left ..) (by omega)
    have bank := library_bankAt (r := q+2) (by omega : 2 ≤ q) cr (known q)
    have seeds := ShapeClimbMono.seedAt_sound (q := q) (K := q/2+2) cr known
    have floors : ∀ i, Floor q (q+2) i ((floorsT q).getD i 0) :=
      (ShapeClimbMono.layersS_sound (by omega) bank seeds (q/2+2) (by omega)).2
    have tf : ∀ i, AvoidFloor q (q+2) (tightP q) i ((tightT2 q).getD i 0) :=
      (ShapeClimbAvoid.layersA_sound (ShapeClimbAvoid.noX_sound q (q+2)) (by omega) bank floors
        (q/2+2) (by omega)).2
    have lf : ∀ i, AvoidFloor q (q+2) (looseP q (floorsT q)) i ((looseT2 q).getD i 0) :=
      (ShapeClimbAvoid.layersA_sound (ShapeClimbAvoid.noX_sound q (q+2)) (by omega) bank floors
        (q/2+2) (by omega)).2
    refine max_lt (ShapeClimbMono.boundOf_sound (by omega) floors free ne deg) ?_
    by_cases zero : Nat.findGreatest (fun m => TightOK2 q (tightT2 q) (looseT2 q) m)
        (ShapeClimbMono.boundOf q (q+2) (looseT2 q)) = 0
    · rw [zero]
      exact card_pos.mpr ne
    · exact tight_bound2 (by omega)
        (fun D V free reg u hu tight => TightFloors.tight_avoids free hq reg hu tight)
        (loose_avoids (by omega) floors) tf lf
        (Nat.findGreatest_of_ne_zero rfl zero) (Nat.findGreatest_le _) free ne deg
  next => exact card_pos.mpr ne

/-- No counterexample at degree `cutoff + 2` has order at most `tightBound2`. -/
theorem tight2_excluded {p : Input} (bad : Bad p) (row : p.s = cutoff p + 2) :
    ¬(0 < p.n ∧ p.n ≤ tightBound2 (cutoff p)) := by
  rintro ⟨pos, small⟩
  have free : QFree p.D (range p.n) (cutoff p) := qfree_of_noShort bad.loopless bad.missing
  have deg : ∀ v ∈ range p.n, cutoff p + 2 ≤ (outN p.D (range p.n) v).card := by
    intro v hv
    rw [← row]
    exact Compose.FloorSix.out_card bad.degree (mem_range.mp hv)
  have := tightBound2_sound free ⟨0, mem_range.mpr pos⟩ deg
  rw [card_range] at this
  omega

/-! ### The same number over the pruned evaluations -/

def tightT2F (q : ℕ) : List ℕ :=
  let fs := floorsTF q
  ShapeClimbAvoid.layersAF (tightP q) noX q (q+2) (library q (bankDegree q)) fs (q/2+2)

def looseT2F (q : ℕ) : List ℕ :=
  let fs := floorsTF q
  ShapeClimbAvoid.layersAF (looseP q fs) noX q (q+2) (library q (bankDegree q)) fs (q/2+2)

def tightBound2F (q : ℕ) : ℕ :=
  if 5 ≤ q then
    let fs := floorsTF q
    let t := tightT2F q
    let g := looseT2F q
    max (ShapeClimbMono.boundOf q (q+2) fs)
      (Nat.findGreatest (fun m => TightOK2 q t g m) (ShapeClimbMono.boundOf q (q+2) g))
  else 0

theorem tightT2F_eq (q : ℕ) : tightT2F q = tightT2 q := by
  simp only [tightT2F, tightT2, ShapeClimbAvoid.layersAF_eq, floorsTF_eq]

theorem looseT2F_eq (q : ℕ) : looseT2F q = looseT2 q := by
  simp only [looseT2F, looseT2, ShapeClimbAvoid.layersAF_eq, floorsTF_eq]

theorem tightBound2F_eq (q : ℕ) : tightBound2F q = tightBound2 q := by
  simp only [tightBound2F, tightBound2, floorsTF_eq, tightT2F_eq, looseT2F_eq]

#print axioms tight_bound2
#print axioms loose_avoids
#print axioms tightBound2_sound
#print axioms tight2_excluded
#print axioms tightBound2F_eq
end LeanCH.BR.TightRule2
