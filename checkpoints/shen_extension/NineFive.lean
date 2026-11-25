import checkpoints.shen_extension.ThinRule
import checkpoints.shen_extension.TightPair

/-!
# Orders 44 and 45 at degree nine, cutoff five, for every digraph

* `no_44'`: no `5`-free digraph of minimum out-degree `9` on `44` labels (`FatShort.no_44` after
  thinning to out-degree exactly `9`, `CollarBound.exists_regular`).
* `loose4`: the climb of the roots that avoid `ShapeClimbAvoid.tightA 9`, with the fat-short
  pattern, radii `0 … 4`, over the floors `ThinRule.floorsH 5 9`; `floor_33`: its value at
  radius four is at least `33` (kernel-checked on the pruned twin `loose4F`).
* `no_45`: no `5`-free digraph of minimum out-degree `9` on `45` labels. Thin to out-degree `9`;
  thin roots that are not tight have four-ball at least `33` (`floor_33`), so
  `FatShort.profile_45` gives every root widths `(9, 9, 8)`, balls `10, 19, 27`; then
  `TightPair.tight_pair_false` at `k = 2` (`46 ≤ 19 + 27`, `48 ≤ 2·19 + 10`).
* `excluded_44`, `excluded_45`: the same in the form of a coverage rule on `Bad p`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.NineFive
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion CHRuleCatalog ProjectedQuotaTransfer
open RecursivePrefixBudget
open ShapeClimbAt (library_bankAt)
open DotTwoPassShellTransport (layer)

/-- **No `5`-free digraph of minimum out-degree `9` on `44` labels.** -/
theorem no_44' {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V 5)
    (deg : ∀ v ∈ V, 9 ≤ (outN D V v).card) (n : V.card = 44) : False := by
  obtain ⟨E, freeE, regE⟩ := CollarBound.exists_regular free deg
  exact FatShort.no_44 freeE regE n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thin_44F : 44 ≤ ThinRule.thinBoundF 5 9 := by decide +kernel

/-- **At most `44` labels.** Every nonempty `5`-free digraph of minimum out-degree `9` has more
than `44` labels (`ThinRule.thinBound 5 9 = 44`, kernel-checked as `thin_44F`). -/
theorem order_gt_44 {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V 5) (ne : V.Nonempty)
    (deg : ∀ v ∈ V, 9 ≤ (outN D V v).card) : 44 < V.card := by
  have h := thin_44F
  rw [ThinRule.thinBoundF_eq] at h
  exact lt_of_le_of_lt h (ThinRule.thinBound_sound free ne deg)

/-- Floors of roots that avoid `tightA 9` at cutoff five, radii `0 … 4`. -/
def loose4 : List ℕ :=
  ShapeClimbAvoid.layersA (ShapeClimbAvoid.tightA 9) (FatShort.fatShortGX 5 9) 5 9
    (library 5 (ThinRule.bankDegree 9)) (ThinRule.floorsH 5 9) 3

def loose4F : List ℕ :=
  ShapeClimbAvoid.layersAF (ShapeClimbAvoid.tightA 9) (FatShort.fatShortGX 5 9) 5 9
    (library 5 (ThinRule.bankDegree 9)) (ThinRule.floorsHF 5 9) 3

theorem loose4F_eq : loose4F = loose4 := by
  simp only [loose4F, loose4, ShapeClimbAvoid.layersAF_eq, ThinRule.floorsHF_eq]

theorem loose4_sound (i : ℕ) :
    ShapeClimbAvoid.AvoidFloor 5 9 (ShapeClimbAvoid.tightA 9) i (loose4.getD i 0) := by
  have pf : 0 < projectionFloor := Nat.succ_pos _
  have known : ∀ q' t, t ≤ ThinRule.bankDegree 9 → NoHost q' t := fun q' t ht =>
    ShapeClimbMono.lower_hosts_every q' t (by
      have := ht.trans (min_le_right (9 - 1) (projectionFloor - 1))
      omega)
  have cr : ThinRule.bankDegree 9 < 9 := lt_of_le_of_lt (min_le_left ..) (by omega)
  have bank := library_bankAt (r := 9) (by omega : 2 ≤ 5) cr (known 5)
  have seeds := ShapeClimbMono.seedAt_sound (q := 5) (K := 5 - 5/2) cr known
  have floors : ∀ i, Floor 5 9 i ((ThinRule.floorsH 5 9).getD i 0) :=
    (ShapeClimbX.layersX_sound (FatShort.fatShortGX_sound 5 9) (by omega) bank seeds
      (5 - 5/2) (by omega)).2
  exact (ShapeClimbAvoid.layersA_sound (FatShort.fatShortGX_sound 5 9) (by omega) bank floors
    3 (by omega)).2 i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floor_33F : 33 ≤ loose4F.getD 4 0 := by decide +kernel

theorem floor_33 : ShapeClimbAvoid.AvoidFloor 5 9 (ShapeClimbAvoid.tightA 9) 4 33 := by
  have h := floor_33F
  rw [loose4F_eq] at h
  exact fun D V free reg u hu av => h.trans (loose4_sound 4 D V free reg u hu av)

/-- **No `5`-free digraph of minimum out-degree `9` on `45` labels.** -/
theorem no_45 {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V 5)
    (deg : ∀ v ∈ V, 9 ≤ (outN D V v).card) (n : V.card = 45) : False := by
  obtain ⟨E, freeE, regE⟩ := CollarBound.exists_regular free deg
  have f4 : ∀ v ∈ V, ThinSuppliers.Thin E V 9 v → ¬ ThinSuppliers.TightR E V 9 v →
      33 ≤ (ball E V v 4).card := fun v hv _ nt =>
    ShapeClimbAvoid.ball_of_tight floor_33 freeE regE hv nt
  have prof := FatShort.profile_45 freeE regE n f4
  have ne : V.Nonempty := card_pos.mp (by omega)
  refine TightPair.tight_pair_false (q := 5) (k := 2) (a := 19) (b := 27) (c := 10) freeE
    (by norm_num) ne (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_) (by omega) (by omega)
  all_goals
    have L := ThinSuppliers.balls_by_layers freeE (by norm_num) regE hv
    have := prof v hv
    norm_num
    omega

/-- No counterexample at degree `9`, cutoff `5` has `44` labels. -/
theorem excluded_44 {p : Input} (bad : Bad p) (hs : p.s = 9) (hc : cutoff p = 5) :
    p.n ≠ 44 := by
  intro hn
  have free : QFree p.D (range p.n) (cutoff p) := qfree_of_noShort bad.loopless bad.missing
  rw [hc] at free
  have deg : ∀ v ∈ range p.n, 9 ≤ (outN p.D (range p.n) v).card := fun v hv => by
    rw [← hs]
    exact Compose.FloorSix.out_card bad.degree (mem_range.mp hv)
  exact no_44' free deg (by rw [card_range, hn])

/-- No counterexample at degree `9`, cutoff `5` has `45` labels. -/
theorem excluded_45 {p : Input} (bad : Bad p) (hs : p.s = 9) (hc : cutoff p = 5) :
    p.n ≠ 45 := by
  intro hn
  have free : QFree p.D (range p.n) (cutoff p) := qfree_of_noShort bad.loopless bad.missing
  rw [hc] at free
  have deg : ∀ v ∈ range p.n, 9 ≤ (outN p.D (range p.n) v).card := fun v hv => by
    rw [← hs]
    exact Compose.FloorSix.out_card bad.degree (mem_range.mp hv)
  exact no_45 free deg (by rw [card_range, hn])

/-- No counterexample at degree `9`, cutoff `5` has at most `44` labels. -/
theorem excluded_le_44 {p : Input} (bad : Bad p) (hs : p.s = 9) (hc : cutoff p = 5) :
    ¬(0 < p.n ∧ p.n ≤ 44) := by
  have := ThinRule.thin_excluded bad
  rw [hs, hc, ← ThinRule.thinBoundF_eq] at this
  rintro ⟨pos, le⟩
  exact this ⟨pos, le.trans thin_44F⟩

#print axioms no_44'
#print axioms order_gt_44
#print axioms excluded_le_44
#print axioms floor_33
#print axioms no_45
#print axioms excluded_44
#print axioms excluded_45
end LeanCH.BR.NineFive
