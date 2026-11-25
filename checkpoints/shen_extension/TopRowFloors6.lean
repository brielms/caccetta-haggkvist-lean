import checkpoints.shen_extension.TopRow
import checkpoints.shen_extension.ThinRule

/-!
# The floors used by `TopRow` at `q = 6`, kernel-checked

* `thinZA`: second layer `8`, third layer `9`. A thin root with a third layer of nine avoids it
  (`avoids_thinZ`); its climb at `q = 6` gives `|B 4| ≥ 34` (`thinZ6_val`).
* `floors6`: `|B 3| ≥ 26` everywhere, `|B 4| ≥ 34` at thin rows with `|B 3| ≤ 27`
  (`ThinSuppliers.tight_ball_four` for third layer `8`, the climb for third layer `9`).
* `no54_fat`: order `54` reduces to the fat savers, with no floor hypothesis.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.TopRowFloors6
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion CHRuleCatalog ProjectedQuotaTransfer
open RecursivePrefixBudget FifthStripAll RigidHost
open ShapeClimbAt (library_bankAt)
open ShapeClimbAvoid (Avoids AvoidFloor)
open DotTwoPassShellTransport (layer)
open ThinSuppliers (Thin TightR)

/-! ### `q = 6` -/

/-- Second layer `8` and third layer `9` (`r = 9`). -/
def thinZA (ws : List ℕ) (last : ℕ) : Bool :=
  decide ((2 ≤ ws.length ∧ ws.getD 1 0 ≠ 8) ∨ (3 ≤ ws.length ∧ ws.getD 2 0 ≠ 9) ∨
    (ws.length = 1 ∧ last < 8) ∨ (ws.length = 2 ∧ last < 9))

theorem avoids_thinZ {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (h2 : (layer D V 2 u).card = 8) (h3 : (layer D V 3 u).card = 9) :
    Avoids D V u thinZA := by
  intro ws last exact bound
  simp only [thinZA, decide_eq_false_iff_not]
  rintro (⟨len, w2⟩ | ⟨len, w3⟩ | ⟨len, w⟩ | ⟨len, w⟩)
  · have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
    omega
  · have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
    omega
  · rw [show ws.length + 1 = 2 by omega] at bound
    omega
  · rw [show ws.length + 1 = 3 by omega] at bound
    omega

def thinZ6 : List ℕ :=
  ShapeClimbAvoid.layersA thinZA (FatShort.fatShortGX 6 9) 6 9
    (library 6 (ThinRule.bankDegree 9)) (ThinRule.floorsH 6 9) 3

def thinZ6F : List ℕ :=
  ShapeClimbAvoid.layersAF thinZA (FatShort.fatShortGX 6 9) 6 9
    (library 6 (ThinRule.bankDegree 9)) (ThinRule.floorsHF 6 9) 3

theorem thinZ6F_eq : thinZ6F = thinZ6 := by
  simp only [thinZ6F, thinZ6, ShapeClimbAvoid.layersAF_eq, ThinRule.floorsHF_eq]

theorem sound6 :
    (∀ i, Floor 6 9 i ((ThinRule.floorsH 6 9).getD i 0)) ∧
    (∀ i, AvoidFloor 6 9 thinZA i (thinZ6.getD i 0)) := by
  have pf : 0 < projectionFloor := Nat.succ_pos _
  have known : ∀ q' t, t ≤ ThinRule.bankDegree 9 → NoHost q' t := fun q' t ht =>
    ShapeClimbMono.lower_hosts_every q' t (by
      have := ht.trans (min_le_right (9 - 1) (projectionFloor - 1))
      omega)
  have cr : ThinRule.bankDegree 9 < 9 := lt_of_le_of_lt (min_le_left ..) (by omega)
  have bank := library_bankAt (r := 9) (by omega : 2 ≤ 6) cr (known 6)
  have seeds := ShapeClimbMono.seedAt_sound (q := 6) (K := 6 - 6/2) cr known
  have floors : ∀ i, Floor 6 9 i ((ThinRule.floorsH 6 9).getD i 0) :=
    (ShapeClimbX.layersX_sound (FatShort.fatShortGX_sound 6 9) (by omega) bank seeds
      (6 - 6/2) (by omega)).2
  exact ⟨floors, (ShapeClimbAvoid.layersA_sound (FatShort.fatShortGX_sound 6 9) (by omega) bank
    floors 3 (by omega)).2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all6 : ThinRule.floorsHF 6 9 = [1, 10, 18, 26, 33] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thinZ6_val : 34 ≤ thinZ6F.getD 4 0 := by decide +kernel

theorem floors6 {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V 6)
    (reg : ∀ v ∈ V, (outN D V v).card = 9) :
    (∀ v ∈ V, 26 ≤ (ball D V v 3).card) ∧
    (∀ v ∈ V, Thin D V 9 v → (ball D V v 3).card ≤ 27 → 34 ≤ (ball D V v 4).card) := by
  obtain ⟨fa, fz⟩ := sound6
  have e : ThinRule.floorsH 6 9 = [1, 10, 18, 26, 33] := by
    rw [← ThinRule.floorsHF_eq]; exact all6
  have deg : ∀ v ∈ V, 9 ≤ (outN D V v).card := fun v hv => (reg v hv).ge
  refine ⟨fun v hv => by have := fa 3 D V free deg v hv; rwa [e] at this, fun v hv thin b3 => ?_⟩
  have L := ThinSuppliers.balls_by_layers free (by norm_num) reg hv
  have w3 := ThinSuppliers.third_wide free (by norm_num) reg hv thin (by norm_num)
  unfold Thin at thin
  by_cases t : (layer D V 3 v).card + 1 ≤ 9
  · have := (ThinSuppliers.tight_ball_four free (by norm_num) reg hv ⟨thin, t⟩ (by norm_num)
      (by norm_num)).2
    omega
  · have := fz 4 D V free reg v hv (avoids_thinZ (by omega) (by omega))
    have v4 := thinZ6_val
    rw [thinZ6F_eq] at v4
    omega

section nine
variable {D : CH.Digraph} {V : Finset ℕ}

/-- **54 ⟸ no fat saver**, floors discharged. -/
theorem no54_fat (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) (n : V.card = 54)
    (fat : ∀ v ∈ V, ¬ Thin D V 9 v → 28 ≤ (ball D V v 3).card) : False :=
  TopRow.no54_of_fat free reg n (floors6 free reg).1 (floors6 free reg).2 fat

end nine

#print axioms floors6
#print axioms no54_fat
end LeanCH.BR.TopRowFloors6
