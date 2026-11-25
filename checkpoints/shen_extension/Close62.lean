import checkpoints.shen_extension.Floors7Row
import checkpoints.shen_extension.EqualLayers
import checkpoints.shen_extension.Close54Final

/-!
# Order 62 at degree nine, cutoff seven

No `7`-free digraph with every out-degree at least `9` has `62` labels.

Score `S(x) = |B_3(x)| + |B_4(x)|` (radii `(3, 4)`), level `63`.

* S-1 `fat_bank` (`q = 7`, `r = 9`): at a root that is not thin with layers `(9, 8, 8)` the third
  layer `Z` is a bank (`BankPrice.Bank`) with exterior the fourth layer `W`: by the lower cutoff
  `6` (`r = 6 + 3`, `SupplierFat54.z_cover` with `AncestorRow.lemma5_six`) the rows of `Z` keep
  their heads in `Z ∪ W`; `|Z| = 8 = q + 1`, `|W| + 1 = 9`, so `TopRowFat.loop_complete` makes
  `Z` a single loop complete to `W`. Every bank row scores `≥ 65` (`BankPrice.a2_bank`).
* `fat_bank_law`: `TopRowFat.FatBank D V 9 3 4 5 (layer · 3)`. The fat savers (not thin,
  score `≤ 62`) have layers `(9, 8, 8)` (`Floors7Row.fat_saver_layers`); banks of two savers are
  equal or disjoint (`RowBanks.banks_meet`); two savers with the same third layer and equal
  two-balls (`|B_2| = 19`) are a gap at radii `(3, 4)` (`EqualLayers.equal_layer_gap`, `j = 3`).
* `no62_regular`: `TopRowFat.no62_of_bank` with `Floors7Row.floors7` and `fat_bank_law`.
* `no_62`, `excluded_62` as in `Close54Final`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.Close62
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar CHRuleCatalog
open DotTwoPassShellTransport (layer layer_subset)
open ThinSuppliers (Thin)

variable {D : CH.Digraph} {V : Finset ℕ}

/-- **S-1.** At a root that is not thin with layers `(9, 8, 8)` the third layer is a bank with
exterior the fourth layer. -/
theorem fat_bank (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) (hY : (layer D V 2 u).card = 9) (hZ : (layer D V 3 u).card = 8)
    (hW : (layer D V 4 u).card = 8) : BankPrice.Bank D V (layer D V 3 u) (layer D V 4 u) := by
  have free6 : QFree D V 6 := free.mono_bound (by norm_num)
  have ne := SupplierFat54.a_nonempty (AncestorRow.lemma5_six free6 reg hu hY)
  have keep : ∀ z ∈ layer D V 3 u, outN D V z ⊆ layer D V 3 u ∪ layer D V 4 u :=
    fun z hz => SupplierFat54.z_cover free6 hu le_rfl reg hY hZ ne hz
  have dj : Disjoint (layer D V 3 u) (layer D V 4 u) := FragmentBudget.layer_disj (by norm_num)
  have L := TopRowFat.loop_complete (r := 9) free (by norm_num) layer_subset (by rw [hZ]) dj
    (by rw [hW]) (fun z hz => reg z (layer_subset hz)) keep
  exact { KV := layer_subset, dis := dj, one := fun k hk => (L k hk).1, keep := keep,
          full := fun k hk => (L k hk).2.1 }

/-- **S-1, the price.** Every row of such a bank scores at least `65`. -/
theorem bank_score (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) (hY : (layer D V 2 u).card = 9) (hZ : (layer D V 3 u).card = 8)
    (hW : (layer D V 4 u).card = 8) {x : ℕ} (hx : x ∈ layer D V 3 u) :
    65 ≤ (ball D V x 3).card + (ball D V x 4).card :=
  BankPrice.a2_bank free reg (fat_bank free reg hu hY hZ hW) hW hx

/-- **The fat-bank law at order `62`.** -/
theorem fat_bank_law (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 62) : TopRowFat.FatBank D V 9 3 4 5 (fun u => layer D V 3 u) where
  sub := fun u hu nt low => by
    obtain ⟨hY, hZ, hW⟩ := Floors7Row.fat_saver_layers free reg hu nt (by omega)
    refine ⟨layer_subset, show 5 ≤ (layer D V 3 u).card by omega, fun x hx => ?_⟩
    have := bank_score free reg hu hY hZ hW hx
    omega
  sep := fun u hu u' hu' nt nt' low low' => by
    obtain ⟨hY, hZ, hW⟩ := Floors7Row.fat_saver_layers free reg hu nt (by omega)
    obtain ⟨hY', hZ', hW'⟩ := Floors7Row.fat_saver_layers free reg hu' nt' (by omega)
    have B := fat_bank free reg hu hY hZ hW
    have B' := fat_bank free reg hu' hY' hZ' hW'
    by_cases d : Disjoint (layer D V 3 u) (layer D V 3 u')
    · exact Or.inr d
    · obtain ⟨s, hs, hs'⟩ := not_disjoint_iff.mp d
      exact Or.inl (RowBanks.banks_meet free (by norm_num) B.KV B'.KV (by rw [hZ]) (by rw [hZ'])
        B.one B'.one B.keep B'.keep B.full B'.full hs hs')
  gap := fun u hu u' hu' nt nt' low low' same ne => by
    obtain ⟨hY, -, -⟩ := Floors7Row.fat_saver_layers free reg hu nt (by omega)
    obtain ⟨hY', -, -⟩ := Floors7Row.fat_saver_layers free reg hu' nt' (by omega)
    have b2 := (Floors7Row.balls9 free reg hu).2.1
    have b2' := (Floors7Row.balls9 free reg hu').2.1
    exact EqualLayers.equal_layer_gap free hu hu' ne (j := 3) (by norm_num) (by norm_num) same
      (show (ball D V u 2).card = (ball D V u' 2).card by omega) (by norm_num) (by norm_num)

/-- **Order 62, out-regular.** -/
theorem no62_regular (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 62) : False :=
  TopRowFat.no62_of_bank free reg n (Floors7Row.floors7 free reg) (fat_bank_law free reg n)

/-- **Order 62.** No `7`-free digraph of minimum out-degree `9` has `62` labels. -/
theorem no_62 (free : QFree D V 7) (deg : ∀ v ∈ V, 9 ≤ (outN D V v).card) (n : V.card = 62) :
    False := by
  obtain ⟨E, freeE, regE⟩ := CollarBound.exists_regular free deg
  exact no62_regular freeE regE n

/-- No counterexample at degree `9`, cutoff `7` has `62` labels. -/
theorem excluded_62 {p : Input} (bad : Bad p) (hs : p.s = 9) (hc : cutoff p = 7) :
    p.n ≠ 62 := by
  intro hn
  have free : QFree p.D (range p.n) (cutoff p) := qfree_of_noShort bad.loopless bad.missing
  rw [hc] at free
  have deg : ∀ v ∈ range p.n, 9 ≤ (outN p.D (range p.n) v).card := fun v hv => by
    rw [← hs]
    exact Compose.FloorSix.out_card bad.degree (mem_range.mp hv)
  exact no_62 free deg (by rw [card_range, hn])

#print axioms fat_bank
#print axioms bank_score
#print axioms fat_bank_law
#print axioms no62_regular
#print axioms no_62
#print axioms excluded_62
end LeanCH.BR.Close62
