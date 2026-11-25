import checkpoints.shen_extension.Close72
import checkpoints.shen_extension.Profiles72II

/-!
# Order 72 at degree nine, cutoff eight

No `8`-free digraph with every out-degree at least `9` has `72` labels.

`Close72.no72_of_profiles` (the closing count) with its three fields from
`Profiles72.profile0_72` (P0), `Profiles72.profileI_72` (PI) and `Profiles72.profileII_72` (PII).
-/

set_option linter.style.longLine false
namespace LeanCH.BR.Close72Final
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar CHRuleCatalog
open DotTwoPassShellTransport (layer layer_subset)

variable {D : CH.Digraph} {V : Finset ℕ}

/-- The three profiles at `q = 8`, `r = 9`. -/
theorem profiles (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9) :
    Close72.Profiles72 D V where
  p0 := fun u hu hY hZ => by
    obtain ⟨one, keep, full, -, -⟩ := Profiles72.profile0_72 free reg hu hY hZ
    exact { KV := layer_subset, dis := FragmentBudget.layer_disj (by norm_num), one := one,
            keep := keep, full := full }
  p1 := fun u hu hY hZ hW => by
    obtain ⟨-, one, keep, full⟩ := Profiles72.profileI_72 free reg hu hY hZ hW
    exact { KV := layer_subset, dis := FragmentBudget.layer_disj (by norm_num), one := one,
            keep := keep, full := full }
  p2 := fun u hu hY hZ hW => Profiles72.profileII_72 free reg hu hY hZ hW

/-- **Order 72, out-regular.** -/
theorem no72_regular (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 72) : False :=
  Close72.no72_of_profiles free reg n (profiles free reg)

/-- **Order 72.** No `8`-free digraph of minimum out-degree `9` has `72` labels. -/
theorem no_72 (free : QFree D V 8) (deg : ∀ v ∈ V, 9 ≤ (outN D V v).card) (n : V.card = 72) :
    False := by
  obtain ⟨E, freeE, regE⟩ := CollarBound.exists_regular free deg
  exact no72_regular freeE regE n

/-- No counterexample at degree `9`, cutoff `8` has `72` labels. -/
theorem excluded_72 {p : Input} (bad : Bad p) (hs : p.s = 9) (hc : cutoff p = 8) :
    p.n ≠ 72 := by
  intro hn
  have free : QFree p.D (range p.n) (cutoff p) := qfree_of_noShort bad.loopless bad.missing
  rw [hc] at free
  have deg : ∀ v ∈ range p.n, 9 ≤ (outN p.D (range p.n) v).card := fun v hv => by
    rw [← hs]
    exact Compose.FloorSix.out_card bad.degree (mem_range.mp hv)
  exact no_72 free deg (by rw [card_range, hn])

#print axioms profiles
#print axioms no72_regular
#print axioms no_72
#print axioms excluded_72
end LeanCH.BR.Close72Final
