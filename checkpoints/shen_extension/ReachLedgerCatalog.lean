import checkpoints.shen_extension.ReachLedger
import checkpoints.shen_extension.LoneRowCatalog

/-!
# Catalog entry for the reach ledger

Four packets and one exit, all generic in the graph, the cutoff, the radii, the floors, the degree
and the lower quota.

* `Ledger D V q` (from `QFree D V q`): row and total ledgers, parent caps, supplier caps and the
  tight supply law, at every admissible pair of radii.
* `Budget D V i j a b` (from floors `a`, `b` at radii `i + j ≤ q`): the exact spend, the order
  bound, and the level counts to any depth.
* `Shells D V q` (from `QFree D V q` and `2 ≤ q`): head balls, row escape, complete rows, full by
  count, closed chains, tied chains, shell classes, class counts.
* `Growth D V q t` (from `NoHost q t` and `QFree D V q`): fragment rows, escapes and ball growth.
* `fragment_exit`: a fragment within range that keeps the quota closes the context.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.ReachLedgerCatalog
open Finset BRq2 BRq3 BR45 BypassRepair ReachLedger

variable {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}

/-- Everything the cutoff alone says about reach, at every admissible pair of radii. -/
structure Ledger (D : CH.Digraph) (V : Finset ℕ) (q : ℕ) : Prop where
  row : ∀ i j v, i + j ≤ q → v ∈ V →
    (ball D V v i).card + (reverseBall D V v j).card + (gap D V i j v).card = V.card + 1
  total : ∀ i j, i + j ≤ q →
    ∑ v ∈ V, (ball D V v i).card + ∑ v ∈ V, (ball D V v j).card
      + ∑ v ∈ V, (gap D V i j v).card = V.card * (V.card + 1)
  parents : ∀ i v, i + 1 ≤ q → v ∈ V → (inN D V v).card + (ball D V v i).card ≤ V.card
  suppliers : ∀ i (S T : Finset ℕ), i + 1 ≤ q → S ⊆ V → T ⊆ V →
    T.card + ∑ s ∈ S, (ball D V s i).card ≤
      (T.filter (fun v => outN D S v = ∅)).card + S.card * V.card
  supply : ∀ i j a, i + i ≤ q → j + 1 ≤ q → (∀ v ∈ V, a ≤ (ball D V v i).card) →
    2 * (V.card + (V.filter (fun v => a + 1 < (ball D V v i).card)).card
        + ∑ v ∈ V, ((ball D V v i).card - (a + 2)))
      + ∑ v ∈ V, (gap D V i i v).card
      + 2 * ∑ s ∈ V.filter (fun v => a + 1 < (ball D V v i).card), (ball D V s j).card
      + V.card * (a + a)
    ≤ V.card * (V.card + 1)
      + 2 * ((V.filter (fun v => (ball D V v i).card = a)).filter
          (fun v => outN D (V.filter (fun v => a + 1 < (ball D V v i).card)) v = ∅)).card
      + 2 * ((V.filter (fun v => a + 1 < (ball D V v i).card)).card * V.card)

@[aesop safe forward (immediate := [free]) (rule_sets := [CHGraphFamilies])]
theorem ledger_packet (free : QFree D V q) : Ledger D V q where
  row := fun _ _ _ hij vv => row_ledger free hij vv
  total := fun _ _ hij => ledger free hij
  parents := fun _ _ hi vv => parent_cap free hi vv
  suppliers := fun _ _ _ hi sv tv => supplier_cap free hi sv tv
  supply := fun _ _ _ hi hj floor => tight_supply free hi hj floor

/-- Floors at two complementary radii, and what is left to spend above them. -/
structure Budget (D : CH.Digraph) (V : Finset ℕ) (i j a b : ℕ) : Prop where
  spend : ∑ v ∈ V, ((ball D V v i).card - a) + ∑ v ∈ V, ((ball D V v j).card - b)
    + ∑ v ∈ V, (gap D V i j v).card + V.card * (a + b) = V.card * (V.card + 1)
  order : V.Nonempty → a + b ≤ V.card + 1
  first : ∀ m, ∑ v ∈ V, ((ball D V v i).card - a) =
    ∑ k ∈ range m, (V.filter (fun v => a + k < (ball D V v i).card)).card
      + ∑ v ∈ V, ((ball D V v i).card - (a + m))
  second : ∀ m, ∑ v ∈ V, ((ball D V v j).card - b) =
    ∑ k ∈ range m, (V.filter (fun v => b + k < (ball D V v j).card)).card
      + ∑ v ∈ V, ((ball D V v j).card - (b + m))

@[aesop safe forward (immediate := [free,hij,hi,hj]) (rule_sets := [CHGraphFamilies])]
theorem budget_packet {i j a b : ℕ} (free : QFree D V q) (hij : i + j ≤ q)
    (hi : ∀ v ∈ V, a ≤ (ball D V v i).card) (hj : ∀ v ∈ V, b ≤ (ball D V v j).card) :
    Budget D V i j a b where
  spend := budget free hij hi hj
  order := card_ge_of_two_balls free hij hi hj
  first := fun m => levels (fun v => (ball D V v i).card) a m V
  second := fun m => levels (fun v => (ball D V v j).card) b m V

/-- Shell laws of a cutoff of at least two. -/
structure Shells (D : CH.Digraph) (V : Finset ℕ) (q : ℕ) : Prop where
  head : ∀ v x k, v ∈ V → x ∈ V → D v x = true → k + 1 ≤ q →
    (ball D V x k).card + 1 ≤ (ball D V v (k + 1)).card
  escape : ∀ p x, x ∈ V → D p x = true → (outN D V p).card ≤ (outN D V x).card →
    ∃ z ∈ outN D V x, z ∉ outN D V p
  complete : ∀ v x b k, x ∈ ball D V v k → b ∈ ball D V v k → D x b = true →
    ball D V v (k+1) \ ball D V v k ⊆ outN D V x →
    (ball D V v (k+2)).card + (outN D (ball D V v k) b).card + 2
      ≤ (ball D V x 2).card + (ball D V v k).card
  full : ∀ v b k, b ∈ ball D V v k →
    (ball D V v (k+1) \ ball D V v k).card + (outN D (ball D V v k) b).card
      ≤ (outN D V b).card →
    ball D V v (k+1) \ ball D V v k ⊆ outN D V b
  chain : ∀ S ⊆ V, S.Nonempty → (∀ x ∈ S, ∃ y ∈ S, D x y = true) → q < S.card
  tied : ∀ v k r c, (∀ x ∈ V, r ≤ (outN D V x).card) →
    (ball D V v (k+1) \ ball D V v k).card < r →
    (∀ x ∈ ball D V v k, ball D V v (k+1) \ ball D V v k ⊆ outN D V x →
      (ball D V x 2).card ≤ c) →
    (ball D V v (k+1) \ ball D V v k).card + c + (ball D V v k).card
      ≤ r + (ball D V v (k+2)).card + 2 →
    (∃ x ∈ ball D V v k, ball D V v (k+1) \ ball D V v k ⊆ outN D V x) →
    q < ((ball D V v k).filter
      (fun x => ball D V v (k+1) \ ball D V v k ⊆ outN D V x)).card
  same : ∀ v w k, k + 1 ≤ q → v ∈ V → w ∈ V → D v w = true →
    ball D V v (k+1) \ ball D V v k = ball D V w (k+1) \ ball D V w k →
    (ball D V w k).card + 1 ≤ (ball D V v k).card
  mask : ∀ (R Y : Finset ℕ) r, R ⊆ V → (∀ v ∈ R, (outN D V v).card = r) →
    (∀ v ∈ R, ball D V v 2 \ ball D V v 1 = Y) →
    R.card * (R.card - 1) ≤ ∑ v ∈ R, (gap D V 2 2 v).card
  floor : ∀ v k r x, (∀ y ∈ V, r ≤ (outN D V y).card) →
    (ball D V v (k+1) \ ball D V v k).card < r → x ∈ ball D V v k →
    ball D V v (k+1) \ ball D V v k ⊆ outN D V x →
    (ball D V v (k+2)).card + 3 ≤ (ball D V x 2).card + (ball D V v k).card
  classes : ∀ k r c (R H : Finset ℕ), (∀ y ∈ V, r ≤ (outN D V y).card) →
    (∀ y ∈ H, (outN D V y).card ≤ r) → (∀ y ∈ H, (ball D V y 2).card ≤ c) →
    (∀ v ∈ R, (ball D V v (k+1) \ ball D V v k).card + 1 = r) →
    (∀ v ∈ R, (ball D V v (k+1) \ ball D V v k).card + c + (ball D V v k).card
      ≤ r + (ball D V v (k+2)).card + 2) →
    (∀ v ∈ R, ∃ x ∈ ball D V v k, ball D V v (k+1) \ ball D V v k ⊆ outN D V x) →
    (∀ v ∈ R, ∀ x ∈ ball D V v k,
      ball D V v (k+1) \ ball D V v k ⊆ outN D V x → x ∈ H) →
    (q + 1) * (R.image (fun v => ball D V v (k+1) \ ball D V v k)).card ≤ H.card
  split : ∀ t r k v, (∀ y ∈ V, r ≤ (outN D V y).card) → v ∈ V → k + 1 ≤ q →
    (ball D V v (k+1) \ ball D V v k).card + t ≤ r + 1 →
    (∃ x ∈ ball D V v k, ball D V v (k+1) \ ball D V v k ⊆ outN D V x) ∨
      ∀ x ∈ (ball D V v k).erase v, t ≤ (outN D ((ball D V v k).erase v) x).card
  roots : ∀ r (R : Finset ℕ), R ⊆ V → (∀ v ∈ R, (outN D V v).card = r) →
    2 * R.card ≤ 2 * (R.image (fun v => ball D V v 2 \ ball D V v 1)).card
      + ∑ v ∈ R, (gap D V 2 2 v).card

@[aesop safe forward (immediate := [free,hq]) (rule_sets := [CHGraphFamilies])]
theorem shells_packet (free : QFree D V q) (hq : 2 ≤ q) : Shells D V q where
  head := fun _ _ _ vv xv arc kq => head_ball_lt free vv xv arc kq
  escape := fun _ _ xv arc le => row_escape free (by omega) xv arc le
  complete := fun _ _ _ _ xk bk xb full => complete_row free hq xk bk xb full
  full := fun _ _ _ bk count => full_of_count bk count
  chain := fun _ sv live next => closed_chain free sv live next
  tied := fun _ _ _ _ degree room cap tight live => tied_chain free hq degree room cap tight live
  same := fun _ _ _ kq vv wv arc same => same_shell_lt free kq vv wv arc same
  mask := fun _ _ _ rv deg mask => shell_class free hq rv deg mask
  floor := fun _ _ _ _ degree room xk full => complete_floor free hq degree room xk full
  classes := fun _ _ _ _ _ degree exact cap size tight live high =>
    class_count free hq degree exact cap size tight live high
  split := fun _ _ _ _ degree vv kq floor => complete_or_fragment free degree vv kq floor
  roots := fun _ _ rv deg => class_roots free hq rv deg

/-- What a lower quota says about fragments of a host. -/
structure Growth (D : CH.Digraph) (V : Finset ℕ) (q t : ℕ) : Prop where
  row : ∀ S ⊆ V, S.Nonempty → S.card ≤ q*t → ∃ x ∈ S, (outN D S x).card < t
  escape : ∀ r, (∀ v ∈ V, r ≤ (outN D V v).card) → ∀ S ⊆ V, S.Nonempty → S.card ≤ q*t →
    ∃ x ∈ S, r + 1 ≤ (outN D (V \ S) x).card + t
  complete : ∀ r, (∀ v ∈ V, r ≤ (outN D V v).card) → 1 ≤ r → ∀ v ∈ V, ∀ k, 1 ≤ k → k + 1 ≤ q →
    (ball D V v k).card ≤ q*t + 1 → (ball D V v (k+1) \ ball D V v k).card + t ≤ r + 1 →
    ∃ x ∈ ball D V v k, ball D V v (k+1) \ ball D V v k ⊆ outN D V x
  ball : ∀ r, (∀ v ∈ V, r ≤ (outN D V v).card) → 1 ≤ r → ∀ v ∈ V, ∀ k, 1 ≤ k → k + 1 ≤ q →
    (ball D V v k).card ≤ q*t + 1 → (ball D V v k).card + r + 1 ≤ (ball D V v (k+1)).card + t

@[aesop safe forward (immediate := [none,free]) (rule_sets := [CHGraphFamilies])]
theorem growth_packet {t : ℕ} (none : NoHost q t) (free : QFree D V q) : Growth D V q t where
  row := fun _ sv live small => fragment_row none free sv live small
  escape := fun _ degree _ sv live small => fragment_escape none free degree sv live small
  ball := fun _ degree hr _ vv _ hk kq small => ball_growth none free degree hr vv hk kq small
  complete := fun _ degree hr _ vv _ hk kq small floor =>
    first_complete none free degree hr vv hk kq small floor

attribute [aesop safe forward (immediate := [none,free,sv,live,small,paid]) (rule_sets := [CHGraphFamilies])] fragment_exit

/-! ### The same packets on a native source -/

@[aesop safe forward (immediate := [order]) (rule_sets := [CHGraphFamilies])]
theorem source_ledger {q r n} {X : ShenMinimumOrder.Source q r} (order : X.V.card ≤ n) :
    Ledger X.D X.V q :=
  have _ := order
  ledger_packet X.free

@[aesop safe forward (immediate := [hq,order]) (rule_sets := [CHGraphFamilies])]
theorem source_shells {q r n} {X : ShenMinimumOrder.Source q r} (hq : 2 ≤ q)
    (order : X.V.card ≤ n) : Shells X.D X.V q :=
  have _ := order
  shells_packet X.free hq

@[aesop safe forward (immediate := [none,order]) (rule_sets := [CHGraphFamilies])]
theorem source_growth {q r t n} {X : ShenMinimumOrder.Source q r} (none : NoHost q t)
    (order : X.V.card ≤ n) : Growth X.D X.V q t :=
  have _ := order
  growth_packet none X.free

#print axioms ledger_packet
#print axioms budget_packet
#print axioms shells_packet
#print axioms growth_packet
#print axioms source_ledger
#print axioms source_shells
#print axioms source_growth
end LeanCH.BR.ReachLedgerCatalog
