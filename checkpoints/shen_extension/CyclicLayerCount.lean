import checkpoints.shen_extension.CommonHeadCutDepth

/-! The layer count behind the common-head returns, for every cutoff.

For a vertex p, layer j consists of the vertices at step j of a closed walk
of length q+1 through p. The layers are disjoint and no arc skips forward
over a layer. Choosing a row of least internal outdegree in each layer and
counting its heads gives, at the two-label order,

    o + q² + q·(distinct exterior heads) ≤ 1 + q·(backward arcs) + q·(exterior heads),

where o is the number of vertices outside the layers.

* `layer_count`: the count for any disjoint layers with chosen rows.
* `cycle_layer_inequality`: the layers of closed walks through p.
* `bank_layer_inequality`: the same at the bank label of a shared-parent bank. -/

namespace LeanCH.BR.CyclicLayerCount
open Finset BRq2 BRq3 BR45 FundedCascade BypassRepair BypassBankReplay JointShortcut
open CommonHeadLastCut
open scoped BigOperators

/-- Successor of a layer index around the q+1 layers. -/
def nxt (q i : ℕ) : ℕ := if i = q then 0 else i+1

/-- The layers before layer i. Layer 0 does not count as earlier than the
last layer, which points forward to it. -/
def earlier (L : ℕ → Finset ℕ) (q i : ℕ) : Finset ℕ :=
  if i = q then (Ico 1 q).biUnion L else (range i).biUnion L

private theorem shift_sum (q : ℕ) (g : ℕ → ℕ) :
    ∑ i∈range (q+1), g (nxt q i) = ∑ i∈range (q+1), g i := by
  rw [sum_range_succ,sum_range_succ']
  have last : nxt q q = 0 := by simp [nxt]
  rw [last]
  congr 1
  apply sum_congr rfl
  intro i hi
  have ne : i ≠ q := (mem_range.mp hi).ne
  simp [nxt,ne]

/-- Heads of the chosen rows, counted by layer. Each row has at most
(|L i| - 1)/q heads in its own layer, at most |L (i+1)| in the next one, and
none two or more layers ahead. -/
theorem layer_count {D : CH.Digraph} {V : Finset ℕ} {q s : ℕ} (L : ℕ → Finset ℕ) (r : ℕ → ℕ)
    (sub : ∀ i ≤ q, L i ⊆ V)
    (disj : ∀ i ≤ q, ∀ k ≤ q, i ≠ k → Disjoint (L i) (L k))
    (deg : ∀ i ≤ q, s ≤ (outN D V (r i)).card)
    (light : ∀ i ≤ q, q*(outN D (L i) (r i)).card+1 ≤ (L i).card)
    (noskip : ∀ i ≤ q, ∀ k ≤ q, i+2 ≤ k → outN D (L k) (r i) = ∅) :
    q*(q+1)*s + (V \ (range (q+1)).biUnion L).card + q + 1 +
        q*((range (q+1)).biUnion (fun i => outN D (V \ (range (q+1)).biUnion L) (r i))).card ≤
      (q+1)*V.card + q*(∑ i∈range (q+1), (outN D (earlier L q i) (r i)).card) +
        q*(∑ i∈range (q+1), (outN D (V \ (range (q+1)).biUnion L) (r i)).card) := by
  classical
  let layers := (range (q+1)).biUnion L
  let ext := fun i => outN D (V \ layers) (r i)
  have le {i} (hi : i∈range (q+1)) : i ≤ q := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have lsub : layers ⊆ V := biUnion_subset.mpr (fun i hi => sub i (le hi))
  have row (i) (hi : i∈range (q+1)) :
      s ≤ (outN D (L i) (r i)).card + (L (nxt q i)).card +
        (outN D (earlier L q i) (r i)).card + (ext i).card := by
    have iq := le hi
    have cover : outN D V (r i) ⊆ ((outN D (L i) (r i) ∪ outN D (L (nxt q i)) (r i)) ∪
        outN D (earlier L q i) (r i)) ∪ ext i := by
      intro y hy
      obtain ⟨yv,arc⟩ := mem_outN.mp hy
      by_cases yl : y∈layers
      · obtain ⟨k,hk,yk⟩ := mem_biUnion.mp yl
        have kq := le hk
        have here : y∈outN D (L k) (r i) := mem_outN.mpr ⟨yk,arc⟩
        by_cases ki : k = i
        · subst ki
          simp [here]
        by_cases last : i = q
        · by_cases k0 : k = 0
          · have e : nxt q i = k := by simp [nxt,last,k0]
            simp [e,here]
          · have back : y∈outN D (earlier L q i) (r i) := mem_outN.mpr
              ⟨by rw [earlier,if_pos last]
                  exact mem_biUnion.mpr ⟨k,mem_Ico.mpr ⟨by omega,by omega⟩,yk⟩,arc⟩
            simp [back]
        · by_cases lo : k < i
          · have back : y∈outN D (earlier L q i) (r i) := mem_outN.mpr
              ⟨by rw [earlier,if_neg last]
                  exact mem_biUnion.mpr ⟨k,mem_range.mpr lo,yk⟩,arc⟩
            simp [back]
          · by_cases one : k = i+1
            · have e : nxt q i = k := by simp [nxt,last,one]
              simp [e,here]
            · have none := noskip i iq k kq (by omega)
              rw [none] at here
              exact (notMem_empty _ here).elim
      · have out : y∈ext i := mem_outN.mpr ⟨mem_sdiff.mpr ⟨yv,yl⟩,arc⟩
        simp [out]
    have c := card_le_card cover
    have u1 := card_union_le ((outN D (L i) (r i) ∪ outN D (L (nxt q i)) (r i)) ∪
      outN D (earlier L q i) (r i)) (ext i)
    have u2 := card_union_le (outN D (L i) (r i) ∪ outN D (L (nxt q i)) (r i))
      (outN D (earlier L q i) (r i))
    have u3 := card_union_le (outN D (L i) (r i)) (outN D (L (nxt q i)) (r i))
    have fw := card_le_card (outN_subset : outN D (L (nxt q i)) (r i) ⊆ L (nxt q i))
    have d := deg i iq
    omega
  have total := sum_le_sum row
  simp only [sum_add_distrib,sum_const,card_range,smul_eq_mul] at total
  rw [shift_sum q (fun i => (L i).card)] at total
  have mass : layers.card = ∑ i∈range (q+1), (L i).card :=
    card_biUnion (fun i hi k hk ne => disj i (le hi) k (le hk) ne)
  have thin := sum_le_sum (fun i (hi : i∈range (q+1)) => light i (le hi))
  simp only [sum_add_distrib,sum_const,card_range,smul_eq_mul,← mul_sum,mul_one] at thin
  have split := card_sdiff_add_card_eq_card lsub
  have outer : ((range (q+1)).biUnion ext).card ≤ (V \ layers).card :=
    card_le_card (biUnion_subset.mpr (fun i _ => outN_subset))
  change q*(q+1)*s + (V \ layers).card + q + 1 + q*((range (q+1)).biUnion ext).card ≤
    (q+1)*V.card + q*(∑ i∈range (q+1), (outN D (earlier L q i) (r i)).card) +
      q*(∑ i∈range (q+1), (ext i).card)
  rw [← mass] at total thin
  generalize (∑ i∈range (q+1), (outN D (L i) (r i)).card) = SI at total thin
  generalize (∑ i∈range (q+1), (outN D (earlier L q i) (r i)).card) = B at total ⊢
  generalize (∑ i∈range (q+1), (ext i).card) = X at total ⊢
  generalize ((range (q+1)).biUnion ext).card = un at outer ⊢
  generalize (V \ layers).card = o at split outer ⊢
  generalize layers.card = M at total thin split
  have scaled := Nat.mul_le_mul_left q total
  have outs := Nat.mul_le_mul_left q outer
  nlinarith [scaled,outs,thin,split]

/-- Vertices at step j of a closed walk of length q+1 through p. -/
noncomputable def ring (D : CH.Digraph) (V : Finset ℕ) (q p j : ℕ) : Finset ℕ := by
  classical
  exact V.filter (fun x => Walk D V p x j ∧ Walk D V x p (q+1-j))

theorem mem_ring {D : CH.Digraph} {V : Finset ℕ} {q p j x : ℕ} :
    x∈ring D V q p j ↔ x∈V ∧ Walk D V p x j ∧ Walk D V x p (q+1-j) := by
  classical
  simp [ring]

private theorem walk_split {D : CH.Digraph} {V : Finset ℕ} {c : ℕ} (j k : ℕ) :
    ∀ {a}, Walk D V a c (j+k) → ∃ b, Walk D V a b j ∧ Walk D V b c k := by
  induction j with
  | zero => intro a w; exact ⟨a,.refl a,by simpa using w⟩
  | succ j ih =>
    intro a w
    rw [show j+1+k = (j+k)+1 by omega] at w
    cases w with
    | step bv ab rest =>
      obtain ⟨b,w1,w2⟩ := ih rest
      exact ⟨b,.step bv ab w1,w2⟩

/-- The layers of closed walks through p: the last one is p itself. -/
noncomputable def layer (D : CH.Digraph) (V : Finset ℕ) (q p i : ℕ) : Finset ℕ :=
  if i = q then {p} else ring D V q p (i+1)

/-- At the two-label order, the layers of closed walks of length q+1 through
p have chosen rows whose backward arcs and repeated exterior heads pay for
all vertices outside the layers, and for q² - 1 more. -/
theorem cycle_layer_inequality {D : CH.Digraph} {V : Finset ℕ} {q t p : ℕ}
    (free : QFree D V q) (hq : 1 ≤ q) (reg : OutEq (t+1) D V)
    (lower : ∀ k, k<t+1 → NoHost q k) (pv : p∈V) (cyc : Walk D V p p (q+1))
    (order : V.card = q*t+2) :
    ∃ r : ℕ → ℕ, (∀ i<q, r i∈ring D V q p (i+1)) ∧ r q = p ∧
      (V \ (range (q+1)).biUnion (layer D V q p)).card + q*q +
          q*((range (q+1)).biUnion
            (fun i => outN D (V \ (range (q+1)).biUnion (layer D V q p)) (r i))).card ≤
        1 + q*(∑ i∈range (q+1), (outN D (earlier (layer D V q p) q i) (r i)).card) +
          q*(∑ i∈range (q+1),
            (outN D (V \ (range (q+1)).biUnion (layer D V q p)) (r i)).card) := by
  classical
  let L := layer D V q p
  have ringV (j) : ring D V q p j ⊆ V := fun x hx => (mem_ring.mp hx).1
  have notp {j} (j1 : 1 ≤ j) (jq : j ≤ q) : p∉ring D V q p j := fun hp =>
    free p j j1 jq (mem_ring.mp hp).2.1
  have apart {j k} (j1 : 1 ≤ j) (jk : j < k) (kq : k ≤ q) :
      Disjoint (ring D V q p j) (ring D V q p k) := by
    apply disjoint_left.mpr
    intro x xj xk
    have w := (mem_ring.mp xj).2.1.append (mem_ring.mp xk).2.2
    exact free p _ (by omega) (by omega) w
  have live (j) (j1 : 1 ≤ j) (jq : j ≤ q) : (ring D V q p j).Nonempty := by
    have w := cyc
    rw [show q+1 = j+(q+1-j) by omega] at w
    obtain ⟨b,w1,w2⟩ := walk_split j (q+1-j) w
    have bv : b∈V := (w1.end_mem_or).elim (fun e => e ▸ pv) id
    exact ⟨b,mem_ring.mpr ⟨bv,w1,w2⟩⟩
  have exit {j x} (j1 : 1 ≤ j) (jq : j ≤ q) (xr : x∈ring D V q p j) :
      ∃ y∈V, D x y = true ∧ y∉ring D V q p j := by
    obtain ⟨_,w1,w2⟩ := mem_ring.mp xr
    rw [show q+1-j = (q-j)+1 by omega] at w2
    cases w2 with
    | step yv xy rest =>
      refine ⟨_,yv,xy,fun yr => ?_⟩
      have w := (mem_ring.mp yr).2.1.append rest
      exact free p _ (by omega) (by omega) w
  have pick (j) (j1 : 1 ≤ j) (jq : j ≤ q) : ∃ x∈ring D V q p j,
      q*(outN D (ring D V q p j) x).card+1 ≤ (ring D V q p j).card := by
    let K := ring D V q p j
    obtain ⟨x,xk,least⟩ := K.exists_min_image (fun i => (outN D K i).card) (live j j1 jq)
    refine ⟨x,xk,?_⟩
    by_contra! heavy
    obtain ⟨y,yv,xy,off⟩ := exit j1 jq xk
    have inside : outN D K x ⊂ outN D V x := by
      refine ⟨fun z hz => mem_outN.mpr ⟨ringV j (mem_outN.mp hz).1,(mem_outN.mp hz).2⟩,
        fun all => off (mem_outN.mp (all (mem_outN.mpr ⟨yv,xy⟩))).1⟩
    have small := card_lt_card inside
    rw [reg x (ringV j xk)] at small
    exact lower _ small D K (live j j1 jq) (Nat.lt_succ_iff.mp heavy)
      (free.mono_set (ringV j)) least
  choose! g gm glight using pick
  let r : ℕ → ℕ := fun i => if i = q then p else g (i+1)
  have rq : r q = p := by simp [r]
  have rlow {i} (iq : i < q) : r i = g (i+1) := by simp [r,iq.ne]
  have Llow {i} (iq : i < q) : L i = ring D V q p (i+1) := by simp [L,layer,iq.ne]
  have Lq : L q = {p} := by simp [L,layer]
  have rin {i} (iq : i < q) : r i∈ring D V q p (i+1) := by
    rw [rlow iq]; exact gm (i+1) (by omega) (by omega)
  have sub : ∀ i ≤ q, L i ⊆ V := by
    intro i iq
    rcases Nat.lt_or_ge i q with lo | hi
    · rw [Llow lo]; exact ringV _
    · rw [show i = q by omega,Lq]; exact singleton_subset_iff.mpr pv
  have disj : ∀ i ≤ q, ∀ k ≤ q, i ≠ k → Disjoint (L i) (L k) := by
    intro i iq k kq ne
    rcases Nat.lt_or_ge i q with ilo | ihi
    · rcases Nat.lt_or_ge k q with klo | khi
      · rw [Llow ilo,Llow klo]
        rcases Nat.lt_or_gt_of_ne ne with a | a
        · exact apart (by omega) (by omega) (by omega)
        · exact (apart (by omega) (by omega) (by omega)).symm
      · rw [Llow ilo,show k = q by omega,Lq]
        exact disjoint_singleton_right.mpr (notp (by omega) (by omega))
    · rcases Nat.lt_or_ge k q with klo | khi
      · rw [show i = q by omega,Lq,Llow klo]
        exact disjoint_singleton_left.mpr (notp (by omega) (by omega))
      · exact (ne (by omega)).elim
  have rv {i} (iq : i ≤ q) : r i∈V := by
    rcases Nat.lt_or_ge i q with lo | hi
    · exact ringV _ (rin lo)
    · rw [show i = q by omega,rq]; exact pv
  have deg : ∀ i ≤ q, t+1 ≤ (outN D V (r i)).card := fun i iq => (reg _ (rv iq)).ge
  have light : ∀ i ≤ q, q*(outN D (L i) (r i)).card+1 ≤ (L i).card := by
    intro i iq
    rcases Nat.lt_or_ge i q with lo | hi
    · rw [Llow lo,rlow lo]; exact glight (i+1) (by omega) (by omega)
    · have e : i = q := by omega
      subst e
      have none : outN D (L i) (r i) = ∅ := by
        rw [Lq,rq]
        exact eq_empty_iff_forall_notMem.mpr (fun y hy => by
          obtain ⟨ym,arc⟩ := mem_outN.mp hy
          rw [mem_singleton.mp ym] at arc
          exact free p 1 (by omega) hq (.step pv arc (.refl _)))
      rw [none,Lq]
      simp
  have noskip : ∀ i ≤ q, ∀ k ≤ q, i+2 ≤ k → outN D (L k) (r i) = ∅ := by
    intro i iq k kq far
    have ilo : i < q := by omega
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨yk,arc⟩ := mem_outN.mp hy
    obtain ⟨_,w1,_⟩ := mem_ring.mp (rin ilo)
    rcases Nat.lt_or_ge k q with klo | khi
    · rw [Llow klo] at yk
      obtain ⟨yv,_,w2⟩ := mem_ring.mp yk
      have w := (w1.snoc yv arc).append w2
      exact free p _ (by omega) (by omega) w
    · rw [show k = q by omega,Lq] at yk
      rw [mem_singleton.mp yk] at arc
      exact free p _ (by omega) (by omega) (w1.snoc pv arc)
  have count := layer_count (D:=D) (V:=V) (q:=q) (s:=t+1) L r sub disj deg light noskip
  refine ⟨r,fun i iq => rin iq,rq,?_⟩
  change (V \ (range (q+1)).biUnion L).card + q*q +
      q*((range (q+1)).biUnion (fun i => outN D (V \ (range (q+1)).biUnion L) (r i))).card ≤
    1 + q*(∑ i∈range (q+1), (outN D (earlier L q i) (r i)).card) +
      q*(∑ i∈range (q+1), (outN D (V \ (range (q+1)).biUnion L) (r i)).card)
  rw [order] at count
  generalize (V \ (range (q+1)).biUnion L).card = o at count ⊢
  generalize ((range (q+1)).biUnion
    (fun i => outN D (V \ (range (q+1)).biUnion L) (r i))).card = un at count ⊢
  generalize (∑ i∈range (q+1), (outN D (earlier L q i) (r i)).card) = B at count ⊢
  generalize (∑ i∈range (q+1), (outN D (V \ (range (q+1)).biUnion L) (r i)).card) = X at count ⊢
  nlinarith [count]

/-- The count at the bank label of a two-label bank with shared fresh
targets. An assigned return gives the closed walk through p. -/
theorem bank_layer_inequality {D : CH.Digraph} {V : Finset ℕ} {q t p h : ℕ}
    (free : QFree D V q) (hq : 3 ≤ q) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (pv : p∈V) (hv : h∈V) (ph : p≠h) (bank : Eligible V {p,h} q t)
    (none : NoHost q t) (lower : ∀ k, k<t+1 → NoHost q k) (order : V.card = q*t+2)
    (f : ℕ → ℕ) (choose : ∀ u∈jointParents D V p h, f u∈heads D V p h ∧ D u (f u)≠true) :
    ∃ r : ℕ → ℕ, (∀ i<q, r i∈ring D V q p (i+1)) ∧ r q = p ∧
      (V \ (range (q+1)).biUnion (layer D V q p)).card + q*q +
          q*((range (q+1)).biUnion
            (fun i => outN D (V \ (range (q+1)).biUnion (layer D V q p)) (r i))).card ≤
        1 + q*(∑ i∈range (q+1), (outN D (earlier (layer D V q p) q i) (r i)).card) +
          q*(∑ i∈range (q+1),
            (outN D (V \ (range (q+1)).biUnion (layer D V q p)) (r i)).card) := by
  classical
  obtain ⟨u,us,back⟩ := chosen_return (C:=fun _ => ∅) free hq reg (by omega) pv hv ph
    (by simpa using bank) (by simpa using none) f choose (fun y _ => by simp)
  have native : Walk D V (f u) u (q-1) := (walk_sub cut_sub back).mono sdiff_subset
  obtain ⟨uv,up,_⟩ := parent_data us
  have zv : f u∈V := outN_subset (mem_inter.mp (choose u us).1).1
  have pz : D p (f u) = true := (mem_outN.mp (mem_inter.mp (choose u us).1).1).2
  have cyc : Walk D V p p (q+1) := by
    have w : Walk D V p p (((q-1)+1)+1) := .step zv pz (native.snoc pv up)
    rwa [show ((q-1)+1)+1 = q+1 by omega] at w
  exact cycle_layer_inequality free (by omega) reg lower pv cyc order

/-- A vertex of layer j has a predecessor one layer earlier: p itself for
j = 1. So an arc from a later row back into layer j is a common head of that
row and of a vertex two or more layers before it. -/
theorem backward_common_head {D : CH.Digraph} {V : Finset ℕ} {q p j a : ℕ}
    (pv : p∈V) (j1 : 1 ≤ j) (jq : j ≤ q) (aj : a∈ring D V q p j) :
    ∃ b∈V, D b a = true ∧ ((j = 1 ∧ b = p) ∨ (2 ≤ j ∧ b∈ring D V q p (j-1))) := by
  classical
  obtain ⟨av,w1,w2⟩ := mem_ring.mp aj
  rw [show j = (j-1)+1 by omega] at w1
  obtain ⟨y,wy,_,ya⟩ := w1.unsnoc
  have yv : y∈V := (wy.end_mem_or).elim (fun e => e ▸ pv) id
  refine ⟨y,yv,ya,?_⟩
  by_cases one : j = 1
  · left
    subst one
    cases wy
    exact ⟨rfl,rfl⟩
  · right
    refine ⟨by omega,mem_ring.mpr ⟨yv,wy,?_⟩⟩
    have w : Walk D V y p ((q+1-j)+1) := .step av ya w2
    rwa [show (q+1-j)+1 = q+1-(j-1) by omega] at w

/-- A common predecessor of two vertices whose layers are two or more apart
is not p and lies in no layer before the one preceding the later vertex. It
is outside the layers, or its arc into the earlier vertex goes backward. -/
theorem cross_layer_parent {D : CH.Digraph} {V : Finset ℕ} {q p j k a x y : ℕ}
    (free : QFree D V q) (pv : p∈V) (j1 : 1 ≤ j) (jk : j+2 ≤ k) (kq : k ≤ q)
    (yk : y∈ring D V q p k) (ay : D a y = true) :
    a ≠ p ∧ ∀ i, 1 ≤ i → i+2 ≤ k → a∉ring D V q p i := by
  classical
  obtain ⟨yv,_,w2⟩ := mem_ring.mp yk
  constructor
  · rintro rfl
    exact free a _ (by omega) (by omega) (.step yv ay w2)
  · intro i i1 ik ai
    have w := ((mem_ring.mp ai).2.1.snoc yv ay).append w2
    exact free p _ (by omega) (by omega) w

/-- At the two-label order any two vertices have a common predecessor. -/
theorem pair_parent {D : CH.Digraph} {V : Finset ℕ} {q t x y : ℕ}
    (free : QFree D V q) (hq : 1 ≤ q) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (none : NoHost q t) (order : V.card = q*t+2)
    (xv : x∈V) (yv : y∈V) (xy : x≠y) : ∃ a∈V, D a x = true ∧ D a y = true := by
  classical
  by_contra! lone
  let B : Finset ℕ := {x,y}
  have bv : B ⊆ V := insert_subset xv (singleton_subset_iff.mpr yv)
  have size : (V \ B).card = q*t := by
    rw [card_sdiff_of_subset bv,card_pair xy,order]; omega
  have live : (V \ B).Nonempty := card_pos.mp (by
    rw [size]; exact Nat.mul_pos (by omega) (by omega))
  apply none D (V \ B) live size.le (free.mono_set sdiff_subset)
  intro a au
  have av := (mem_sdiff.mp au).1
  have split := card_outN_union (D:=D) (show Disjoint B (V \ B) from disjoint_sdiff) a
  rw [union_sdiff_of_subset bv,reg a av] at split
  have few : (outN D B a).card ≤ 1 := by
    by_contra! two
    have all : outN D B a = B := eq_of_subset_of_card_le outN_subset
      ((card_pair xy).le.trans two)
    have ax : D a x = true := (mem_outN.mp (all ▸ (by simp [B] : x∈B))).2
    have ay : D a y = true := (mem_outN.mp (all ▸ (by simp [B] : y∈B))).2
    exact lone a av ax ay
  omega

/-- Two vertices in layers two or more apart have a common predecessor that
is not p and lies in no layer before the one preceding the later vertex. -/
theorem chord_parent {D : CH.Digraph} {V : Finset ℕ} {q t p j k x y : ℕ}
    (free : QFree D V q) (hq : 1 ≤ q) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (none : NoHost q t) (order : V.card = q*t+2) (pv : p∈V)
    (j1 : 1 ≤ j) (jk : j+2 ≤ k) (kq : k ≤ q)
    (xj : x∈ring D V q p j) (yk : y∈ring D V q p k) :
    ∃ a∈V, D a x = true ∧ D a y = true ∧ a ≠ p ∧
      ∀ i, 1 ≤ i → i+2 ≤ k → a∉ring D V q p i := by
  classical
  have xv := (mem_ring.mp xj).1
  have yv := (mem_ring.mp yk).1
  have ne : x ≠ y := by
    rintro rfl
    have w := (mem_ring.mp xj).2.1.append (mem_ring.mp yk).2.2
    exact free p _ (by omega) (by omega) w
  obtain ⟨a,av,ax,ay⟩ := pair_parent free hq reg ht none order xv yv ne
  obtain ⟨np,off⟩ := cross_layer_parent (j:=j) (x:=x) free pv j1 jk kq yk ay
  exact ⟨a,av,ax,ay,np,off⟩

#print axioms layer_count
#print axioms cycle_layer_inequality
#print axioms bank_layer_inequality
#print axioms backward_common_head
#print axioms cross_layer_parent
#print axioms pair_parent
#print axioms chord_parent
end LeanCH.BR.CyclicLayerCount
