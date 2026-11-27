import checkpoints.shen_extension.BypassBankReplay
import LeanCH.BR.Compose.ThinRigid

namespace LeanCH.BR.BypassBankReplay
open Finset BRq2 BRq3 BR45 BypassRepair RemoteParentPacking

/-- In any backward walk, the missed heads charged at different steps of a
window are disjoint. The choice of predecessor at each step is unrestricted. -/
theorem unrestricted_window {D V q s} (reg : OutEq s D V) (room : V.card ≤ q*s)
    {v : ℕ → ℕ} (live : ∀ i, v i ∈ V) (edge : ∀ i, D (v (i+1)) (v i) = true) (a : ℕ) :
    s ≤ ∑ i ∈ range (q+1), (outN D V (v (a+i+1)) \ missed D V q (v (a+i))).card := by
  classical
  let H := fun i => outN D V (v (a+i+1))
  let M := fun i => H i ∩ missed D V q (v (a+i))
  have route {i y} (hit : y ∈ M i) (k : ℕ) : Walk D V (v (a+i+k+1)) y (k+1) := by
    induction k with
    | zero =>
      have h := mem_outN.mp (mem_inter.mp hit).1
      exact .step h.1 h.2 (.refl _)
    | succ k ih => exact .step (live _) (edge _) ih
  have apart {i j} (lt : i < j) (le : j ≤ q) : Disjoint (M i) (M j) := by
    refine disjoint_left.mpr (fun y yi yj => ?_)
    have w := route yi (j-i-1)
    rw [show a+i+(j-i-1)+1 = a+j by omega] at w
    exact misses_positive (mem_inter.mp yj).2 (by omega) (by omega) w
  have dis : (↑(range (q+1)) : Set ℕ).PairwiseDisjoint M := by
    intro i hi j hj ne
    have li := mem_range.mp hi
    have lj := mem_range.mp hj
    rcases lt_or_gt_of_ne ne with ll|gg
    · exact apart ll (by omega)
    · exact (apart gg (by omega)).symm
  have sub : (range (q+1)).biUnion M ⊆ V := by
    intro y hy
    obtain ⟨i, _, yi⟩ := mem_biUnion.mp hy
    exact outN_subset (mem_inter.mp yi).1
  have bound := card_le_card sub
  rw [card_biUnion dis] at bound
  have split (i : ℕ) : (H i \ missed D V q (v (a+i))).card + (M i).card = s :=
    (card_sdiff_add_card_inter (H i) _).trans (reg _ (live _))
  have sum : (∑ i ∈ range (q+1), (H i \ missed D V q (v (a+i))).card) +
      (∑ i ∈ range (q+1), (M i).card) = (q+1)*s := by
    rw [← sum_add_distrib]
    simp [split]
  change s ≤ ∑ i ∈ range (q+1), (H i \ missed D V q (v (a+i))).card
  rw [Nat.add_mul, Nat.one_mul] at sum
  omega

theorem chain_through_arc {q s} (X : ShenMinimumOrder.Source q s) (hq : 2 ≤ q)
    (hs : 0 < s) (reg : OutEq s X.D X.V) (room : X.V.card ≤ q*s)
    {x p z} (xv : x ∈ X.V) (pv : p ∈ X.V) (zv : z ∈ X.V)
    (xp : X.D x p = true) (pz : X.D p z = true) :
    ∃ v : ℕ → ℕ, v 2 = x ∧ v 1 = p ∧ (∀ i, X.D (v (i+1)) (v i) = true) ∧
      ∀ a, s ≤ ∑ i ∈ range (q+1),
        (outN X.D X.V (v (a+i+1)) \ missed X.D X.V q (v (a+i))).card := by
  classical
  let takeParent (u : ↥X.V) := ShenCycleSuccessor.fixed_parent X hq hs u.property
  let next (u : ↥X.V) : ↥X.V :=
    ⟨(takeParent u).choose, (takeParent u).choose_spec.1⟩
  let walk (i : ℕ) : ↥X.V := Nat.rec ⟨x,xv⟩ (fun _ u => next u) i
  let v : ℕ → ℕ
    | 0 => z
    | 1 => p
    | i+2 => (walk i).val
  have live : ∀ i, v i ∈ X.V
    | 0 => zv
    | 1 => pv
    | i+2 => (walk i).property
  have edge : ∀ i, X.D (v (i+1)) (v i) = true
    | 0 => pz
    | 1 => xp
    | i+2 => (takeParent (walk i)).choose_spec.2.1
  exact ⟨v,rfl,rfl,edge,unrestricted_window reg room live edge⟩

/-- Extend two designated heads of the marked row together with prescribed
additional labels while retaining a second row that loses at least two heads. -/
theorem extend_joint_bank_at {q s} {X : ShenMinimumOrder.Source q s}
    (hq : 2 ≤ q) (hs : 4 ≤ s) (reg : OutEq s X.D X.V) (room : X.V.card ≤ q*s)
    {b x j p z : ℕ} (size : b = X.V.card-q*(s-1)) (lower : 2 ≤ b)
    (space : b+s+1 ≤ X.V.card) (xv : x ∈ X.V) (jv : j ∈ X.V)
    (zv : z ∈ X.V) (pz : X.D p z = true) (fresh : X.D x z ≠ true)
    {T K : Finset ℕ} (heads : T ⊆ outN X.D X.V x) (two : T.card = 2)
    (pt : p ∈ T) (jt : j ∉ T)
    (keep : K ⊆ X.V \ (outN X.D X.V x ∪ {x,z,j})) (fit : K.card ≤ b-2)
    (other : 2 ≤ (outN X.D (T ∪ K) j).card) :
    ∃ B, Marked X ⟨B,x,p,z⟩ ∧ j ∈ X.V \ B ∧ (outN X.D (X.V \ B) j).card < s-1 := by
  classical
  let H := outN X.D X.V x
  let A := X.V \ (H ∪ {x,z,j})
  have three : ({x,z,j} : Finset ℕ).card ≤ 3 := by
    have h1 := card_insert_le x ({z,j}:Finset ℕ)
    have h2 : ({z,j}:Finset ℕ).card ≤ 2 := card_le_two
    omega
  have plentiful : b-2 ≤ A.card := by
    have h1 := card_le_card_sdiff_add_card (s:=X.V) (t:=H ∪ {x,z,j})
    have h2 := card_union_le H ({x,z,j}:Finset ℕ)
    have h3 : H.card=s := reg _ xv
    change b-2 ≤ (X.V \ (H ∪ {x,z,j})).card
    omega
  obtain ⟨F,kf,fa,fc⟩ := exists_subsuperset_card_eq keep fit plentiful
  let B := T ∪ F
  have off {u} (uF : u ∈ F) : u ∉ H ∪ {x,z,j} := (mem_sdiff.mp (fa uF)).2
  have apart : Disjoint T F := disjoint_left.mpr (fun u ut uf => off uf (mem_union_left _ (heads ut)))
  have bv : B ⊆ X.V := union_subset (heads.trans outN_subset) (fa.trans sdiff_subset)
  have bc : B.card=b := by
    rw [show B=T∪F from rfl,card_union_of_disjoint apart,two,fc]
    omega
  have xB : x ∉ B := by
    intro h
    rcases mem_union.mp h with ht|hf
    · exact loopfree X.free (by omega) xv (mem_outN.mp (heads ht)).2
    · exact off hf (by simp)
  have zB : z ∉ B := by
    intro h
    rcases mem_union.mp h with ht|hf
    · exact fresh (mem_outN.mp (heads ht)).2
    · exact off hf (by simp)
  have jB : j ∉ B := by
    intro h
    rcases mem_union.mp h with ht|hf
    · exact jt ht
    · exact off hf (by simp)
  have removed (u : ℕ) : outN X.D (X.V \ B) u = outN X.D X.V u \ B := by
    ext h; simp only [mem_outN,mem_sdiff]; tauto
  have inter : H ∩ B = T := by
    ext a
    constructor
    · intro h
      rcases mem_union.mp (mem_inter.mp h).2 with ht|hf
      · exact ht
      · exact False.elim (off hf (mem_union_left _ (mem_inter.mp h).1))
    · exact fun ht => mem_inter.mpr ⟨heads ht,mem_union_left _ ht⟩
  have dx : (outN X.D (X.V \ B) x).card+1=s-1 := by
    have h := card_sdiff_add_card_inter H B
    rw [inter,two,show H.card=s from reg _ xv] at h
    rw [removed]
    change (H \ B).card+1=s-1
    omega
  have inside : outN X.D (T ∪ K) j ⊆ outN X.D X.V j ∩ B := by
    intro a ha
    obtain ⟨aTK,edge⟩ := mem_outN.mp ha
    have aB := (union_subset_union (Subset.rfl : T ⊆ T) kf) aTK
    exact mem_inter.mpr ⟨mem_outN.mpr ⟨bv aB,edge⟩,aB⟩
  have dj : (outN X.D (X.V \ B) j).card < s-1 := by
    have h := card_sdiff_add_card_inter (outN X.D X.V j) B
    have h2 := other.trans (card_le_card inside)
    rw [reg _ jv] at h
    rw [removed]
    omega
  obtain ⟨pv,xp⟩ := mem_outN.mp (heads pt)
  have chain := chain_through_arc X hq (by omega) reg room xv pv zv xp pz
  exact ⟨B,⟨bv,bc.trans size,mem_sdiff.mpr ⟨xv,xB⟩,mem_union_left _ pt,
    mem_sdiff.mpr ⟨zv,zB⟩,xp,pz,fresh,dx,chain⟩,mem_sdiff.mpr ⟨jv,jB⟩,dj⟩

theorem extend_joint_bank {q s} {X : ShenMinimumOrder.Source q s}
    (hq : 2 ≤ q) (hs : 4 ≤ s) (reg : OutEq s X.D X.V) (room : X.V.card ≤ q*s)
    {b x j p z : ℕ} (size : b = X.V.card-q*(s-1)) (lower : 2 ≤ b)
    (space : b+s+1 ≤ X.V.card) (xv : x ∈ X.V) (jv : j ∈ X.V) (jne : j ≠ x)
    (zv : z ∈ X.V) (pz : X.D p z = true) (fresh : X.D x z ≠ true)
    {T K : Finset ℕ} (heads : T ⊆ outN X.D X.V x) (two : T.card = 2)
    (pt : p ∈ T) (jt : j ∉ T)
    (keep : K ⊆ X.V \ (outN X.D X.V x ∪ {x,z,j})) (fit : K.card ≤ b-2)
    (other : 2 ≤ (outN X.D (T ∪ K) j).card) :
    ∃ m, Marked X m ∧ JointShort X m := by
  obtain ⟨B,marked,jb,short⟩ := extend_joint_bank_at hq hs reg room size lower space xv jv
    zv pz fresh heads two pt jt keep fit other
  exact ⟨⟨B,x,p,z⟩,marked,j,jb,jne,short⟩

end LeanCH.BR.BypassBankReplay

