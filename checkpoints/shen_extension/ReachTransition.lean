import checkpoints.shen_extension.ParentIntersection
import checkpoints.shen_extension.RootedKernelTransition
import checkpoints.shen_extension.LabelledReachTensor
import checkpoints.shen_extension.CommonTensorClosure
import checkpoints.shen_extension.SeymourTransition

namespace LeanCH.BR.ShenReachTransition
open BRq2 BRq3 Finset ShenLabelledReach
open Classical

/-- An arc in the new graph represents an actual reach entry. Its price is
computed from the difference of the two original ball rows. -/
noncomputable def nextGraph (D : CH.Digraph) (V : Finset ℕ) (q k : ℕ)
    (radius potential : ℕ → ℕ) : CH.Digraph := fun x y => decide
  (x∈V ∧ x≠y ∧ y∈ball D V x (radius x) ∧
    k * cost D V q radius x y + potential x ≤ q + potential y)

private theorem lift_walk {D V q k radius potential}
    (free : QFree D V q) (bounds : ∀ x∈V, radius x≤q) {a b m}
    (p : Walk (nextGraph D V q k radius potential) V a b m) :
    ∃ l, m≤l ∧ k*l+potential a≤m*q+potential b ∧ Walk D V a b l := by
  induction p with
  | refl a => exact ⟨0,le_rfl,by simp,.refl a⟩
  | @step a j b m hj edge tail ih =>
    obtain ⟨ha,ne,entry,price⟩ := of_decide_eq_true edge
    obtain ⟨d,pos,cap,path⟩ := lift_entry free ha (bounds a ha) ne entry
    obtain ⟨l,lo,hi,walk⟩ := ih
    refine ⟨d+l,by omega,?_,path.append walk⟩
    rw [Nat.succ_mul,Nat.mul_add]
    have paid := Nat.mul_le_mul_left k cap
    omega

theorem next_free {D V q k radius potential} (free : QFree D V q)
    (bounds : ∀ x∈V, radius x≤q) (hk : 0<k) :
    QFree (nextGraph D V q k radius potential) V k := by
  intro a m pos cap walk
  obtain ⟨l,lo,hi,path⟩ := lift_walk free bounds walk
  have room := Nat.mul_le_mul_right q cap
  exact free a l (by omega) (Nat.le_of_mul_le_mul_left (by omega : k*l≤k*q) hk) path

private theorem from_edges {D : CH.Digraph} {n} (a) (tail : List ℕ)
    (inside : ∀ x∈tail, x<n) (edges : CH.EdgesFrom D a tail) :
    Walk D (range n) a (tail.getLastD a) tail.length := by
  induction tail generalizing a with
  | nil => exact .refl a
  | cons b rest ih =>
    have sub (x) (hx : x∈rest) := inside x (List.mem_cons_of_mem _ hx)
    have walk := Walk.step (mem_range.mpr (inside b (by simp))) edges.1 (ih b sub edges.2)
    simpa only [List.getLastD_cons,List.length_cons] using walk

theorem no_cycle_of_free {D n q} (free : QFree D (range n) q) :
    ¬CH.HasDirectedCycleAtMost D n q := by
  rintro ⟨l,cycle,bound⟩
  cases l with
  | nil => exact cycle.elim
  | cons a tail =>
    obtain ⟨_,_,inside,edges,last⟩ := cycle
    have path := from_edges a tail (fun x hx => inside _ (List.mem_cons_of_mem _ hx)) edges
    exact free a (tail.length+1) (by omega) bound
      (path.snoc (mem_range.mpr (inside a (by simp))) last)

/-- A closed child at a smaller cutoff gives a literal cycle on the parent.
The same labels can be used again at the next step. -/
theorem pullback {D n q k radius potential} (loop : CH.Loopless D n)
    (bounds : ∀ x∈range n, radius x≤q) (hk : 0<k)
    (child : CH.HasDirectedCycleAtMost (nextGraph D (range n) q k radius potential) n k) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  exact no_cycle_of_free (next_free (qfree_of_noShort loop no) bounds hk) child

theorem next_loopless (D : CH.Digraph) (n q h) (radius potential : ℕ → ℕ) :
    CH.Loopless (nextGraph D (range n) q h radius potential) n := by
  intro x _
  simp [nextGraph]

/-- A new head at a vertex of maximal potential on S costs at most q/k
whenever the head also belongs to S. This uses the actual underlying walk. -/
theorem peak_heads {D V q k radius potential} (free : QFree D V q)
    (bounds : ∀ x∈V, radius x≤q) (hk : 0<k) {S : Finset ℕ} (ne : S.Nonempty) :
    ∃ x∈S, outN (nextGraph D V q k radius potential) S x ⊆
      (ball D V x (q/k)).erase x := by
  obtain ⟨x,hx,peak⟩ := S.exists_max_image potential ne
  refine ⟨x,hx,?_⟩
  intro y hy
  obtain ⟨ys,edge⟩ := mem_outN.mp hy
  obtain ⟨xv,diff,entry,price⟩ := of_decide_eq_true edge
  obtain ⟨d,_,cap,path⟩ := lift_entry free xv (bounds x xv) diff entry
  have paid := Nat.mul_le_mul_left k cap
  have py := peak y ys
  have bound : d≤q/k := (Nat.le_div_iff_mul_le hk).mpr (by rw [Nat.mul_comm]; omega)
  exact mem_erase.mpr ⟨diff.symm,mem_ball.mpr ⟨ball_subset entry,d,bound,path⟩⟩

/-- In particular a 3-free out-regular input cannot improve its uniform
degree by repricing into cutoff two, even when row radii are chosen freely. -/
theorem triangle_degree_ceiling {D V radius potential s} (free : QFree D V 3)
    (bounds : ∀ x∈V, radius x≤3) (ne : V.Nonempty) (reg : OutEq s D V) :
    ∃ x∈V, (outN (nextGraph D V 3 2 radius potential) V x).card≤s := by
  obtain ⟨x,hx,sub⟩ := peak_heads (potential:=potential) free bounds (by decide : 0<2) ne
  have row : (ball D V x (3/2)).erase x ⊆ outN D V x := by
    intro y hy
    obtain ⟨different,inside⟩ := mem_erase.mp hy
    exact ((mem_ball_one hx).mp inside).resolve_left different
  exact ⟨x,hx,(card_le_card (sub.trans row)).trans (reg x hx).le⟩

/-- A finite chain of strictly decreasing cutoffs, ending in a previously
checked class. All costs are recomputed on each current graph. -/
inductive Closes (n : ℕ) : ℕ → CH.Digraph → Prop where
  | kernels {q D s} (two : 2≤q) (ord : n≤q*s) (deg : CH.MinOutdegreeAtLeast D n s)
      (sparse : ShenRootedKernel.Sparse D (range n)) : Closes n q D
  | exchange {q D} : ShenTransversal.ExchangeTest q D (range n) → Closes n q D
  | seymour {q D U} (three : 3≤q) (sub : U⊆range n)
      (stuck : ¬ShenSeymour.Peels D U) : Closes n q D
  | cover {q D s} (two : 2≤q) (ord : n≤q*s) (deg : CH.MinOutdegreeAtLeast D n s)
      (banks : ShenParentIntersection.ThinCover q D (range n)) : Closes n q D
  | shen {q D s} (pos : 0<s) (cut : 0<q) (window : 2*s-4≤q) (ord : n≤q*s)
      (deg : CH.MinOutdegreeAtLeast D n s) : Closes n q D
  | columns {k D t} (two : 2≤k) (ord : n≤k*t) (deg : CH.MinOutdegreeAtLeast D n t)
      (classified : ∀ U⊆range n, ShenPrimeTransition.Prime D U →
        ShenParentIntersection.Separated D U U →
        U.card≤k+2 ∨ (4≤k ∧ U.card≤k+3) ∨ ShenCircle.Consecutive D U) : Closes n k D
  | pairs {k D t} (two : 2≤k) (ord : n≤k*t) (deg : CH.MinOutdegreeAtLeast D n t) (round : ℕ)
      (classified : ∀ U⊆range n, ShenPrimeTransition.Prime D U →
        ShenParentIntersection.PairClique (ShenParentIntersection.Compatible D (range n) round) U →
        U.card≤k+2 ∨ (4≤k ∧ U.card≤k+3) ∨ ShenCircle.Consecutive D U) : Closes n k D
  | step {q D k radius potential} (down : k<q) (pos : 0<k)
      (bounds : ∀ x∈range n, radius x≤q)
      (child : Closes n k (nextGraph D (range n) q k radius potential)) : Closes n q D

/-- A directly checkable Seymour leaf at any depth of the reach-transition tree. -/
theorem closes_of_dense_bank {D n q} (three : 3≤q) (bank : ShenSeymour.DenseBank D (range n)) :
    Closes n q D := by
  obtain ⟨U,sub,stuck⟩ := ShenSeymour.stuck_of_dense_bank bank
  exact .seymour three sub stuck

theorem Closes.cycle {n q D} (tree : Closes n q D) (hn : 0<n) (loop : CH.Loopless D n) :
    CH.HasDirectedCycleAtMost D n q := by
  induction tree with
  | kernels two ord deg sparse => exact ShenRootedKernel.cycle_of_sparse two ord loop deg sparse
  | exchange test => exact ShenTransversal.cycle_of_exchange loop test
  | seymour three sub stuck => exact ShenSeymour.cycle_of_no_peel three loop sub stuck
  | cover two ord deg banks =>
    exact ShenParentIntersection.cycle_of_thin_cover two hn ord loop deg banks
  | shen pos cut window ord deg =>
    exact ShenFirstStrip.cycle_in_two_strip_window pos cut window hn ord loop deg
  | columns two ord deg classified =>
    exact ShenParentIntersection.cycle_of_separated_classes two hn ord loop deg classified
  | pairs two ord deg round classified =>
    exact ShenParentIntersection.cycle_of_pair_round two hn ord loop deg round classified
  | step down pos bounds child ih =>
    exact pullback loop bounds pos (ih (next_loopless _ _ _ _ _ _))

#print axioms next_free
#print axioms pullback
#print axioms peak_heads
#print axioms triangle_degree_ceiling
#print axioms Closes.cycle
end LeanCH.BR.ShenReachTransition
