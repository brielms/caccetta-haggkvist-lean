import checkpoints.shen_extension.LateTargetReach
import checkpoints.shen_extension.ReturnSponsorMass
import checkpoints.shen_extension.MissedFreshCut
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace LeanCH.BR.Closure.ReturnTargetReach
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity TwoParentReturnPivot ReturnSponsorMass

/-- The target and its certified count at a particular distance from x. -/
def Count (D : CH.Digraph) (V : Finset ℕ) (x r : ℕ) (T : Finset ℕ) (k : ℕ) : Prop :=
  k≤(T∩ball D V x r).card

/-- Transport multiple rows at once, counting each new target no more than its
actual number of incoming arcs from the reached rows. -/
theorem step {D V x r T Z E k d m} (start : Count D V x r T k) (zv : Z⊆V)
    (need : ∀a∈T∩ball D V x r,E.card+d≤(outN D (Z∪E) a).card)
    (overlap : ∀h∈Z∩ball D V x (r+1),(inN D (T∩ball D V x r) h).card≤m) :
    k*d≤(Z∩ball D V x (r+1)).card*m := by
  let A := T∩ball D V x r
  let B := Z∩ball D V x (r+1)
  have low (a) (ha : a∈A) : d≤(outN D B a).card := by
    have sub : outN D (Z∪E) a⊆outN D B a∪E := by
      intro h hh
      obtain ⟨menu,arc⟩ := mem_outN.mp hh
      rcases mem_union.mp menu with hz|he
      · exact mem_union_left _ (mem_outN.mpr ⟨mem_inter.mpr ⟨hz,ball_step (mem_inter.mp ha).2 (zv hz) arc⟩,arc⟩)
      · exact mem_union_right _ he
    have cnt := (card_le_card sub).trans (card_union_le _ _)
    have due := need a ha
    omega
  have sums : (∑a∈A,(outN D B a).card)=∑h∈B,(inN D A h).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun i j=>D i j=true)
  calc
    k*d≤A.card*d := Nat.mul_le_mul_right d start
    _ ≤ ∑a∈A,(outN D B a).card := by simpa using (sum_le_sum low)
    _ = ∑h∈B,(inN D A h).card := sums
    _ ≤ B.card*m := by simpa using (sum_le_sum (s:=B) overlap)

/-- A schedule of actual row quotas can be replayed to any finite depth. The
overlap hypotheses concern only the reached rows at each stage. -/
def Replay (D : CH.Digraph) (V : Finset ℕ) (x r : ℕ) (T : Finset ℕ) (k : ℕ) : Prop :=
  ∀(N : ℕ) (targets exceptions : ℕ→Finset ℕ) (counts quota overlap : ℕ→ℕ),
    targets 0=T → counts 0=k →
    (∀j<N,targets (j+1)⊆V) →
    (∀j<N,∀a∈targets j∩ball D V x (r+j),
      (exceptions j).card+quota j≤(outN D (targets (j+1)∪exceptions j) a).card) →
    (∀j<N,∀h∈targets (j+1)∩ball D V x (r+j+1),
      (inN D (targets j∩ball D V x (r+j)) h).card≤overlap j) →
    (∀j<N,∀z<counts (j+1),z*overlap j<counts j*quota j) →
    ∀j≤N,Count D V x (r+j) (targets j) (counts j)

theorem replay {D V x r T k} (start : Count D V x r T k) : Replay D V x r T k := by
  intro N targets ex counts quota overlap t0 k0 sub due sharing round j
  induction j with
  | zero => intro _; simpa [t0,k0] using start
  | succ j ih =>
    intro le
    have lt : j<N := by omega
    have moved := step (ih (by omega)) (sub j lt) (due j lt) (sharing j lt)
    change counts (j+1)≤(targets (j+1)∩ball D V x (r+j+1)).card
    by_contra! low
    exact (Nat.not_lt_of_le moved) (round j lt _ low)

/-- From the named neutral second neighbour, every possible continuation
still has q distinct next heads. Each avoids short returns to the sponsor. -/
def March (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (x r p z : ℕ) : Prop :=
  ∀j,j+3≤q →
    (∃v∈V,Walk D V z v j) ∧
    ∀v∈V,Walk D V z v j →
      q≤(outN D V v).card ∧
      outN D V v⊆(V.filter (fun h=>p∉ball D V h (q-(j+3))))∩ball D V x (r+(j+3))

theorem march {q D V x r p z} (free : QFree D V q) (positive : 0<q)
    (degree : ∀v∈V,q≤(outN D V v).card) (xp : p∈ball D V x r)
    (zv : z∈V) (prefixPath : Walk D V p z 2) : March q D V x r p z := by
  intro j room
  have runs (k : ℕ) : ∃v∈V,Walk D V z v k := by
    induction k with
    | zero => exact ⟨z,zv,.refl _⟩
    | succ k ih =>
      obtain ⟨v,hv,path⟩ := ih
      obtain ⟨h,hh⟩ := card_pos.mp (positive.trans_le (degree v hv))
      obtain ⟨inside,arc⟩ := mem_outN.mp hh
      exact ⟨h,inside,path.snoc inside arc⟩
  refine ⟨runs j,?_⟩
  intro v hv path
  refine ⟨degree v hv,?_⟩
  intro h hh
  obtain ⟨inside,arc⟩ := mem_outN.mp hh
  have ph := (prefixPath.append path).snoc inside arc
  have avoid : p∉ball D V h (q-(j+3)) := by
    intro back
    obtain ⟨_,d,short,hp⟩ := mem_ball.mp back
    exact free p _ (by omega) (by omega) (ph.append hp)
  obtain ⟨_,k,short,first⟩ := mem_ball.mp xp
  exact mem_inter.mpr ⟨mem_filter.mpr ⟨inside,avoid⟩,mem_ball.mpr ⟨inside,_,by omega,first.append ph⟩⟩

def Outcome (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (b p t y : ℕ) : Prop :=
    let U := V.erase b
    let B := bank q D U t y
    let S := B.filter (fun h=>D p h=true)
    let Z := outN D V t∩neutral D V p
    (∃h∈outN D U p,h∈outN D U t \ B) ∨
      ∀x r,p∈ball D V x r →
        Count D V x (r+2) Z (q-S.card) ∧ Replay D V x (r+2) Z (q-S.card) ∧
          (S.card<q → ∃z∈Z,March q D V x r p z)

/-- Instantiate the mined rule at the named return in the native repair. In
the second case every ancestor receives the target set, its count, and the
finite replay rule with that count already supplied. -/
theorem native {q n b p t y w c} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (bv : b∈X.V) (pv : p∈X.V) (tr : t∈region q X.D X.V b) (pt : X.D p t=true)
    (high : 1<c) (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c)
    (diffuse : ∀i∈X.V,(q:ℚ)^2*w i≤1) :
    Outcome q X.D X.V b p t y := by
  classical
  unfold Outcome
  intro U B S Z
  by_cases kept : ∃h∈outN X.D U p,h∈outN X.D U t \ B
  · exact Or.inl kept
  right
  have tv : t∈X.V := BRsub.ballSet_subset tr
  have tb := ((saturated_region (by omega : 2≤q) X.free X.sat bv tv).mp tr).2
  obtain ⟨cover,dis⟩ := partition hq X.free pv tv pt tb kept
  change outN X.D X.V t=Z∪S at cover
  have same : outN X.D (Z∪S) t=outN X.D X.V t := by
    ext h
    simp only [mem_outN,←cover]
    simp
  have deg := MissedFreshCut.native_degree (by omega : 2≤q) high rows diffuse tv
  have exactCard : (outN X.D X.V t).card=Z.card+S.card := by rw [cover,card_union_of_disjoint dis]
  have zv : Z⊆X.V := fun h hz=>outN_subset (mem_inter.mp hz).1
  have no : t∉Z := fun h=> Bool.noConfusion (((mem_filter.mp (mem_inter.mp h).2).2.1).symm.trans pt)
  intro x r xp
  have path := ball_step xp tv pt
  have count : Count X.D X.V x (r+2) Z (q-S.card) := by
    by_cases large : q≤S.card
    · simp [Count,Nat.sub_eq_zero_of_le large]
    have need : S.card+(q-S.card)≤(outN X.D (Z∪S) t).card := by rw [same]; omega
    exact (SATBoundaryPilot.late_target (A:={t}) (T:=Z) (E:=S) path
      (mem_union_left _ (mem_singleton_self t)) zv (by intro a ha; obtain rfl:=mem_singleton.mp ha; exact need)).resolve_left no
  refine ⟨count,replay count,?_⟩
  intro smallBank
  have bound : q-S.card≤(Z∩ball X.D X.V x (r+2)).card := count
  obtain ⟨z,hz⟩ := card_pos.mp ((Nat.sub_pos_of_lt smallBank).trans_le bound)
  have zin := (mem_inter.mp hz).1
  obtain ⟨zv,tz⟩ := mem_outN.mp (mem_inter.mp zin).1
  exact ⟨z,zin,march X.free (by omega) (fun _ hv=>MissedFreshCut.native_degree (by omega : 2≤q) high rows diffuse hv)
    xp zv (.step tv pt (.step zv tz (.refl _)))⟩

/-- Run the return transition at the sponsor itself. A positive first quota
gives q distinct targets at each subsequent admissible radius. -/
theorem at_parent {q D V b p t y} (pv : p∈V) (outcome : Outcome q D V b p t y) :
    let U := V.erase b
    let B := bank q D U t y
    let S := B.filter (fun h=>D p h=true)
    let Z := outN D V t∩neutral D V p
    (∃h∈outN D U p,h∈outN D U t \ B) ∨
      Count D V p 2 Z (q-S.card) ∧
      (S.card<q → ∀j,j+3≤q →
        Count D V p (j+3) (V.filter (fun h=>p∉ball D V h (q-(j+3)))) q) := by
  intro U B S Z
  unfold Outcome at outcome
  rcases outcome with kept|follow
  · exact Or.inl kept
  obtain ⟨count,_,next⟩ := follow p 0 (self_mem_ball pv)
  refine Or.inr ⟨count,?_⟩
  intro low j room
  obtain ⟨z,_,run⟩ := next low
  obtain ⟨⟨v,inside,path⟩,allRows⟩ := run j room
  obtain ⟨many,targets⟩ := allRows v inside path
  simpa [Count] using many.trans (card_le_card targets)

#print axioms at_parent

def OnModel {q n} (X : ShortestCycleWeights.Model q n) : Prop :=
  ∀{b p t y : ℕ} {w : ℕ→ℚ} {c : ℚ}, b∈X.V → p∈X.V → t∈region q X.D X.V b →
    X.D p t=true → 1<c → (∀i∈X.V,WeightedSD.row q X.D X.V w i=c) →
    (∀i∈X.V,(q:ℚ)^2*w i≤1) → Outcome q X.D X.V b p t y

theorem on_model {q n} (X : ShortestCycleWeights.Model q n) (hq : 3≤q) : OnModel X :=
  fun bv pv tr pt high rows diffuse=>native X hq bv pv tr pt high rows diffuse

#print axioms on_model
#print axioms march
#print axioms step
#print axioms replay
#print axioms native
end LeanCH.BR.Closure.ReturnTargetReach
