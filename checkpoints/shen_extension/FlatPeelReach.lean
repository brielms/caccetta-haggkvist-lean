import checkpoints.shen_extension.ForwardMerge
import LeanCH.BR.BRWeightedStrictAtomFloor

namespace LeanCH.BR.Closure.FlatPeelReach
open Finset BRq2 BRq3 BR45 BRsub WeightedSD ForwardMerge

/-- The labels whose entire forward ball is retained. -/
noncomputable def interior (D : CH.Digraph) (V U : Finset ℕ) (k : ℕ) :=
  V.filter (fun i=>ball D V i k⊆U)

private theorem next {D : CH.Digraph} {V U : Finset ℕ} {i k} (iv : i∈V) :
    ball D V i (k+1)⊆U ↔ ball D V i k⊆U ∧ ∀j∈outN D V i,ball D V j k⊆U := by
  constructor
  · intro yes
    refine ⟨(ball_mono_radius (Nat.le_succ k)).trans yes,?_⟩
    intro j jh t th
    obtain ⟨tv,l,bound,path⟩ := mem_ball.mp th
    have ed := mem_outN.mp jh
    exact yes (mem_ball.mpr ⟨tv,l+1,by omega,.step ed.1 ed.2 path⟩)
  · rintro ⟨old,heads⟩ t th
    obtain ⟨tv,l,bound,path⟩ := mem_ball.mp th
    cases path with
    | refl => exact old (self_mem_ball iv)
    | step jv ed tail => exact heads _ (mem_outN.mpr ⟨jv,ed⟩) (mem_ball.mpr ⟨tv,_,by omega,tail⟩)

private theorem retained {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ} {w : ℕ→ℚ} {i : ℕ}
    (ss : S⊆V) (old : mass V w≤WeightedSD.row q D V w i) :
    outN D V i⊆S → mass V w≤WeightedSD.row q D S w i := by
  intro closed
  have same : outN D S i=outN D V i := by
    ext j
    simp only [mem_outN]
    exact ⟨fun h=>⟨ss h.1,h.2⟩,fun h=>⟨closed (mem_outN.mpr h),h.2⟩⟩
  simpa only [WeightedSD.row,outW_eq_mass,same] using old

private theorem retained_iff {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ} {w : ℕ→ℚ} {c : ℚ}
    (ss : S⊆V) (pos : ∀v∈V,0≤w v) (high : mass V w<c)
    (big : ∀v∈V,c-mass V w<(q:ℚ)*w v) {i : ℕ} (flat : WeightedSD.row q D V w i=c) :
    mass V w≤WeightedSD.row q D S w i ↔ outN D V i⊆S := by
  refine ⟨?_,retained ss (flat ▸ high.le)⟩
  intro enough j jh
  by_contra no
  have hj := mem_outN.mp jh
  have belongs : j∈outN D (V\S) i := mem_outN.mpr ⟨mem_sdiff.mpr ⟨hj.1,no⟩,hj.2⟩
  have lost : w j≤outW D (V\S) w i := by
    rw [outW_eq_mass]
    exact single_le_sum (fun v hv=>pos v (mem_sdiff.mp (mem_outN.mp hv).1).1) belongs
  rw [WeightedSD.row,outW_split ss,mul_add] at flat
  unfold WeightedSD.row at enough
  linarith only [big j hj.1,mul_le_mul_of_nonneg_left lost (Nat.cast_nonneg (α:=ℚ) q),flat,enough]

private theorem zero {D : CH.Digraph} {V U : Finset ℕ} (us : U⊆V) : interior D V U 0=U := by
  ext i
  constructor
  · intro h
    obtain ⟨iv,k⟩ := mem_filter.mp h
    exact k (self_mem_ball iv)
  · intro iu
    exact mem_filter.mpr ⟨us iu,fun j jh=>(eq_of_mem_ball_zero jh).symm ▸ iu⟩

/-- All radii, all deleted sets, both graph orientations by instantiation. -/
theorem exact_rounds {q : ℕ} {D : CH.Digraph} {V U : Finset ℕ} (hq : 2≤q)
    (free : QFree D V q) (small : SmallerSmallRow q V.card) (us : U⊆V)
    {w : ℕ→ℚ} (pos : ∀v∈V,0≤w v) {c : ℚ} (high : mass V w<c)
    (flat : ∀i∈V,WeightedSD.row q D V w i=c) (k : ℕ) :
    rounds q D V w U k=interior D V U k := by
  have bound := strict_atom_floor_of_proper hq free (fun S ss ne=>small.induced free S ss ne)
    w pos c high (fun i iv=>(flat i iv).ge)
  have atom (v) (vv : v∈V) : c-mass V w<(q:ℚ)*w v := by nlinarith only [bound v vv,pos v vv]
  induction k with
  | zero => exact (zero us).symm
  | succ k ih =>
    rw [rounds,ih]; ext i
    change (i∈(interior D V U k).filter _) ↔ i∈V.filter _
    simp only [mem_filter]
    constructor
    · rintro ⟨old,paid⟩
      obtain ⟨iv,kept⟩ := mem_filter.mp old
      have heads := (retained_iff (filter_subset _ _) pos high atom (flat i iv)).mp paid
      exact ⟨iv,(next iv).mpr ⟨kept,fun j jh=>(mem_filter.mp (heads jh)).2⟩⟩
    · rintro ⟨iv,all⟩
      obtain ⟨kept,heads⟩ := (next iv).mp all
      exact ⟨mem_filter.mpr ⟨iv,kept⟩,(retained_iff (filter_subset _ _) pos high atom (flat i iv)).mpr
        (fun j jh=>mem_filter.mpr ⟨(mem_outN.mp jh).1,heads j jh⟩)⟩

/-- Every strict weighting pays every row protected by its whole forward ball.
    Weights with unequal row surpluses can preserve additional rows. -/
theorem survives {q : ℕ} {D : CH.Digraph} {V U : Finset ℕ} (us : U⊆V)
    {w : ℕ→ℚ} (paid : ∀i∈V,mass V w≤WeightedSD.row q D V w i) (k : ℕ) :
    interior D V U k⊆rounds q D V w U k := by
  induction k with
  | zero => rw [zero us]; exact Subset.rfl
  | succ k ih =>
    intro i iv
    obtain ⟨iv,all⟩ := mem_filter.mp iv
    obtain ⟨old,heads⟩ := (next iv).mp all
    apply mem_filter.mpr
    refine ⟨ih (mem_filter.mpr ⟨iv,old⟩),?_⟩
    have sub : ∀l,rounds q D V w U l⊆V := by
      intro l; induction l with
      | zero => exact us
      | succ l prev => exact (filter_subset _ _).trans prev
    exact retained (sub k) (paid i iv) (fun j jh=>ih (mem_filter.mpr ⟨(mem_outN.mp jh).1,heads j jh⟩))

/-- Non-flat positive strict laws still impose the strict geometric budget. -/
theorem budget {q : ℕ} {D : CH.Digraph} {V U : Finset ℕ} (hq : 2≤q)
    (free : QFree D V q) (small : SmallerSmallRow q V.card) (us : U⊆V) (room : U.card+1<V.card)
    (live : U.Nonempty) {w : ℕ→ℚ} (pos : ∀v∈V,0<w v)
    (strict : ∀i∈V,mass V w<WeightedSD.row q D V w i) :
    (q:ℚ)*mass (interior D V U (q-1)) w<mass U w := by
  have sub : ∀l,rounds q D V w U l⊆V := by
    intro l; induction l with
    | zero => exact us
    | succ l prev => exact (filter_subset _ _).trans prev
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
    (mass_mono (survives us (fun i iv=>(strict i iv).le) _)
      (fun i ii=>(pos i (sub _ ii)).le)) (Nat.cast_nonneg q))
    (decay hq free small us room live w pos strict)

private theorem mix_mass (S : Finset ℕ) (x z : ℕ→ℚ) (t : ℚ) :
    mass S (fun i=>x i+t*z i)=mass S x+t*mass S z := by
  simp [mass,sum_add_distrib,mul_sum]

private theorem mix_row (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (x z : ℕ→ℚ) (t : ℚ) (i : ℕ) :
    WeightedSD.row q D V (fun j=>x j+t*z j) i=WeightedSD.row q D V x i+t*WeightedSD.row q D V z i := by
  simp only [WeightedSD.row,outW_eq_mass,mix_mass]; ring

/-- The geometric inequality holds on every nonnegative weak direction of
    the strict source cone, including a direction with zero coordinates. -/
theorem weak_budget {q : ℕ} {D : CH.Digraph} {V U : Finset ℕ} (hq : 2≤q)
    (free : QFree D V q) (small : SmallerSmallRow q V.card) (bad : ¬SmallRow q D V)
    (us : U⊆V) (room : U.card+1<V.card) (live : U.Nonempty)
    {z : ℕ→ℚ} (pos : ∀i∈V,0≤z i) (paid : ∀i∈V,mass V z≤WeightedSD.row q D V z i) :
    (q:ℚ)*mass (interior D V U (q-1)) z≤mass U z := by
  obtain ⟨x,nn,_,strict⟩ := strict_witness_of_not_smallRow bad
  have xp := strict_positive_of_proper_smallRow (fun S ss ne=>small.induced free S ss ne) x nn strict
  let R := interior D V U (q-1)
  let gap (v : ℕ→ℚ) := mass U v-(q:ℚ)*mass R v
  have base : 0<gap x := sub_pos.mpr (budget hq free small us room live xp strict)
  by_contra! violation
  have neg : 0 < -gap z := by change 0 < -(mass U z-(q:ℚ)*mass R z); linarith only [violation]
  let t := gap x/(-gap z)
  have tp : 0<t := div_pos base neg
  let w := fun i=>x i+t*z i
  have positive (i) (iv : i∈V) : 0<w i := add_pos_of_pos_of_nonneg (xp i iv) (mul_nonneg tp.le (pos i iv))
  have rows (i) (iv : i∈V) : mass V w<WeightedSD.row q D V w i := by
    dsimp only [w]; rw [mix_mass,mix_row]
    exact add_lt_add_of_lt_of_le (strict i iv) (mul_le_mul_of_nonneg_left (paid i iv) tp.le)
  have result : 0<gap x+t*gap z := by
    have h := budget hq free small us room live positive rows
    dsimp only [w] at h; rw [mix_mass,mix_mass] at h
    dsimp only [gap,R]; linarith only [h]
  have cancel : t*(-gap z)=gap x := div_mul_cancel₀ _ neg.ne'
  linarith only [result,cancel]

/-- For a tail b and head a, deleting a cannot influence a head of a
    by time q-1. Deleting b cannot influence that head before time q-1. -/
theorem head_geometry {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (hq : 2≤q) (free : QFree D V q)
    {b a : V} (ba : D b a=true) {h : ℕ} (hh : h∈outN D V a) :
    h∈interior D V (V.erase b.val) (q-2) ∧
    (h∈interior D V ((V.erase a.val).erase b.val) (q-1) ↔ b.val∉ball D V h (q-1)) := by
  obtain ⟨hv,ah⟩ := mem_outN.mp hh
  have na : a.val∉ball D V h (q-1) := by
    rintro hit; obtain ⟨_,k,bound,path⟩ := mem_ball.mp hit
    exact free a (k+1) (by omega) (by omega) (.step hv ah path)
  have nb : b.val∉ball D V h (q-2) := by
    rintro hit; obtain ⟨_,k,bound,path⟩ := mem_ball.mp hit
    exact free b (k+1+1) (by omega) (by omega) (.step a.property ba (.step hv ah path))
  refine ⟨mem_filter.mpr ⟨hv,fun j hit=>mem_erase.mpr ⟨fun e=>nb (e ▸ hit),ball_subset hit⟩⟩,?_⟩
  constructor
  · intro inside hit
    exact (mem_erase.mp ((mem_filter.mp inside).2 hit)).1 rfl
  · intro no
    exact mem_filter.mpr ⟨hv,fun j hit=>mem_erase.mpr
      ⟨fun e=>no (e ▸ hit),mem_erase.mpr ⟨fun e=>na (e ▸ hit),ball_subset hit⟩⟩⟩

#print axioms weak_budget
#print axioms head_geometry

#print axioms exact_rounds
#print axioms budget
end LeanCH.BR.Closure.FlatPeelReach
