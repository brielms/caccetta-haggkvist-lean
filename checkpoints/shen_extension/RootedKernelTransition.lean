import checkpoints.shen_extension.ParentIntersection
import checkpoints.shen_extension.TerminalTransport

/-! Rooted minimum boundaries, following Hamidoune, arXiv:0909.5664,
Lemmas 1–4. Integer vertex masses and the unmatched kernel arcs are retained. -/
namespace LeanCH.BR.ShenRootedKernel
open BRq2 BRq3 Finset ShenReturnCut ShenPrimeTransition
open Classical

abbrev wt (w : ℕ → ℕ) (A : Finset ℕ) := ∑ x∈A, w x

private theorem mono {w : ℕ → ℕ} {A B : Finset ℕ} (sub : A⊆B) : wt w A≤wt w B :=
  sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)

def Rooted (D : CH.Digraph) (V : Finset ℕ) (v : ℕ) (S : Finset ℕ) : Prop :=
  S⊆V ∧ v∈S ∧ ∀ x∈S, D x v≠true

structure Kernel (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℕ) (v : ℕ) (S : Finset ℕ) : Prop where
  rooted : Rooted D V v S
  low : ∀ A, Rooted D V v A → wt w (boundary D V S)≤wt w (boundary D V A)
  small : ∀ A, Rooted D V v A → wt w (boundary D V A)=wt w (boundary D V S) → S.card≤A.card

theorem exists_kernel {D V} (w : ℕ → ℕ) {v : ℕ} (hv : v∈V) (loop : D v v≠true) :
    ∃ S, Kernel D V w v S := by
  let C := V.powerset.filter (Rooted D V v)
  have mem (A) : A∈C ↔ Rooted D V v A :=
    ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨mem_powerset.mpr h.1,h⟩⟩
  have non : C.Nonempty := ⟨{v},(mem _).mpr ⟨by simpa using hv,by simp,by simpa using loop⟩⟩
  let cost := fun S => wt w (boundary D V S)
  obtain ⟨A,a,minA⟩ := C.exists_min_image cost non
  let M := C.filter (fun S => cost S=cost A)
  obtain ⟨S,s,minS⟩ := M.exists_min_image Finset.card ⟨A,mem_filter.mpr ⟨a,rfl⟩⟩
  obtain ⟨inC,eq⟩ := mem_filter.mp s
  exact ⟨S,(mem S).mp inC,fun B hb => eq.le.trans (minA B ((mem B).mpr hb)),
    fun B hb h => minS B (mem_filter.mpr ⟨(mem B).mpr hb,h.trans eq⟩)⟩

private theorem closed_mem {D V A x} : x∈closedRows D V A ↔ x∈A ∨ ∃ y∈A, x∈outN D V y := by
  simp [closedRows,ShenReturnCut.image]

private theorem increment (D V w A) :
    wt w (boundary D V A)+wt w A=wt w (closedRows D V A) := by
  have h : A⊆closedRows D V A := subset_union_left
  have eq : closedRows D V A \ A=boundary D V A := by
    ext; simp [closedRows,boundary]; tauto
  simpa only [eq] using sum_sdiff (f:=w) h

theorem submod (D V w A B) :
    wt w (boundary D V (A∩B))+wt w (boundary D V (A∪B)) ≤
    wt w (boundary D V A)+wt w (boundary D V B) := by
  have hu : closedRows D V (A∪B) = closedRows D V A ∪ closedRows D V B := by
    unfold closedRows ShenReturnCut.image
    rw [union_biUnion]
    ext z; simp only [mem_union]; tauto
  have hi : closedRows D V (A∩B) ⊆ closedRows D V A ∩ closedRows D V B := by
    intro z hz
    rcases closed_mem.mp hz with h|⟨y,hy,e⟩
    · exact mem_inter.mpr ⟨closed_mem.mpr (.inl (mem_inter.mp h).1),closed_mem.mpr (.inl (mem_inter.mp h).2)⟩
    · exact mem_inter.mpr ⟨closed_mem.mpr (.inr ⟨y,(mem_inter.mp hy).1,e⟩),
        closed_mem.mpr (.inr ⟨y,(mem_inter.mp hy).2,e⟩)⟩
  have h₁ := increment D V w (A∩B)
  have h₂ := increment D V w (A∪B)
  rw [hu] at h₂
  have h₃ := increment D V w A
  have h₄ := increment D V w B
  have h₅ := mono (w:=w) hi
  have h₆ : wt w (A∪B) + wt w (A∩B) = wt w A + wt w B := sum_union_inter
  have h₇ : wt w (closedRows D V A ∪ closedRows D V B) + wt w (closedRows D V A ∩ closedRows D V B) =
      wt w (closedRows D V A) + wt w (closedRows D V B) := sum_union_inter
  unfold wt at *
  omega

/-- An internal kernel arc either returns to its source through the target
kernel's boundary, or enters a strictly smaller kernel. -/
theorem nested_or_boundary {D V w x y A B} (ka : Kernel D V w x A) (kb : Kernel D V w y B)
    (ya : y∈A) (xy : D x y=true) : B ⊂ A ∨ x∈boundary D V B := by
  have xb : x∉B := fun h => kb.rooted.2.2 x h xy
  by_cases paid : x∈boundary D V B
  · exact Or.inr paid
  left
  have unionR : Rooted D V x (A∪B) := by
    refine ⟨union_subset ka.rooted.1 kb.rooted.1,mem_union_left _ ka.rooted.2.1,?_⟩
    intro z hz zx
    rcases mem_union.mp hz with a|b
    · exact ka.rooted.2.2 z a zx
    · exact paid (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨z,b,mem_outN.mpr ⟨ka.rooted.1 ka.rooted.2.1,zx⟩⟩,xb⟩)
  have interR : Rooted D V y (A∩B) :=
    ⟨inter_subset_right.trans kb.rooted.1,mem_inter.mpr ⟨ya,kb.rooted.2.1⟩,
      fun z hz => kb.rooted.2.2 z (mem_inter.mp hz).2⟩
  have sub := submod D V w A B
  have l := ka.low _ unionR
  have r := kb.low _ interR
  have card := kb.small _ interR (by omega)
  have eq := eq_of_subset_of_card_le (inter_subset_right : A∩B⊆B) card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨eq ▸ inter_subset_left,fun h => xb (h ▸ ka.rooted.2.1)⟩

theorem ball_budget {q D V w v S} (free : QFree D V q) (hq : 0<q) (K : Kernel D V w v S) :
    w v + wt w (outN D V v) + (q-1)*wt w (boundary D V S) ≤ wt w V := by
  have vv := K.rooted.1 K.rooted.2.1
  have first : ball D V v 1 = insert v (outN D V v) := by ext y; simp [mem_ball_one vv]
  have outside : v∉outN D V v := fun h => loopfree free hq vv (mem_outN.mp h).2
  have grow (k : ℕ) (cap : k+1≤q) :
      wt w (ball D V v k)+wt w (boundary D V S)≤wt w (ball D V v (k+1)) := by
    have rooted : Rooted D V v (ball D V v k) :=
      ⟨ball_subset,self_mem_ball vv,fun _ hy => no_back_arc free vv hy cap⟩
    have step : closedRows D V (ball D V v k) ⊆ ball D V v (k+1) := by
      intro z hz
      rcases closed_mem.mp hz with h|⟨y,hy,e⟩
      · exact ball_mono_radius (by omega : k≤k+1) h
      · exact ball_step hy (mem_outN.mp e).1 (mem_outN.mp e).2
    have b := K.low _ rooted
    have inc := increment D V w (ball D V v k)
    have := mono (w:=w) step
    omega
  have iter (j : ℕ) (cap : j+1≤q) :
      w v + wt w (outN D V v) + j*wt w (boundary D V S) ≤ wt w (ball D V v (j+1)) := by
    induction j with
    | zero => simp [first,wt,sum_insert outside]
    | succ j ih =>
      have pre := ih (by omega)
      have next := grow (j+1) cap
      rw [Nat.succ_mul]; omega
  exact (iter (q-1) (by omega)).trans (mono ball_subset)

def Internal (D : CH.Digraph) (K : ℕ → Finset ℕ) (x y : ℕ) : Prop :=
  D x y=true ∧ y∈K x

def Paid (D : CH.Digraph) (V : Finset ℕ) (K : ℕ → Finset ℕ) (x y : ℕ) : Prop :=
  Internal D K x y ∧ x∈boundary D V (K y)

noncomputable def load (V : Finset ℕ) (w : ℕ → ℕ) (P : ℕ → ℕ → Prop) (x : ℕ) :=
  ∑ y∈V, if P x y then w y else 0

theorem root_charge {D V w K} (kernels : ∀ x∈V, Kernel D V w x (K x)) {x} (hx : x∈V) :
    wt w (outN D V x) + load V w (fun a b => Paid D V K b a) x ≤
    wt w (boundary D V (K x)) + load V w (Internal D K) x := by
  let B := boundary D V (K x)
  have sub : B ⊆ V := by
    intro y hy
    obtain ⟨_,_,out⟩ := mem_biUnion.mp (mem_sdiff.mp hy).1
    exact (mem_outN.mp out).1
  have recB : V.filter (fun y => y∈B)=B :=
    Finset.ext (fun y => ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨sub h,h⟩⟩)
  change _ ≤ wt w B + _
  conv_rhs => lhs; rw [←recB]
  simp only [load,wt,outN,sum_filter,←sum_add_distrib]
  apply sum_le_sum
  intro y hy
  by_cases p : Paid D V K y x
  · have no := (kernels y hy).rooted.2.2 x p.1.2
    simp [p,no,show y∈B from p.2]
  · by_cases e : D x y=true
    · by_cases yk : y∈K x
      · simp [e,p,Internal,yk]
      · have hit : y∈B := mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨x,(kernels x hx).rooted.2.1,
          mem_outN.mpr ⟨hy,e⟩⟩,yk⟩
        simp [p,e,hit]
    · simp [p,e]

/-- The margin in each strict row forces a net excess of internal outgoing
weight over returned incoming weight on the same vertex. -/
theorem row_excess {q D V w K} (hq : 2≤q) (free : QFree D V q) (strict : Strict q D V w)
    (kernels : ∀ x∈V, Kernel D V w x (K x)) {x} (hx : x∈V) :
    load V w (fun a b => Paid D V K b a) x < load V w (Internal D K) x := by
  have budget := ball_budget free (by omega : 0<q) (kernels x hx)
  have high := nat_strict.mp strict x hx
  change wt w V < w x + q * (∑ y∈V, if D x y=true then w y else 0) at high
  rw [show (∑ y∈V, if D x y=true then w y else 0)=wt w (outN D V x) by simp [wt,outN,sum_filter]] at high
  have bound : wt w (boundary D V (K x)) < wt w (outN D V x) := by
    by_contra! small
    have le := Nat.mul_le_mul_left (q-1) small
    have eq := congrArg (fun k => k * wt w (outN D V x)) (show q=q-1+1 by omega)
    simp only [Nat.add_mul,Nat.one_mul] at eq
    omega
  have bill := root_charge kernels hx
  omega

noncomputable def flow (V : Finset ℕ) (w : ℕ → ℕ) (P : ℕ → ℕ → Prop) :=
  ∑ x∈V, w x * load V w P x

private theorem flow_reverse (V w P) : flow V w (fun a b => P b a) = flow V w P := by
  unfold flow load
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  by_cases hit : P x y <;> simp [hit,Nat.mul_comm]

def Descends (D : CH.Digraph) (K : ℕ → Finset ℕ) (x y : ℕ) : Prop :=
  Internal D K x y ∧ K y ⊂ K x

def Unpaid (D : CH.Digraph) (V : Finset ℕ) (K : ℕ → Finset ℕ) (x y : ℕ) : Prop :=
  Internal D K x y ∧ x∉boundary D V (K y)

private theorem partition_flow (D V K w S) :
    flow S w (Internal D K) = flow S w (Paid D V K) + flow S w (Unpaid D V K) := by
  unfold flow
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro x _
  rw [←Nat.mul_add]
  congr 1
  unfold load
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro y _
  by_cases hit : Internal D K x y <;> by_cases back : x∈boundary D V (K y) <;>
    simp [Paid,Unpaid,hit,back]

/-- The original strict surplus, before rounding to integers. The same
factor q-1 is used at every vertex, allowing paid arcs to cancel exactly. -/
theorem margin_bill {q D V w K} (hq : 2≤q) (free : QFree D V q) (strict : Strict q D V w)
    (kernels : ∀ x∈V, Kernel D V w x (K x)) :
    (∑ x∈V, w x * (score q D V w x - wt w V)) ≤ (q-1)*flow V w (Unpaid D V K) := by
  let c := q-1
  have row (x) (hx : x∈V) :
      (score q D V w x - wt w V) + c*load V w (fun a b => Paid D V K b a) x ≤
        c*load V w (Internal D K) x := by
    have high := nat_strict.mp strict x hx
    have budget := ball_budget free (by omega : 0<q) (kernels x hx)
    have pay := Nat.mul_le_mul_left c (root_charge kernels hx)
    have factor := congrArg (fun k => k * wt w (outN D V x)) (show q=c+1 by dsimp [c]; omega)
    have eq : score q D V w x = w x + q*wt w (outN D V x) := by simp [score,wt,outN,sum_filter]
    change wt w V < _ at high
    change _ + c*_ ≤ _ at budget
    simp only [Nat.mul_add] at pay
    simp only [Nat.add_mul,Nat.one_mul] at factor
    omega
  have weight (x) (hx : x∈V) := Nat.mul_le_mul_left (w x) (row x hx)
  have aggregate := sum_le_sum weight
  simp only [Nat.mul_add,Nat.mul_left_comm (w _) c,sum_add_distrib,←mul_sum] at aggregate
  change _ + c*flow V w (fun a b => Paid D V K b a) ≤ c*flow V w (Internal D K) at aggregate
  rw [flow_reverse,partition_flow D V K w V,Nat.mul_add] at aggregate
  change _ ≤ c*flow V w (Unpaid D V K)
  omega

/-- The entire unit of excess is required again inside every internally
closed family of roots. Arcs entering the family can only strengthen it. -/
theorem closed_pressure {q D V w K S} (hq : 2≤q) (free : QFree D V q)
    (strict : Strict q D V w) (kernels : ∀ x∈V, Kernel D V w x (K x))
    (sub : S⊆V) (closed : ∀ x∈S, ∀ y∈V, Internal D K x y → y∈S) :
    wt w S ≤ flow S w (Unpaid D V K) := by
  have row (x) (hx : x∈S) : load S w (fun a b => Paid D V K b a) x < load S w (Internal D K) x := by
    have lo : load S w (fun a b => Paid D V K b a) x ≤ load V w (fun a b => Paid D V K b a) x :=
      sum_le_sum_of_subset_of_nonneg sub (by intros; exact Nat.zero_le _)
    have eq : load S w (Internal D K) x = load V w (Internal D K) x :=
      sum_subset sub (fun y hy out => ite_eq_right (fun hit => out (closed x hx y hy hit)))
    rw [eq]
    exact lo.trans_lt (row_excess hq free strict kernels (sub hx))
  have agg := sum_le_sum (s:=S) (fun x hx => Nat.mul_le_mul_left (w x) (row x hx))
  change (∑ x∈S, w x*(load S w (fun a b => Paid D V K b a) x + 1)) ≤ _ at agg
  simp only [Nat.mul_add,Nat.mul_one,sum_add_distrib] at agg
  change flow S w (fun a b => Paid D V K b a) + wt w S ≤ flow S w (Internal D K) at agg
  rw [flow_reverse,partition_flow D V K w S] at agg
  omega

theorem descent_mass {q D V w K} (hq : 2≤q) (free : QFree D V q) (strict : Strict q D V w)
    (kernels : ∀ x∈V, Kernel D V w x (K x)) :
    wt w V ≤ flow V w (Descends D K) := by
  have charge := sum_le_sum (s:=V) (fun x hx =>
    Nat.mul_le_mul_left (w x) (row_excess hq free strict kernels hx))
  change (∑ x∈V, w x * (load V w (fun a b => Paid D V K b a) x + 1)) ≤ _ at charge
  simp only [Nat.mul_add,Nat.mul_one,sum_add_distrib] at charge
  change flow V w (fun a b => Paid D V K b a) + wt w V ≤ flow V w (Internal D K) at charge
  rw [flow_reverse] at charge
  have split : flow V w (Internal D K) ≤ flow V w (Paid D V K) + flow V w (Descends D K) := by
    unfold flow
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro x hx
    rw [←Nat.mul_add]
    apply Nat.mul_le_mul_left
    unfold load
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro y hy
    by_cases hit : Internal D K x y
    · rcases nested_or_boundary (kernels x hx) (kernels y hy) hit.2 hit.1 with down|paid
      · simp [hit,show Descends D K x y from ⟨hit,down⟩]
      · simp [hit,show Paid D V K x y from ⟨hit,paid⟩]
    · simp [hit]
  omega

theorem kernel_family {D V} (w : ℕ → ℕ) (loop : ∀ v∈V, D v v≠true) :
    ∃ K : ℕ → Finset ℕ, ∀ x∈V, Kernel D V w x (K x) := by
  let K (x : ℕ) := if hx : x∈V then (exists_kernel w hx (loop x hx)).choose else ∅
  exact ⟨K,fun x hx => by simpa [K,hx] using (exists_kernel w hx (loop x hx)).choose_spec⟩

def Sparse (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∃ K, (∀ x∈V, Kernel D V (fun _ => 1) x (K x)) ∧ flow V (fun _ => 1) (Unpaid D V K)<V.card

theorem cycle_of_sparse {n s q D} (hq : 2≤q) (ord : n≤q*s) (loop : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n s) (sparse : Sparse D (range n)) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  obtain ⟨K,kernels,small⟩ := sparse
  have strict : Strict q D (range n) (fun _ => 1) := by
    apply nat_strict.mpr
    intro x hx
    have lower := Nat.mul_le_mul_left q (Compose.FloorSix.out_card degree (mem_range.mp hx))
    simp [score] at *
    omega
  have size := closed_pressure hq (qfree_of_noShort loop no) strict kernels
    (Finset.Subset.refl _) (fun _ _ _ hy _ => hy)
  exact small.not_ge (by simpa [wt] using size)

/-- A permutation of the labels preserving the host and its induced arcs. -/
structure Symmetry (D : CH.Digraph) (V : Finset ℕ) (e : ℕ ≃ ℕ) : Prop where
  inside : ∀ x, e x∈V ↔ x∈V
  edge : ∀ x∈V, ∀ y∈V, D (e x) (e y)=D x y

theorem Symmetry.inverse {D V e} (a : Symmetry D V e) : Symmetry D V e.symm := by
  refine ⟨fun x => ?_,fun x hx y hy => ?_⟩
  · simpa using (a.inside (e.symm x)).symm
  · have xv := (a.inside (e.symm x)).mp (by simpa using hx)
    have yv := (a.inside (e.symm y)).mp (by simpa using hy)
    simpa using (a.edge _ xv _ yv).symm

theorem Symmetry.rooted_map {D V e} (a : Symmetry D V e) {x S} (h : Rooted D V x S) :
    Rooted D V (e x) (S.map e.toEmbedding) := by
  refine ⟨?_,mem_map.mpr ⟨x,h.2.1,rfl⟩,?_⟩
  · intro y hy
    obtain ⟨z,hz,rfl⟩ := mem_map.mp hy
    exact (a.inside z).mpr (h.1 hz)
  · intro y hy
    obtain ⟨z,hz,rfl⟩ := mem_map.mp hy
    simpa [a.edge z (h.1 hz) x (h.1 h.2.1)] using h.2.2 z hz

private theorem boundary_iff {D V S z} : z∈boundary D V S ↔
    z∈V ∧ z∉S ∧ ∃ y∈S, D y z=true := by
  constructor
  · intro h
    obtain ⟨y,hy,edge⟩ := mem_biUnion.mp (mem_sdiff.mp h).1
    exact ⟨(mem_outN.mp edge).1,(mem_sdiff.mp h).2,y,hy,(mem_outN.mp edge).2⟩
  · rintro ⟨hv,hs,y,hy,edge⟩
    exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨y,hy,mem_outN.mpr ⟨hv,edge⟩⟩,hs⟩

theorem Symmetry.boundary_card {D V e} (a : Symmetry D V e) {S} (sub : S⊆V) :
    (boundary D V (S.map e.toEmbedding)).card = (boundary D V S).card := by
  have eq : boundary D V (S.map e.toEmbedding) = (boundary D V S).map e.toEmbedding := by
    ext z
    obtain ⟨z,rfl⟩ := e.surjective z
    simp only [boundary_iff,mem_map_equiv,e.symm_apply_apply,a.inside]
    constructor
    · rintro ⟨zv,zs,y,hy,edge⟩
      refine ⟨zv,zs,e.symm y,hy,?_⟩
      simpa using (a.edge _ (sub hy) _ zv).symm.trans (by simpa using edge)
    · rintro ⟨zv,zs,u,hu,edge⟩
      exact ⟨zv,zs,e u,by simpa using hu,(a.edge _ (sub hu) _ zv).trans edge⟩
  rw [eq,card_map]

theorem Symmetry.kernel_size {D V e x A B} (a : Symmetry D V e)
    (ka : Kernel D V (fun _ => 1) x A) (kb : Kernel D V (fun _ => 1) (e x) B) :
    A.card=B.card := by
  have ar := a.rooted_map ka.rooted
  have br : Rooted D V x (B.map e.symm.toEmbedding) := by simpa using a.inverse.rooted_map kb.rooted
  have ac := a.boundary_card ka.rooted.1
  have bc := a.inverse.boundary_card kb.rooted.1
  have lo := kb.low _ ar
  have hi := ka.low _ br
  simp [wt,ac,bc] at lo hi
  have aSize := ka.small _ br (by simp [wt,bc]; omega)
  have bSize := kb.small _ ar (by simp [wt,ac]; omega)
  simp only [card_map] at aSize bSize
  omega

def Transitive (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀ x∈V, ∀ y∈V, ∃ e : ℕ ≃ ℕ, Symmetry D V e ∧ e x=y

theorem sparse_of_transitive {D V} (nonempty : V.Nonempty) (loop : ∀ x∈V, D x x≠true)
    (symmetry : Transitive D V) : Sparse D V := by
  obtain ⟨K,hK⟩ := kernel_family _ loop
  have none (x) (hx : x∈V) (y) (hy : y∈V) : ¬Unpaid D V K x y := by
    obtain ⟨e,aut,eq⟩ := symmetry x hx y hy
    intro h
    have size := aut.kernel_size (hK x hx) (eq.symm ▸ hK y hy)
    rw [eq] at size
    have down := (nested_or_boundary (hK x hx) (hK y hy) h.1.2 h.1.1).resolve_right h.2
    exact (card_lt_card down).ne size.symm
  have zero : flow V (fun _ => 1) (Unpaid D V K)=0 :=
    sum_eq_zero (fun x hx => by simp [load,sum_eq_zero (fun y hy => ite_eq_right (none x hx y hy))])
  exact ⟨K,hK,zero ▸ card_pos.mpr nonempty⟩

theorem cycle_of_transitive {n q s D} (hn : 0<n) (hq : 2≤q) (ord : n≤q*s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (symmetry : Transitive D (range n)) : CH.HasDirectedCycleAtMost D n q :=
  cycle_of_sparse hq ord loop degree (sparse_of_transitive ⟨0,mem_range.mpr hn⟩
    (fun x hx => by simp [loop x (mem_range.mp hx)]) symmetry)

#print axioms nested_or_boundary
#print axioms ball_budget
#print axioms descent_mass
#print axioms margin_bill
#print axioms closed_pressure
#print axioms cycle_of_sparse
#print axioms sparse_of_transitive
#print axioms cycle_of_transitive

structure Candidate (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (s : ℕ) : Prop where
  nonempty : V.Nonempty
  order : V.card≤q*s
  degree : ∀ x∈V, s≤(outN D V x).card

/-- Minimize the order of the induced host, allowing its degree parameter
to change at each step while keeping the cutoff and original arcs. -/
structure Terminal (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (s : ℕ) extends Candidate q D V s where
  stop : ∀ B⊆V, ∀ d, Candidate q D B d → V.card≤B.card

theorem terminal_of_candidate {q D V s} (start : Candidate q D V s) :
    ∃ U⊆V, ∃ d, Terminal q D U d := by
  let F := V.powerset.filter (fun U => ∃ d, Candidate q D U d)
  have mem (U) : U∈F ↔ U⊆V ∧ ∃ d, Candidate q D U d := by simp [F]
  obtain ⟨U,hu,minU⟩ := F.exists_min_image Finset.card
    ⟨V,(mem V).mpr ⟨Finset.Subset.refl _,s,start⟩⟩
  obtain ⟨sub,d,src⟩ := (mem U).mp hu
  exact ⟨U,sub,d,src,fun B bu t h => minU B ((mem B).mpr ⟨bu.trans sub,t,h⟩)⟩

theorem punctured_degree {D V w x A} (K : Kernel D V w x A) {s}
    (deg : ∀ v∈V, s≤(outN D V v).card) :
    ∀ y∈A.erase x, s-(boundary D V A).card≤(outN D (A.erase x) y).card := by
  intro y hy
  have ya := mem_of_mem_erase hy
  have sub : outN D V y ⊆ outN D (A.erase x) y ∪ boundary D V A := by
    intro z hz
    obtain ⟨zv,e⟩ := mem_outN.mp hz
    by_cases za : z∈A
    · have ne : z≠x := by rintro rfl; exact K.rooted.2.2 y ya e
      exact mem_union_left _ (mem_outN.mpr ⟨mem_erase.mpr ⟨ne,za⟩,e⟩)
    · exact mem_union_right _ (boundary_iff.mpr ⟨zv,za,y,ya,e⟩)
  have cap := (card_le_card sub).trans (card_union_le _ _)
  have low := deg y (K.rooted.1 ya)
  omega

/-- Every root of a minimum-order induced obstruction supplies an actual
smaller host of positive degree, and its order must strictly exceed the
cutoff times that degree. -/
theorem terminal_kernel_size {q D V s x A} (endpt : Terminal q D V s) (hq : 2≤q)
    (free : QFree D V q) (K : Kernel D V (fun _ => 1) x A) :
    (boundary D V A).card<s ∧ q*(s-(boundary D V A).card)+2≤A.card := by
  have xv := K.rooted.1 K.rooted.2.1
  have b := ball_budget free (by omega : 0<q) K
  simp only [wt,sum_const,smul_eq_mul,mul_one] at b
  have deg := endpt.degree x xv
  have ord := endpt.order
  have thin : (boundary D V A).card<s := by
    by_contra! le
    have pr := Nat.mul_le_mul_left (q-1) le
    have fact := congrArg (fun k => k*s) (show q=q-1+1 by omega)
    simp only [Nat.add_mul,Nat.one_mul] at fact
    omega
  refine ⟨thin,?_⟩
  have outside : (outN D V x \ A).card ≤ (boundary D V A).card :=
    card_le_card (by intro z hz; obtain ⟨out,ex⟩ := mem_sdiff.mp hz
                     exact boundary_iff.mpr ⟨(mem_outN.mp out).1,ex,x,K.rooted.2.1,(mem_outN.mp out).2⟩)
  have ne : (A.erase x).Nonempty := by
    have inter := card_sdiff_add_card_inter (outN D V x) A
    obtain ⟨z,hz⟩ := card_pos.mp (by omega : 0<(outN D V x ∩ A).card)
    obtain ⟨e,za⟩ := mem_inter.mp hz
    exact ⟨z,mem_erase.mpr ⟨fun eq => K.rooted.2.2 x K.rooted.2.1 (eq ▸ (mem_outN.mp e).2),za⟩⟩
  have cut := card_erase_add_one K.rooted.2.1
  have smaller := (card_erase_lt_of_mem K.rooted.2.1).trans_le (card_le_card K.rooted.1)
  by_contra! fails
  exact smaller.not_ge (endpt.stop _ ((erase_subset _ _).trans K.rooted.1) _
    ⟨ne,by omega,punctured_degree K endpt.degree⟩)

#print axioms terminal_of_candidate
#print axioms terminal_kernel_size

private theorem score_heads (q D V w x) : score q D V w x = w x + q*wt w (outN D V x) := by
  simp [score,wt,outN,sum_filter]

/-- One specific retained row must carry the exit demand on the actual
boundary heads that it reaches. -/
theorem kernel_exit {q D V b} {X : Witness q D V b} (least : X.Minimal) (hq : 2≤q)
    (free : QFree D X.carrier q) {x A} (K : Kernel D X.carrier X.weights x A) :
    ∃ y∈A.erase x, score q D X.carrier X.weights y ≤ wt X.weights (A.erase x) +
      q*wt X.weights (outN D (boundary D X.carrier A) y) := by
  let W := X.carrier
  let B := A.erase x
  let C := boundary D W A
  let w := X.weights
  have xv := K.rooted.1 K.rooted.2.1
  have ne : B.Nonempty := by
    have budget := ball_budget free (by omega : 0<q) K
    have high := nat_strict.mp X.strict x xv
    rw [score_heads] at high
    by_contra empty
    have only : ∀ y∈A, y=x := fun y hy => by
      by_contra diff
      exact empty ⟨y,mem_erase.mpr ⟨diff,hy⟩⟩
    have sub : outN D W x ⊆ C := by
      intro y hy
      exact boundary_iff.mpr ⟨(mem_outN.mp hy).1,fun a =>
        K.rooted.2.2 x K.rooted.2.1 (only y a ▸ (mem_outN.mp hy).2),x,K.rooted.2.1,(mem_outN.mp hy).2⟩
    have lo := Nat.mul_le_mul_left (q-1) (mono (w:=w) sub)
    have eq := congrArg (fun k => k*wt w (outN D W x)) (show q=q-1+1 by omega)
    simp only [Nat.add_mul,Nat.one_mul] at eq
    change wt w W < w x + q*wt w (outN D W x) at high
    change w x + wt w (outN D W x) + (q-1)*wt w C ≤ wt w W at budget
    omega
  have sub : B⊆W.erase x := fun y hy => mem_erase.mpr
    ⟨(mem_erase.mp hy).1,K.rooted.1 (mem_of_mem_erase hy)⟩
  have bw : B⊆W := sub.trans (erase_subset _ _)
  have less : wt w B<wt w W := by
    have eq := sum_erase_add W w xv
    have lo := mono (w:=w) sub
    have pos := X.positive x xv
    change wt w (W.erase x)+w x=wt w W at eq
    change 0<w x at pos
    omega
  obtain ⟨y,hy,low⟩ := light_after_edit least (bw.trans X.subset) ne w
    (fun i hi => X.positive i (bw hi)) less
  have ya := mem_of_mem_erase hy
  have oe : outN D W y = outN D B y ∪ outN D C y := by
    ext z
    constructor
    · intro e
      obtain ⟨zv,yz⟩ := mem_outN.mp e
      by_cases za : z∈A
      · exact mem_union_left _ (mem_outN.mpr ⟨mem_erase.mpr
          ⟨fun he => K.rooted.2.2 y ya (he ▸ yz),za⟩,yz⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨boundary_iff.mpr ⟨zv,za,y,ya,yz⟩,yz⟩)
    · intro e
      rcases mem_union.mp e with left|right
      · exact mem_outN.mpr ⟨bw (mem_outN.mp left).1,(mem_outN.mp left).2⟩
      · exact mem_outN.mpr ⟨(boundary_iff.mp (mem_outN.mp right).1).1,(mem_outN.mp right).2⟩
  have dis : Disjoint (outN D B y) (outN D C y) := Finset.disjoint_left.mpr
    (fun z inB inC => (boundary_iff.mp (mem_outN.mp inC).1).2.1 (mem_of_mem_erase (mem_outN.mp inB).1))
  refine ⟨y,hy,?_⟩
  rw [score_heads] at low ⊢
  change w y + q*wt w (outN D W y) ≤ wt w B + q*wt w (outN D C y)
  rw [oe,show wt w (outN D B y ∪ outN D C y)=wt w (outN D B y)+wt w (outN D C y) from sum_union dis,Nat.mul_add]
  change w y+q*wt w (outN D B y) ≤ wt w B at low
  omega

#print axioms kernel_exit

theorem boundary_omissions {q D V b} {X : Witness q D V b} (least : X.Minimal) (hq : 2≤q)
    (free : QFree D X.carrier q) {x A} (K : Kernel D X.carrier X.weights x A) :
    let W := X.carrier
    let w := X.weights
    let C := boundary D W A
    ∃ y∈A.erase x, w x + (score q D W w y - wt w W) + q*wt w (C \ outN D C y) ≤
      wt w (closedRows D W A \ insert x (outN D W x)) := by
  intro W w C
  obtain ⟨y,hy,bill⟩ := kernel_exit least hq free K
  refine ⟨y,hy,?_⟩
  have xv := K.rooted.1 K.rooted.2.1
  have high := nat_strict.mp X.strict y (K.rooted.1 (mem_of_mem_erase hy))
  have grow := ball_budget free (by omega : 0<q) K
  have inside : insert x (outN D W x) ⊆ closedRows D W A := by
    intro z hz
    rcases mem_insert.mp hz with rfl|e
    · exact closed_mem.mpr (Or.inl K.rooted.2.1)
    · exact closed_mem.mpr (.inr ⟨x,K.rooted.2.1,e⟩)
  have extra := sum_sdiff (f:=w) inside
  have e0 : x∉outN D W x := fun e => loopfree free (by omega) xv (mem_outN.mp e).2
  rw [sum_insert e0] at extra
  have inc := increment D W w A
  have er := sum_erase_add A w K.rooted.2.1
  have missing := sum_sdiff (f:=w) (filter_subset (fun z => D y z=true) C)
  change wt w (C \ outN D C y)+wt w (outN D C y)=wt w C at missing
  have times := congrArg (fun t => q*t) missing
  have factor := congrArg (fun t => t*wt w C) (show q=q-1+1 by omega)
  simp only [Nat.mul_add] at times
  simp only [Nat.add_mul,Nat.one_mul] at factor
  change wt w W < score q D W w y at high
  change score q D W w y ≤ wt w (A.erase x)+q*wt w (outN D C y) at bill
  change w x + wt w (outN D W x) + (q-1)*wt w C ≤ wt w W at grow
  change wt w C + wt w A = wt w (closedRows D W A) at inc
  change wt w (A.erase x)+w x=wt w A at er
  change wt w (closedRows D W A \ insert x (outN D W x)) + (w x+wt w (outN D W x)) =
    wt w (closedRows D W A) at extra
  omega

#print axioms boundary_omissions
end LeanCH.BR.ShenRootedKernel
