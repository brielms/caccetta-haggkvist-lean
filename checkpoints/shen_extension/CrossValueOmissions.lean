import checkpoints.shen_extension.NativeReturnAccounts

namespace LeanCH.BR.Closure.CrossValueOmissions
open Finset BRq2 BRq3 BR45 WeightedSD FirstPacketBarrier MarkedCyclePeeling

def lost (D G : CH.Digraph) (V : Finset ℕ) : Finset (ℕ×ℕ) :=
  (V×ˢV).filter (fun e=>D e.1 e.2=true ∧ G e.1 e.2=false)

def cost (q : ℕ) (a b : ℕ→ℚ) (A : Finset (ℕ×ℕ)) : ℚ :=
  ∑e∈A,(q:ℚ)*a e.1*b e.2

theorem selected_sub {D F i j} (hit : graph D F i j=true) : D i j=true := by
  obtain ⟨M,hm⟩ := active.mp hit
  exact (mem_col.mp hm).2.2.2

/-- The cost of the omitted ordered pairs is the difference of the
two row contractions, for arbitrary signed vectors and nested graphs. -/
theorem difference {D G : CH.Digraph} {V : Finset ℕ} (q : ℕ)
    (sub : ∀i∈V,∀j∈V,G i j=true → D i j=true) (a b : ℕ→ℚ) :
    cost q a b (lost D G V) =
      (∑i∈V,a i*WeightedSD.row q D V b i)-(∑i∈V,a i*WeightedSD.row q G V b i) := by
  rw [cost,lost,sum_filter,sum_product,←sum_sub_distrib]
  apply sum_congr rfl; intro i iv
  simp only [WeightedSD.row,outW,mul_add,mul_sum]
  rw [add_sub_add_left_eq_sub]
  rw [←sum_sub_distrib]
  apply sum_congr rfl; intro j jv
  cases dij : D i j <;> cases gij : G i j <;> simp <;>
    first | exact (Bool.noConfusion (dij.symm.trans (sub i iv j jv gij))) | ring

private theorem contract {V : Finset ℕ} {a f : ℕ→ℚ} {c : ℚ} (prob : mass V a=1)
    (flat : ∀i∈V,f i=c) : (∑i∈V,a i*f i)=c := by
  calc
    _ = ∑i∈V,a i*c := sum_congr rfl (fun i iv=>by rw [flat i iv])
    _ = mass V a*c := (sum_mul ..).symm
    _ = c := by rw [prob,one_mul]

/-- The two mixed prices give the same exact budget on the same lost
arcs. Native and selected equalizers are normalized on the same support. -/
theorem exact_gap {q D G V w π x ρ c d}
    (sub : ∀i∈V,∀j∈V,G i j=true → D i j=true)
    (wm : mass V w=1) (pm : mass V π=1) (xm : mass V x=1) (rm : mass V ρ=1)
    (wr : ∀i∈V,WeightedSD.row q D V w i=c) (pc : ∀j∈V,WeightedSD.col q D V π j=c)
    (xr : ∀i∈V,WeightedSD.row q G V x i=d) (rc : ∀j∈V,WeightedSD.col q G V ρ j=d) :
    cost q ρ w (lost D G V)=c-d ∧ cost q π x (lost D G V)=c-d := by
  constructor
  · rw [difference q sub,NativeReturnAccounts.balance q G V w ρ,contract rm wr,contract wm rc]
  · rw [difference q sub,NativeReturnAccounts.balance q D V x π,contract xm pc,contract pm xr]

theorem subset_budget {q D G V a b c d A} (an : ∀i∈V,0≤a i) (bn : ∀j∈V,0≤b j)
    (budget : cost q a b (lost D G V)=c-d) (sub : A⊆lost D G V) : cost q a b A≤c-d := by
  rw [←budget]
  apply sum_le_sum_of_subset_of_nonneg sub
  intro e er _
  obtain ⟨iv,jv⟩ := mem_product.mp (mem_filter.mp er).1
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (an _ iv)) (bn _ jv)

theorem rectangle (q : ℕ) (a b : ℕ→ℚ) (P H : Finset ℕ) :
    cost q a b (P×ˢH)=(q:ℚ)*mass P a*mass H b := by
  simp only [cost,sum_product,←mul_sum,←sum_mul,mass]

/-- One omitted native star is charged once, regardless of how many
marked cycles use the same first arc. -/
theorem star {q D G V a b c d p} (pv : p∈V) (an : ∀i∈V,0≤a i) (bn : ∀j∈V,0≤b j)
    (budget : cost q a b (lost D G V)=c-d) {T : Finset ℕ} (heads : T⊆outN D V p)
    (absent : ∀t∈T,G p t=false) :
    (q:ℚ)*a p*mass T b≤c-d := by
  have sub : ({p}:Finset ℕ)×ˢT⊆lost D G V := by
    rintro ⟨i,j⟩ e
    obtain ⟨ip,jt⟩ := mem_product.mp e
    obtain rfl := mem_singleton.mp ip
    obtain ⟨jv,pj⟩ := mem_outN.mp (heads jt)
    exact mem_filter.mpr ⟨mem_product.mpr ⟨pv,jv⟩,pj,absent j jt⟩
  simpa only [rectangle,mass,sum_singleton] using subset_budget an bn budget sub

/-- The requested specialization to a complete family's selected graph.
The same accounting holds without completeness. At a heavy native parent
the lost selected forward weight satisfies c·x(T) < q·(c−1). -/
theorem on_family {q D F V w π x ρ c d}
    (wm : mass V w=1) (pm : mass V π=1) (xm : mass V x=1) (rm : mass V ρ=1)
    (wp : ∀i∈V,0<w i) (pp : ∀i∈V,0<π i) (xp : ∀i∈V,0<x i) (rp : ∀i∈V,0<ρ i)
    (wr : ∀i∈V,WeightedSD.row q D V w i=c) (pc : ∀j∈V,WeightedSD.col q D V π j=c)
    (xr : ∀i∈V,WeightedSD.row q (graph D F) V x i=d)
    (rc : ∀j∈V,WeightedSD.col q (graph D F) V ρ j=d) (high : 1<d) :
    let G := graph D F
    let L := lost D G V
    cost q ρ w L=c-d ∧ cost q π x L=c-d ∧ c-d<c-1 ∧
    ∀p∈V,∀T⊆outN D V p,(∀t∈T,G p t=false) →
      (q:ℚ)*π p*mass T x≤c-d ∧ (q:ℚ)*ρ p*mass T w≤c-d ∧
      (0<q → c<(q:ℚ)^2*π p → c*mass T x<(q:ℚ)*(c-1)) := by
  intro G L
  obtain ⟨fwd,rev⟩ := exact_gap (fun _ _ _ _=>selected_sub) wm pm xm rm wr pc xr rc
  refine ⟨fwd,rev,by linarith,?_⟩
  intro p pv T sub absent
  have a := star pv (fun i iv=>(pp i iv).le) (fun j jv=>(xp j jv).le) rev sub absent
  have b := star pv (fun i iv=>(rp i iv).le) (fun j jv=>(wp j jv).le) fwd sub absent
  refine ⟨a,b,?_⟩
  intro qp heavy
  have qpos : (0:ℚ)<q := by exact_mod_cast qp
  have m := mass_nonneg (fun t ht=>(xp t (outN_subset (sub ht))).le)
  nlinarith only [mul_le_mul_of_nonneg_right heavy.le m,mul_le_mul_of_nonneg_left a qpos.le,
    mul_lt_mul_of_pos_left (show c-d<c-1 by linarith only [high]) qpos]

#print axioms difference
#print axioms exact_gap
#print axioms subset_budget
#print axioms on_family
end LeanCH.BR.Closure.CrossValueOmissions
