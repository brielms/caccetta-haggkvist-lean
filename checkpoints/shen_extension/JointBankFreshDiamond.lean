import checkpoints.shen_extension.JointBankGeometry
import checkpoints.shen_extension.SupplierFat54

namespace LeanCH.BR.BypassBankReplay
open Finset BRq2 BRq3 BR45 BypassRepair

/-- All surviving rows heading both deleted labels and missing the target. -/
def freshRows (D : CH.Digraph) (V : Finset ℕ) (p h z : ℕ) : Finset ℕ :=
  (inN D V p ∩ inN D V h).filter (fun c => D c z ≠ true)

namespace FreshDiamond

private def far (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) :=
  V.filter (fun z => z ≠ u ∧ D u z ≠ true ∧ D z u ≠ true)

private abbrev middle (D : CH.Digraph) (V : Finset ℕ) (c z : ℕ) :=
  outN D (inN D V z) c

private theorem far_card {D V} (free : QFree D V 3) {c} (cv : c∈V) :
    (far D V c).card + 1 + (outN D V c).card + (inN D V c).card = V.card := by
  let H := outN D V c
  let I := inN D V c
  have dis : Disjoint H I := disjoint_left.mpr fun a ah ai =>
    digonfree free (by decide) cv (mem_outN.mp ah).1 (mem_outN.mp ah).2 (mem_inN.mp ai).2
  have off : c ∉ H ∪ I := by
    intro cc
    rcases mem_union.mp cc with ch|ci
    · exact loopfree free (by decide) cv (mem_outN.mp ch).2
    · exact loopfree free (by decide) cv (mem_inN.mp ci).2
  have sub : insert c (H∪I) ⊆ V := insert_subset_iff.mpr
    ⟨cv,union_subset outN_subset (fun _ h => (mem_inN.mp h).1)⟩
  have eq : far D V c = V \ insert c (H∪I) := by
    ext z
    simp only [far,H,I,mem_filter,mem_sdiff,mem_insert,mem_union,mem_outN,mem_inN]
    tauto
  have cnt := card_sdiff_add_card_eq_card sub
  rw [← eq,card_insert_of_notMem off,card_union_of_disjoint dis] at cnt
  change (far D V c).card+1+H.card+I.card=V.card
  omega

private theorem swap_far {D V} (f : ℕ → ℕ → ℕ) :
    (∑ c∈V,∑ z∈far D V c,f c z) = ∑ z∈V,∑ c∈far D V z,f c z := by
  apply sum_comm'
  intro c z
  simp only [far,mem_filter]
  tauto

/-- The two-step count consumes at most one internal arc per unordered pair
of heads of a row. -/
private theorem row_paths {D V s} (free : QFree D V 3) (reg : OutEq s D V)
    {c} (cv : c∈V) :
    s*(s+1) ≤ 2*∑ z∈far D V c,(middle D V c z).card := by
  classical
  let H := outN D V c
  let F := far D V c
  have hsize : H.card=s := reg c cv
  have eq (z : ℕ) : middle D V c z = inN D H z := by
    ext p
    simp only [middle,H,mem_inN,mem_outN]
    tauto
  have swap : (∑ z∈F,(middle D V c z).card) = ∑ p∈H,(outN D F p).card := by
    simp_rw [eq]
    exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun z p => D p z=true)
  have dis : Disjoint H F := disjoint_left.mpr fun z zh zf => (mem_filter.mp zf).2.2.1 (mem_outN.mp zh).2
  have partition (p) (ph : p∈H) : (outN D H p).card + (outN D F p).card = s := by
    have seen : outN D (H ∪ F) p = outN D V p := by
      ext z
      constructor
      · intro h
        obtain ⟨hz,e⟩ := mem_outN.mp h
        exact mem_outN.mpr ⟨(union_subset outN_subset (filter_subset _ _)) hz,e⟩
      · intro h
        obtain ⟨zv,pz⟩ := mem_outN.mp h
        refine mem_outN.mpr ⟨?_,pz⟩
        by_cases cz : D c z=true
        · exact mem_union_left _ (mem_outN.mpr ⟨zv,cz⟩)
        · apply mem_union_right
          obtain ⟨pv,cp⟩ := mem_outN.mp ph
          have diff : z≠c := fun hc => digonfree free (by decide) cv pv cp (hc ▸ pz)
          exact mem_filter.mpr ⟨zv,diff,cz,fun zc =>
            free c 3 (by decide) (by decide)
              (.step pv cp (.step zv pz (.step cv zc (.refl _))))⟩
    have cnt := card_outN_union (D:=D) dis p
    rw [seen,reg p (outN_subset ph)] at cnt
    omega
  have total : (∑ p∈H,(outN D H p).card)+(∑ p∈H,(outN D F p).card)=s*s := by
    rw [←sum_add_distrib,sum_congr rfl partition,sum_const,smul_eq_mul,hsize]
  have cap := SupplierFat54.arc_count (free.mono_set (show H⊆V from outN_subset)) (by decide : 2≤3)
  rw [hsize] at cap
  change s*(s+1) ≤ 2*∑ z∈F,(middle D V c z).card
  rw [swap]
  nlinarith only [cap,total]

/-- Count each ordered pair of distinct intermediate vertices by its target. -/
private theorem target_pairs {D V s} {z : ℕ} (_zv : z∈V)
    (limit : ∀ p∈V,∀ h∈V,p≠h → D p z=true → D h z=true →
      8*(freshRows D V p h z).card ≤ s) :
    8 * (∑ c∈far D V z,(middle D V c z).offDiag.card) ≤
      (inN D V z).offDiag.card*s := by
  classical
  let P := inN D V z
  let F := far D V z
  let R (c : ℕ) (e : ℕ×ℕ) := D c e.1=true ∧ D c e.2=true
  have eq (c : ℕ) : (middle D V c z).offDiag = P.offDiag.filter (R c) := by
    ext ⟨i,j⟩
    simp only [middle,P,R,mem_filter,mem_offDiag,mem_outN]
    tauto
  have cnt : (∑ c∈F,(middle D V c z).offDiag.card) =
      ∑ e∈P.offDiag,(F.filter (fun c => R c e)).card := by
    simp_rw [eq]
    exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
  have paid (e : ℕ×ℕ) (em : e∈P.offDiag) :
      8*(F.filter (fun c => R c e)).card ≤ s := by
    obtain ⟨i,j,ij⟩ := mem_offDiag.mp em
    have sub : F.filter (fun c => R c e) ⊆ freshRows D V e.1 e.2 z := by
      intro c cm
      obtain ⟨cf,ci,cj⟩ := mem_filter.mp cm
      obtain ⟨cv,_,_,cz⟩ := mem_filter.mp cf
      exact mem_filter.mpr ⟨mem_inter.mpr ⟨mem_inN.mpr ⟨cv,ci⟩,mem_inN.mpr ⟨cv,cj⟩⟩,cz⟩
    exact (Nat.mul_le_mul_left 8 (card_le_card sub)).trans
      (limit _ (mem_inN.mp i).1 _ (mem_inN.mp j).1 ij (mem_inN.mp i).2 (mem_inN.mp j).2)
  change 8*(∑ c∈F,(middle D V c z).offDiag.card) ≤ P.offDiag.card*s
  rw [cnt,mul_sum]
  simpa only [sum_const,smul_eq_mul] using sum_le_sum paid

private theorem square_bound (a : ℕ) (S : Finset ℕ) :
    4*a*S.card ≤ 4*S.offDiag.card+(a+1)*(a+1) := by
  rw [offDiag_card]
  have cnt : S.card*S.card-S.card+S.card=S.card*S.card := by
    cases e : S.card with
    | zero => simp
    | succ k => exact Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by omega))
  zify at cnt ⊢
  nlinarith only [cnt,sq_nonneg (2*(S.card:ℤ)-((a:ℤ)+1))]

end FreshDiamond

open FreshDiamond in
/-- A positive fraction of a row's degree can occur as fresh marks for one
pair of deleted heads and a single common target in a triangle-free source. -/
theorem exists_fresh_pair_at_triangle {D V s} (free : QFree D V 3) (live : V.Nonempty)
    (reg : OutEq s D V) (hs : 8 ≤ s) (room : V.card ≤ 3*s) :
    ∃ p∈V,∃ h∈V,p≠h ∧ ∃z∈V,D p z=true ∧ D h z=true ∧ s < 8*(freshRows D V p h z).card := by
  classical
  obtain ⟨a,rfl⟩ : ∃a,s=a+1 := ⟨s-1,by omega⟩
  by_contra! limit
  let n := V.card
  let T := ∑ c∈V,∑ z∈far D V c,(middle D V c z).card
  let M := ∑ c∈V,(far D V c).card
  let K := ∑ c∈V,∑ z∈far D V c,(middle D V c z).offDiag.card
  have np : 0<n := card_pos.mpr live
  have indeg : (∑ c∈V,(inN D V c).card)=n*(a+1) := by
    have dc : (∑ c∈V,(outN D V c).card)=∑ c∈V,(inN D V c).card := Compose.ThinRigid.sum_out_eq_sum_in D V
    rw [← dc]
    rw [sum_congr rfl reg,sum_const,smul_eq_mul]
  have far_sum : M + n + n*(a+1) + n*(a+1) = n*n := by
    have cnt := sum_congr (s₁:=V) rfl (fun c cv => far_card free cv)
    simp only [sum_add_distrib,sum_const,smul_eq_mul,mul_one] at cnt
    rw [sum_congr rfl reg,indeg,sum_const,smul_eq_mul] at cnt
    exact cnt
  have m_bound : M ≤ n*a := by
    have size := Nat.mul_le_mul_left n room
    change n*n ≤ n*(3*(a+1)) at size
    nlinarith only [far_sum,size]
  have t_bound : n*((a+1)*(a+1+1)) ≤ 2*T := by
    have cnt := sum_le_sum (s:=V) (fun c cv => row_paths free reg cv)
    simpa only [T,sum_const,smul_eq_mul,←mul_sum,n] using cnt
  have k_bound : 8*K ≤ n*(a+1)*(2*a)*(a+1) := by
    have swapped : K = ∑ z∈V,∑ c∈far D V z,(middle D V c z).offDiag.card :=
      swap_far (fun c z => (middle D V c z).offDiag.card)
    rw [swapped,mul_sum]
    have bound (z : ℕ) (zv : z∈V) :
        8*(∑ c∈far D V z,(middle D V c z).offDiag.card) ≤ (inN D V z).card*(2*a)*(a+1) := by
      have cnt := target_pairs (s:=a+1) zv (fun p pv h hv ph ep eh => limit p pv h hv ph z zv ep eh)
      have sz := far_card free zv
      rw [reg z zv] at sz
      have lim : (inN D V z).card-1 ≤ 2*a := by omega
      have pbound : (inN D V z).offDiag.card ≤ (inN D V z).card*(2*a) := by
        rw [offDiag_card,←Nat.mul_sub_one]
        exact Nat.mul_le_mul_left _ lim
      exact cnt.trans (Nat.mul_le_mul_right _ pbound)
    have cnt := sum_le_sum bound
    rw [←sum_mul,←sum_mul,indeg] at cnt
    exact cnt
  have sq_bound : 4*a*T ≤ 4*K+M*((a+1)*(a+1)) := by
    have localRow (c : ℕ) :
        4*a*(∑ z∈far D V c,(middle D V c z).card) ≤
        4*(∑ z∈far D V c,(middle D V c z).offDiag.card)+(far D V c).card*((a+1)*(a+1)) := by
      have cnt := sum_le_sum (s:=far D V c) (fun z _ => square_bound a (middle D V c z))
      rw [sum_add_distrib,←mul_sum,←mul_sum,sum_const,smul_eq_mul] at cnt
      exact cnt
    have cnt := sum_le_sum (s:=V) (fun c _ => localRow c)
    simpa only [T,K,M,←mul_sum,sum_add_distrib,←sum_mul] using cnt
  have lower := Nat.mul_le_mul_left (2*a) t_bound
  have upper := Nat.mul_le_mul_right ((a+1)*(a+1)) m_bound
  have positive : 0<n*a*(a+1) := Nat.mul_pos (Nat.mul_pos np (by omega)) (by omega)
  nlinarith only [lower,upper,sq_bound,k_bound,positive]


/-- Every fresh row for these same two deleted labels and the same target
can be used as the marked row on the two-label source boundary. -/
theorem exists_fresh_marked_pair {s} (X : ShenMinimumOrder.Source 3 s) (reg : OutEq s X.D X.V)
    (hs : 8 ≤ s) (order : X.V.card = 3*(s-1)+2) :
    ∃ m : Cell, Marked X m ∧ JointShort X m ∧
      ∃ h∈X.V,m.parent≠h ∧ m.bank={m.parent,h} ∧ X.D h m.target=true ∧
        m.x∈freshRows X.D X.V m.parent h m.target ∧
        s < 8*(freshRows X.D X.V m.parent h m.target).card ∧
        ∀ y∈freshRows X.D X.V m.parent h m.target,
          Marked X ⟨m.bank,y,m.parent,m.target⟩ ∧ JointShort X ⟨m.bank,y,m.parent,m.target⟩ := by
  classical
  have room : X.V.card ≤ 3*s := by omega
  obtain ⟨p,pv,h,hv,ph,z,zv,pz,hz,many⟩ := exists_fresh_pair_at_triangle X.free X.nonempty reg hs room
  let C := freshRows X.D X.V p h z
  let B : Finset ℕ := {p,h}
  let U := X.V \ B
  have sz : 2 ≤ C.card := by change s<8*C.card at many; omega
  have bc : B.card=2 := card_pair ph
  have bv : B⊆X.V := insert_subset pv (singleton_subset_iff.mpr hv)
  have zp : z≠p := fun eq => loopfree X.free (by decide) pv (eq ▸ pz)
  have zh : z≠h := fun eq => loopfree X.free (by decide) hv (eq ▸ hz)
  have zu : z∈U := mem_sdiff.mpr ⟨zv,by simp [B,zp,zh]⟩
  have mark (c : ℕ) (cm : c∈C) : Marked X ⟨B,c,p,z⟩ := by
    obtain ⟨both,fresh⟩ := mem_filter.mp cm
    obtain ⟨cv,cp⟩ := mem_inN.mp (mem_inter.mp both).1
    have ch := (mem_inN.mp (mem_inter.mp both).2).2
    have cnp : c≠p := fun eq => loopfree X.free (by decide) pv (eq ▸ cp)
    have cnh : c≠h := fun eq => loopfree X.free (by decide) hv (eq ▸ ch)
    have cu : c∈U := mem_sdiff.mpr ⟨cv,by simp [B,cnp,cnh]⟩
    have sub : B ⊆ outN X.D X.V c :=
      insert_subset_iff.mpr ⟨mem_outN.mpr ⟨pv,cp⟩,singleton_subset_iff.mpr (mem_outN.mpr ⟨hv,ch⟩)⟩
    have eq : outN X.D U c = outN X.D X.V c \ B := by ext a; simp only [U,mem_sdiff,mem_outN]; tauto
    have cnt := card_sdiff_add_card_eq_card sub
    rw [←eq,bc,reg c cv] at cnt
    exact ⟨bv,by change B.card = _; omega,cu,by simp [B],zu,cp,pz,fresh,by
      change (outN X.D U c).card+1=s-1; omega,
      chain_through_arc X (by decide) (by omega) reg room cv pv zv cp pz⟩
  have all (c : ℕ) (cm : c∈C) : Marked X ⟨B,c,p,z⟩ ∧ JointShort X ⟨B,c,p,z⟩ := by
    have ne : (C.erase c).Nonempty := card_pos.mp (by rw [card_erase_of_mem cm]; omega)
    obtain ⟨j,jm⟩ := ne
    obtain ⟨jc,jC⟩ := mem_erase.mp jm
    have other := mark j jC
    have dj : (outN X.D U j).card+1=s-1 := other.deficit
    exact ⟨mark c cm,j,other.xu,jc,by change (outN X.D U j).card<s-1; omega⟩
  obtain ⟨c,cm⟩ := card_pos.mp (by omega : 0<C.card)
  exact ⟨⟨B,c,p,z⟩,(all c cm).1,(all c cm).2,h,hv,ph,rfl,hz,cm,many,all⟩

#print axioms exists_fresh_pair_at_triangle
#print axioms exists_fresh_marked_pair

end LeanCH.BR.BypassBankReplay

