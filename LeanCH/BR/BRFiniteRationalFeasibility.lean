import LeanCH.BR.BRFiniteDual
import Mathlib.Data.Fin.Tuple.Basic

/-! Exact descent of finite weak rational linear inequalities from real to
rational solutions. Closed faces are preserved by elimination, not density. -/
namespace LeanCH.BR.FiniteDual
open Finset
universe u v

theorem finite_interval_point {I : Type u} (L U : Finset I) (r : I→ℚ)
    (h : ∀j∈L,∀i∈U,r j≤r i) :
    ∃t : ℚ,(∀j∈L,r j≤t) ∧ (∀i∈U,t≤r i) := by
  classical
  by_cases hl : L.Nonempty
  · obtain ⟨j,hj,hmax⟩ := L.exists_max_image r hl
    exact ⟨r j,hmax,fun i hi=>h j hj i hi⟩
  · by_cases hu : U.Nonempty
    · obtain ⟨i,hi,hmin⟩ := U.exists_min_image r hu
      exact ⟨r i,fun j hj=>False.elim (hl ⟨j,hj⟩),hmin⟩
    · exact ⟨0,fun j hj=>False.elim (hl ⟨j,hj⟩),fun i hi=>False.elim (hu ⟨i,hi⟩)⟩

theorem rational_weak_feasible_fin (n : ℕ) :
    ∀{I : Type u} [Fintype I] (A : I→Fin n→ℚ) (b : I→ℚ)
      (x : Fin n→ℝ), (∀i,(∑j,(A i j:ℝ)*x j)≤(b i:ℝ)) →
      ∃y : Fin n→ℚ,∀i,(∑j,A i j*y j)≤b i := by
  classical
  induction n with
  | zero =>
    intro I _ A b x hx
    refine ⟨fun j=>Fin.elim0 j,?_⟩
    intro i
    have h : (0:ℝ)≤(b i:ℝ) := by simpa using hx i
    simpa using (show (0:ℚ)≤b i by exact_mod_cast h)
  | succ n ih =>
    intro I _ A b x hx
    let A' : (I ⊕ (I×I))→Fin n→ℚ := fun e k=>
      match e with
      | .inl i => if A i 0=0 then A i k.succ else 0
      | .inr (i,j) => if 0<A i 0 ∧ A j 0<0 then
          A i 0*A j k.succ-A j 0*A i k.succ else 0
    let b' : (I ⊕ (I×I))→ℚ := fun e=>
      match e with
      | .inl i => if A i 0=0 then b i else 0
      | .inr (i,j) => if 0<A i 0 ∧ A j 0<0 then A i 0*b j-A j 0*b i else 0
    have hxsplit (i : I) : (A i 0:ℝ)*x 0+(∑k:Fin n,(A i k.succ:ℝ)*x k.succ)≤(b i:ℝ) := by
      simpa only [Fin.sum_univ_succ] using hx i
    have hp : ∀e,(∑k:Fin n,(A' e k:ℝ)*x k.succ)≤(b' e:ℝ) := by
      intro e
      rcases e with i | ⟨i,j⟩
      · by_cases hz : A i 0=0
        · simpa [A',b',hz] using hxsplit i
        · simp [A',b',hz]
      · by_cases hsign : 0<A i 0 ∧ A j 0<0
        · have hi : (0:ℝ)<(A i 0:ℝ) := by exact_mod_cast hsign.1
          have hj : (A j 0:ℝ)<0 := by exact_mod_cast hsign.2
          have h1 := mul_le_mul_of_nonneg_left (hxsplit i) (neg_nonneg.mpr hj.le)
          have h2 := mul_le_mul_of_nonneg_left (hxsplit j) hi.le
          simp only [A',b',if_pos hsign,Rat.cast_sub,Rat.cast_mul,sub_mul,mul_assoc,
            sum_sub_distrib,←mul_sum]
          nlinarith
        · simp [A',b',hsign]
    obtain ⟨y,hy⟩ := ih A' b' (fun k=>x k.succ) hp
    let tail : I→ℚ := fun i=>∑k:Fin n,A i k.succ*y k
    let bound : I→ℚ := fun i=>(b i-tail i)/A i 0
    let L := univ.filter (fun i=>A i 0<0)
    let U := univ.filter (fun i=>0<A i 0)
    have hpair : ∀j∈L,∀i∈U,bound j≤bound i := by
      intro j hj i hi
      have hn : A j 0<0 := (mem_filter.mp hj).2
      have hpos : 0<A i 0 := (mem_filter.mp hi).2
      have hsign : 0<A i 0 ∧ A j 0<0 := ⟨hpos,hn⟩
      have h := hy (.inr (i,j))
      simp only [A',b',if_pos hsign,sub_mul,mul_assoc,sum_sub_distrib,←mul_sum] at h
      change A i 0*tail j-A j 0*tail i≤A i 0*b j-A j 0*b i at h
      dsimp only [bound]
      rw [le_div_iff₀ hpos,div_mul_eq_mul_div,div_le_iff_of_neg hn]
      nlinarith
    obtain ⟨t,hL,hU⟩ := finite_interval_point L U bound hpair
    refine ⟨Fin.cons t y,?_⟩
    intro i
    simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    change A i 0*t+tail i≤b i
    rcases lt_trichotomy (A i 0) 0 with hn | hz | hp
    · have h := hL i (mem_filter.mpr ⟨mem_univ _,hn⟩)
      have hb := (div_le_iff_of_neg hn).mp h
      nlinarith
    · have h := hy (.inl i)
      simpa [A',b',hz,tail] using h
    · have h := hU i (mem_filter.mpr ⟨mem_univ _,hp⟩)
      have hb := (le_div_iff₀ hp).mp h
      nlinarith

theorem rational_weak_feasible {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (A : I→J→ℚ) (b : I→ℚ) (x : J→ℝ)
    (hx : ∀i,(∑j,(A i j:ℝ)*x j)≤(b i:ℝ)) :
    ∃y : J→ℚ,∀i,(∑j,A i j*y j)≤b i := by
  classical
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hfin : ∀i,(∑k,(A i (e k):ℝ)*x (e k))≤(b i:ℝ) := by
    intro i
    simpa only [e.sum_comp (fun j=>(A i j:ℝ)*x j)] using hx i
  obtain ⟨y,hy⟩ := rational_weak_feasible_fin (Fintype.card J)
    (fun i k=>A i (e k)) b (fun k=>x (e k)) hfin
  refine ⟨fun j=>y (e.symm j),?_⟩
  intro i
  have he : (∑j,A i j*y (e.symm j))=∑k,A i (e k)*y k := by
    rw [←e.sum_comp (fun j=>A i j*y (e.symm j))]
    simp only [Equiv.symm_apply_apply]
  rw [he]
  exact hy i

end LeanCH.BR.FiniteDual
