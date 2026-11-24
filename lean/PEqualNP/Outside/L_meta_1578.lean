import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1578

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_stepW_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega

theorem foldl_stepW_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_take_getD (gs : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((gs.take t).foldl stepW w).length) :
    (gs.foldl stepW w).getD i false = ((gs.take t).foldl stepW w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t gs, List.foldl_append]
  exact foldl_stepW_getD _ _ _ hi

theorem gate_val (C : Circuit) (x : Fin 13 → Bool) (t : ℕ) (ht : t < C.gates.length) :
    (C.wires (List.ofFn x)).getD (13 + t) false =
      (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
        if i < 13 + t then (C.wires (List.ofFn x)).getD i false else false) := by
  have hsplit : C.gates = C.gates.take t ++ C.gates[t] :: C.gates.drop (t + 1) := by
    simp [List.take_append_drop]
  have hlen : ((C.gates.take t).foldl stepW (List.ofFn x)).length = 13 + t := by
    rw [foldl_stepW_length, List.length_ofFn, List.length_take, Nat.min_eq_left ht.le]
  have hlhs : (C.wires (List.ofFn x)).getD (13 + t) false =
      (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
        ((C.gates.take t).foldl stepW (List.ofFn x)).getD i false) := by
    change (C.gates.foldl stepW (List.ofFn x)).getD (13 + t) false = _
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [foldl_stepW_getD _ _ _ (by simp only [stepW, List.length_append, List.length_singleton, hlen]; omega)]
    simp only [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : ((C.gates.take t).foldl stepW (List.ofFn x)).length ≤ 13 + t), hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hlhs]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs with hi
  · exact (foldl_take_getD C.gates (List.ofFn x) t i (by omega)).symm
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem input_val (C : Circuit) (x : Fin 13 → Bool) (i : Fin 13) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  change (C.gates.foldl stepW (List.ofFn x)).getD i.val false = x i
  rw [foldl_stepW_getD _ _ _ (by simp)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

def wire (gates : List Gate) (x : Fin 13 → Bool) (w : ℕ) : Bool :=
  (Circuit.mk gates w).eval (List.ofFn x)

def miss (L : Fin 13 → Finset (Fin 13)) (t : Fin 13) : Fin 13 → Bool :=
  fun a => decide (a ∉ L t)

def special (L : Fin 13 → Finset (Fin 13)) (p : Fin 13) : Fin 13 → Bool :=
  fun a => decide (a = p ∨ a ∉ L 0)

def lines13 (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

theorem special_geometry : ∀ (p t : Fin 13), p = 3 ∨ p = 9 →
    t ∈ ({4, 10, 12} : Finset (Fin 13)) ∨ t ∈ ({1, 5, 11} : Finset (Fin 13)) →
    p ∉ lines13 t := by
  intro p t hp ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases hp with rfl | rfl <;> rcases ht with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> decide

theorem nonzero_first : ∀ t : Fin 13, t ∈ ({4, 10, 12} : Finset (Fin 13)) → t ≠ 0 := by
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl <;> decide

theorem nonzero_second : ∀ t : Fin 13, t ∈ ({1, 5, 11} : Finset (Fin 13)) → t ≠ 0 := by
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl <;> decide

theorem raw_invariant (L : Fin 13 → Finset (Fin 13)) (hL : ∀ t, L t = lines13 t)
    (p l m a : Fin 13) (hp : p = 3 ∨ p = 9)
    (hl : l ∈ ({4, 10, 12} : Finset (Fin 13))) (hm : m ∈ ({1, 5, 11} : Finset (Fin 13)))
    (hs : special L p a = true) (h0 : miss L 0 a = false) :
    miss L l a = true ∧ miss L m a = true := by
  have ha : a = p := by
    simp only [special, decide_eq_true_eq] at hs
    rcases hs with he | hout
    · exact he
    · have hm0 : miss L 0 a = true := decide_eq_true hout
      rw [hm0] at h0
      contradiction
  subst a
  simp only [miss, decide_eq_true_eq, hL]
  exact ⟨special_geometry p l hp (Or.inl hl), special_geometry p m hp (Or.inr hm)⟩

theorem wire_input (gates : List Gate) (x : Fin 13 → Bool) (i : Fin 13) :
    wire gates x i.val = x i := input_val (Circuit.mk gates 0) x i

theorem wire_gate (gates : List Gate) (x : Fin 13 → Bool) (i : Fin gates.length)
    (hi : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val) :
    wire gates x (13 + i.val) = (gates.get i).op.eval ((gates.get i).inputs.map (wire gates x)) := by
  rw [wire, Circuit.eval, gate_val (Circuit.mk gates (13 + i.val)) x i.val i.isLt]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hat : a < 13 + i.val := hi a ha
  rw [ite_eq_left hat]
  rfl

theorem wire_or (gates : List Gate) (x : Fin 13 → Bool) (i : Fin gates.length)
    (hi : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val) (ho : (gates.get i).op = GateOp.or) :
    wire gates x (13 + i.val) = true ↔ ∃ a ∈ (gates.get i).inputs, wire gates x a = true := by
  rw [wire_gate gates x i hi, ho]
  simp [GateOp.eval, List.any_eq_true]

theorem before_invariant (L : Fin 13 → Finset (Fin 13)) (hL : ∀ t, L t = lines13 t)
    (gates : List Gate) (zs : Fin gates.length) (l m p : Fin 13)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hinputs : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (hl : l ∈ ({4, 10, 12} : Finset (Fin 13))) (hm : m ∈ ({1, 5, 11} : Finset (Fin 13)))
    (hp : p = 3 ∨ p = 9)
    (hearly : ∀ i : Fin gates.length, i < zs → (gates.get i).op = GateOp.and →
      wire gates (miss L 0) (13 + i.val) = false →
      ∀ t : Fin 13, t ≠ 0 → wire gates (miss L t) (13 + i.val) = false →
      wire gates (special L 3) (13 + i.val) = false ∧ wire gates (special L 9) (13 + i.val) = false)
    (w : ℕ) (hw : w < 13 + zs.val) :
    wire gates (special L p) w = true → wire gates (miss L 0) w = false →
    wire gates (miss L l) w = true ∧ wire gates (miss L m) w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hs hzero
    by_cases hraw : w < 13
    · let a : Fin 13 := ⟨w, hraw⟩
      change wire gates (special L p) a.val = true at hs
      change wire gates (miss L 0) a.val = false at hzero
      rw [wire_input] at hs hzero
      change wire gates (miss L l) a.val = true ∧ wire gates (miss L m) a.val = true
      rw [wire_input, wire_input]
      exact raw_invariant L hL p l m a hp hl hm hs hzero
    · let i : Fin gates.length := ⟨w - 13, by have hz := zs.isLt; omega⟩
      have hiw : w = 13 + i.val := by dsimp [i]; omega
      have hil : i < zs := by change i.val < zs.val; omega
      have hmem : gates.get i ∈ gates := List.get_mem gates i
      rw [hiw] at hs hzero ⊢
      rcases hops _ hmem with hand | hor
      · have ht (t : Fin 13) (hnt : t ≠ 0) : wire gates (miss L t) (13 + i.val) = true := by
          cases he : wire gates (miss L t) (13 + i.val)
          · obtain ⟨h3, h9⟩ := hearly i hil hand hzero t hnt he
            rcases hp with rfl | rfl
            · rw [h3] at hs; contradiction
            · rw [h9] at hs; contradiction
          · rfl
        exact ⟨ht l (nonzero_first l hl), ht m (nonzero_second m hm)⟩
      · obtain ⟨a, ha, hsa⟩ := (wire_or gates _ i (hinputs i) hor).mp hs
        have ha0 : wire gates (miss L 0) a = false := by
          cases he : wire gates (miss L 0) a
          · rfl
          · have h := (wire_or gates _ i (hinputs i) hor).mpr ⟨a, ha, he⟩
            rw [hzero] at h
            contradiction
        have halt : a < w := hiw.symm ▸ (hinputs i a ha)
        obtain ⟨hal, ham⟩ := ih a halt (halt.trans hw) hsa ha0
        exact ⟨(wire_or gates _ i (hinputs i) hor).mpr ⟨a, ha, hal⟩,
          (wire_or gates _ i (hinputs i) hor).mpr ⟨a, ha, ham⟩⟩

theorem split_values : ∀ u0 ul um v0 vl vm : Bool,
    (u0 && v0) = false → (ul && vl) = false → (um && vm) = false →
    (u0 = false → ul = true ∧ um = true) → (v0 = false → vl = true ∧ vm = true) →
    (ul = false ∧ um = false ∧ u0 = true ∧ v0 = false ∧ vl = true ∧ vm = true) ∨
    (vl = false ∧ vm = false ∧ v0 = true ∧ u0 = false ∧ ul = true ∧ um = true) := by
  intro u0 ul um v0 vl vm h0 hl hm hu hv
  cases u0
  · obtain ⟨hlu, hmu⟩ := hu rfl
    have hv0 : v0 = true := by
      cases he : v0
      · have hlv := (hv he).1
        simp [hlu, hlv] at hl
      · rfl
    simp [hlu, hmu] at hl hm
    exact Or.inr ⟨hl, hm, hv0, rfl, hlu, hmu⟩
  · have hv0 : v0 = false := by simpa using h0
    obtain ⟨hlv, hmv⟩ := hv hv0
    simp [hlv, hmv] at hl hm
    exact Or.inl ⟨hl, hm, rfl, hv0, hlv, hmv⟩

end PEqualNP.Outside.L_meta_1578

open PEqualNP.Outside.L_meta_1578 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1578 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (zs : Fin gates.length) (u v : ℕ) (l m : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) →
    (gates.get zs).op = PEqualNP.CircuitLowerBounds.GateOp.and → (gates.get zs).inputs = [u, v] →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 3 ∨ ((3 = 3 ∨ 3 = 9) ∧ v ∉ L 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 9 ∨ ((9 = 3 ∨ 9 = 9) ∧ v ∉ L 0)))) = true) →
    (∀ i : Fin gates.length, i < zs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false →
      ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 3 ∨ ((3 = 3 ∨ 3 = 9) ∧ v ∉ L 0)))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 9 ∨ ((9 = 3 ∨ 9 = 9) ∧ v ∉ L 0)))) = false) →
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) ∨
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) := by
  intro L hL gates zs u v l m hops hinputs hl hm hand huv h0 hlt hmt hspecial hearly
  have hLines : ∀ t, L t = lines13 t := hL
  have hop : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => (hops g hg).1
  have hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + i.val :=
    fun i => (hinputs i).2
  have hu : u < 13 + zs.val := hin zs u (by rw [huv]; simp)
  have hv : v < 13 + zs.val := hin zs v (by rw [huv]; simp)
  have hfinal (x : Fin 13 → Bool) : wire gates x (13 + zs.val) =
      (wire gates x u && wire gates x v) := by
    rw [wire_gate gates x zs (hin zs), hand, huv]
    simp [GateOp.eval]
  have hsp : wire gates (special L 3) (13 + zs.val) = true ∨
      wire gates (special L 9) (13 + zs.val) = true := by
    simpa [wire, special] using hspecial
  have hearly' : ∀ i : Fin gates.length, i < zs → (gates.get i).op = GateOp.and →
      wire gates (miss L 0) (13 + i.val) = false →
      ∀ t : Fin 13, t ≠ 0 → wire gates (miss L t) (13 + i.val) = false →
      wire gates (special L 3) (13 + i.val) = false ∧ wire gates (special L 9) (13 + i.val) = false := by
    simpa [wire, miss, special] using hearly
  obtain ⟨p, hp, hsp⟩ : ∃ p : Fin 13, (p = 3 ∨ p = 9) ∧
      wire gates (special L p) (13 + zs.val) = true := by
    rcases hsp with h3 | h9
    · exact ⟨3, Or.inl rfl, h3⟩
    · exact ⟨9, Or.inr rfl, h9⟩
  rw [hfinal] at hsp
  obtain ⟨hsu, hsv⟩ := Bool.and_eq_true_iff.mp hsp
  have h0' : wire gates (miss L 0) (13 + zs.val) = false := h0
  have hl' : wire gates (miss L l) (13 + zs.val) = false := hlt
  have hm' : wire gates (miss L m) (13 + zs.val) = false := hmt
  rw [hfinal] at h0' hl' hm'
  exact split_values _ _ _ _ _ _ h0' hl' hm'
    (before_invariant L hLines gates zs l m p hop hin hl hm hp hearly' u hu hsu)
    (before_invariant L hLines gates zs l m p hop hin hl hm hp hearly' v hv hsv)
