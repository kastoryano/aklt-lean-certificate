import RootedKP.Honeycomb
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

namespace RootedKP.Honeycomb

theorem adj_heightQ_step {u v : Vertex} (h : Adj u v) :
    heightQ v - heightQ u = 1 ∨ heightQ v - heightQ u = -1 := by
  cases u <;> cases v <;> simp_all [Adj, heightQ] <;> omega

theorem Walk.heightQ_parity {u v : Vertex} {n : ℕ} (h : Walk u v n) :
    (heightQ v - heightQ u - (n : ℤ)) % 2 = 0 := by
  induction h with
  | nil v => simp
  | @cons u v w n huv hvw ih =>
      have hs := adj_heightQ_step huv
      omega

/-- Closed honeycomb walks have even edge length, at every size. -/
theorem Walk.closed_even {v : Vertex} {n : ℕ} (h : Walk v v n) : n % 2 = 0 := by
  have hp := h.heightQ_parity
  omega

def translate (dq dr : ℤ) : Vertex → Vertex
  | .a q r => .a (q + dq) (r + dr)
  | .b q r => .b (q + dq) (r + dr)

theorem translate_adj (dq dr : ℤ) {u v : Vertex} (h : Adj u v) :
    Adj (translate dq dr u) (translate dq dr v) := by
  cases u <;> cases v <;> simp_all [Adj, translate] <;> omega

theorem translate_injective (dq dr : ℤ) : Function.Injective (translate dq dr) := by
  intro u v h
  cases u <;> cases v <;> simp_all [translate] <;> omega

theorem translate_inverse (dq dr : ℤ) (v : Vertex) :
    translate dq dr (translate (-dq) (-dr) v) = v := by
  cases v <;> simp [translate]

/-- Rotation by120 degrees around the vertex `a(0,0)`. -/
def turnAtA : Vertex → Vertex
  | .a q r => .a (-q - r) q
  | .b q r => .b (-q - r - 1) q

theorem turnAtA_adj {u v : Vertex} (h : Adj u v) : Adj (turnAtA u) (turnAtA v) := by
  cases u <;> cases v <;> simp_all [Adj, turnAtA] <;> omega

theorem turnAtA_three (v : Vertex) : turnAtA (turnAtA (turnAtA v)) = v := by
  cases v <;> simp only [turnAtA] <;> congr 1 <;> omega

theorem turnAtA_injective : Function.Injective turnAtA := by
  intro u v h
  have hh := congrArg (fun z => turnAtA (turnAtA z)) h
  simpa only [turnAtA_three] using hh

def turnK (k : Fin 3) (v : Vertex) : Vertex :=
  match k.val with
  | 0 => v
  | 1 => turnAtA v
  | _ => turnAtA (turnAtA v)

def edgeTransport (q r : ℤ) (k : Fin 3) (v : Vertex) : Vertex :=
  translate q r (turnK k v)

theorem edgeTransport_adj (q r : ℤ) (k : Fin 3) {u v : Vertex} (h : Adj u v) :
    Adj (edgeTransport q r k u) (edgeTransport q r k v) := by
  apply translate_adj
  fin_cases k <;> simp only [turnK]
  · exact h
  · exact turnAtA_adj h
  · exact turnAtA_adj (turnAtA_adj h)

theorem edgeTransport_injective (q r : ℤ) (k : Fin 3) :
    Function.Injective (edgeTransport q r k) := by
  apply (translate_injective q r).comp
  fin_cases k <;> simp only [turnK]
  · exact Function.injective_id
  · exact turnAtA_injective
  · exact turnAtA_injective.comp turnAtA_injective

theorem edgeTransport_surjective (q r : ℤ) (k : Fin 3) :
    Function.Surjective (edgeTransport q r k) := by
  intro v
  fin_cases k
  · exact ⟨translate (-q) (-r) v, translate_inverse q r v⟩
  · refine ⟨turnAtA (turnAtA (translate (-q) (-r) v)), ?_⟩
    simp only [edgeTransport, turnK, turnAtA_three, translate_inverse]
  · refine ⟨turnAtA (translate (-q) (-r) v), ?_⟩
    simp only [edgeTransport, turnK, turnAtA_three, translate_inverse]

theorem edgeTransport_adj_iff (q r : ℤ) (k : Fin 3) (u v : Vertex) :
    Adj (edgeTransport q r k u) (edgeTransport q r k v) ↔ Adj u v := by
  fin_cases k <;> cases u <;> cases v <;>
    simp [edgeTransport, turnK, turnAtA, translate, Adj] <;> omega

/-- Every unoriented honeycomb edge is an isometric copy of the anchored
edge used by finite loop enumeration. The coordinate map is injective and
adjacency-preserving by the preceding theorems. -/
theorem edge_transitive {u v : Vertex} (h : Adj u v) :
    ∃ q r : ℤ, ∃ k : Fin 3,
      (edgeTransport q r k (.a 0 0) = u ∧ edgeTransport q r k (.b 0 0) = v) ∨
      (edgeTransport q r k (.a 0 0) = v ∧ edgeTransport q r k (.b 0 0) = u) := by
  cases u with
  | a q r =>
      cases v with
      | a q' r' => exact False.elim h
      | b q' r' =>
          rcases h with ⟨hq, hr⟩ | ⟨hq, hr⟩ | ⟨hq, hr⟩ <;> subst q' <;> subst r'
          · refine ⟨q, r, 0, Or.inl ?_⟩
            simp [edgeTransport, turnK, translate]
          · refine ⟨q, r, 1, Or.inl ?_⟩
            simp [edgeTransport, turnK, turnAtA, translate]
            omega
          · refine ⟨q, r, 2, Or.inl ?_⟩
            simp [edgeTransport, turnK, turnAtA, translate]
            omega
  | b q r =>
      cases v with
      | b q' r' => exact False.elim h
      | a q' r' =>
          rcases h with ⟨hq, hr⟩ | ⟨hq, hr⟩ | ⟨hq, hr⟩ <;> subst q <;> subst r
          · refine ⟨q', r', 0, Or.inr ?_⟩
            simp [edgeTransport, turnK, translate]
          · refine ⟨q', r', 1, Or.inr ?_⟩
            simp [edgeTransport, turnK, turnAtA, translate]
            omega
          · refine ⟨q', r', 2, Or.inr ?_⟩
            simp [edgeTransport, turnK, turnAtA, translate]
            omega

end RootedKP.Honeycomb
