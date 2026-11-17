/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module
public import FormalConjecturesUtil

/-!
# Tao's Optimization constant 4a / The cap set constant

*References:*
- [Tao's optimization constant 4a](https://teorth.github.io/optimizationproblems/constants/4a.html)
- [EG2016] Ellenberg, J. S. and Gijswijt, D., *On large subsets of F_q^n with no 
  three-term arithmetic progression* (https://doi.org/10.4007/annals.2017.185.1.8)
-/

@[expose] public section

namespace Constant4a
/-- **Tao's Optimization constant 4a / The cap set constant**:
The largest constant $C$ such that $r(n) \leq C^{(1+o(1)) n}$, where $r(n)$ is the size of the largest cap set in $\mathbb{F}_{3}^{n}$, i.e., a set that does not contain any lines (length three progressions).
-/

@[optimization_constant "4a"]
noncomputable def C4a : ℝ :=
  sSup {(sSup (card '' {A : Finset (GaloisField 3 n) | 
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 0 → x = y ∧ y = z})) ^ (1 / n) | n > 0}
  -- sSup {C : ℝ | GaloisField 3 n}
#check Asymptotics.IsLittleO
#check Asymptotics.isLittleO_iff_forall_isBigOWith


def c4a_eq.answer : ℝ := sorry

/-- What is the exact value of the constant? -/
@[category research open, question value, AMS 5]
theorem c4a_eq : C4a = c4a_eq.answer := by
  sorry

/-- Can the best known upper bound $3/8 \sqrt[3]{207+33\sqrt{33}}$ be improved? -/
@[category research open, question, AMS 5]
theorem c4a_upper_bound_improved : C4a < 3 / 8 * (207 + 33 * √ 33) ^ (1/3) := by
  sorry

end Constant4a
