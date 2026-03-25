# Theorm Proving with Aristotle and Lean

## aristotle references

### Source Links
https://aristotle.harmonic.fun/dashboard/docs/overview
https://aristotle.harmonic.fun/dashboard/docs/installation
https://aristotle.harmonic.fun/dashboard/docs/lean-project
https://aristotle.harmonic.fun/dashboard/docs/history
https://aristotle.harmonic.fun/dashboard/docs/api
https://aristotle.harmonic.fun/dashboard/docs/toolchain
https://aristotle.harmonic.fun/dashboard/docs/tips
https://aristotle.harmonic.fun/dashboard/docs/citation



### Helpful Aristotle Information
#### Overview
Aristotle is an automated theorem proving system by Harmonic that proves and formally verifies graduate and research-level problems in math, software, and more using Lean 4.

#### What Aristotle Can Do
Fill sorries in your Lean project — submit a file and Aristotle fills in all sorry placeholders with verified proofs.
Formalize mathematics — give Aristotle a paper, textbook, or notes in natural language and it produces formal Lean proofs.
Prove from prompts — describe a theorem in plain English and Aristotle formalizes and proves it.
Find counterexamples — when a statement is false, Aristotle can disprove it and surface a counterexample.


#### Submitting Projects
Fill Sorries in a Lean Project
Submit a Lean project to Aristotle and it will fill in all the sorry placeholders with verified proofs.

aristotle submit "Fill in the sorries" --project-dir ./my-lean-project --wait
Or via the Python API:

python
Copy
project = await Project.create_from_directory(
    prompt="Fill in the sorries",
    project_dir="./my-lean-project"
)
result = await project.wait_for_completion()
Project Requirements
Your Lean project should include:

A lakefile.toml (or lakefile.lean) configuration file
A lean-toolchain file specifying the Lean version
.lean source files with proper import structure
A typical layout:

my-lean-project/
├── lakefile.toml
├── lean-toolchain
├── lake-manifest.json
└── MyLeanProject/
    ├── Basic.lean
    └── Main.lean
The SDK automatically packages your directory for upload, skipping build artifacts (.olean, .lake/packages/).

#### Guide Aristotle with Natural Language Proof Sketches
You can provide natural language hints to guide Aristotle's proof search. Include your proof sketch in the header comment of the theorem, tagged with PROVIDED SOLUTION. Your sketch can be as general or as detailed as you like.

lean
Copy
/--
Given x, y ∈ [0, π/2], show that cos(sqrt(x ^ 2 + y ^ 2)) ≤ cos x * cos y.

PROVIDED SOLUTION
Set r := sqrt(x^2 + y^2). If r > π/2, then the inequality holds trivially.
So consider the case r ≤ π/2. Write x = r cos φ, y = r sin φ.
Consider the function F(φ) := log(cos(r cos φ)) + log(cos(r sin φ)). Then
F(0) = F(π/2) = log r, so it suffices to show that for F(φ) ≥ F(0) = F(π/2).
The derivative of F is F'(φ) = r(sin φ tan(r cos φ) - cos φ tan(r * sin φ)).
Define G(u) := tan u / u. The derivative of G on (0, π/2) is
(u - sin u cos u) / (u ^ 2 * (cos u) ^ 2), which is nonnegative on (0, π/2),
so G is increasing on (0, π/2).

For φ in [0, π/4], we have r * cos φ ≥ r * sin φ, so by monotonicity of G,
tan(r * cos φ)/(r * cos φ) ≥ tan(r * sin φ)/(r * sin φ). On [π/4, π/2],
the inequality is reversed. Multiplying this by r^2 cos φ sin φ gives that
F' is nonnegative on [0, π/4] and nonpositive on [π/4, π/2]. This means that
for φ in [0, π/4], F(φ) ≥ F(0), and for φ in [π/4, π/2], F(φ) ≥ F(π/2),
completing the proof.
-/
theorem final (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ Real.pi / 2) (hy : 0 ≤ y) (hy' : y ≤ Real.pi / 2) :
    Real.cos (Real.sqrt (x ^ 2 + y ^2)) ≤ Real.cos x * Real.cos y := by
  sorry
Aristotle does not see comments inside proof blocks.

#### Counterexamples and Negations
Aristotle can disprove false statements and find counterexamples, helping you identify logical errors, missed edge cases, or misformalizations. When a statement is false, Aristotle leaves a comment on the theorem with a proof of the negation.

lean
Copy
/-
Aristotle found this block to be false.
Here is a proof of the negation:
theorem my_favorite_theorem (k : ℕ) :
  ∑' n : ℕ, (1 : ℝ) / Nat.choose (n + k + 1) n = 1 + 1 / k := by
    -- Wait, there's a mistake. We can actually prove the opposite.
    negate_state;
    -- Proof starts here:
    use 0; norm_num;
    erw [ tsum_eq_zero_of_not_summable ] <;> norm_num;
    exact_mod_cast mt ( summable_nat_add_iff 1 |> Iff.mp ) Real.not_summable_natCast_inv
-/
theorem my_favorite_theorem (k : ℕ) :
    ∑' n : ℕ, (1 : ℝ) / Nat.choose (n + k + 1) n = 1 + 1 / k := by
  sorry
The custom negate_state tactic is automatically included in the file header. Source:

lean
Copy
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try push_neg
  )
)
Working with Data
Aristotle does not modify your definitions by default. For example, the following will not be changed:

lean
Copy
def foo : Nat := by sorry
Aristotle will create its own data where needed.

#### Submit a Prompt
You can use Aristotle in plain English — no Lean required. Ask anything, from specific math problems to general conceptual questions:

aristotle submit "Prove that the square root of 2 is irrational" --wait
aristotle submit "Implement Newton iteration and prove it correct" --wait
Or via the Python API:

python
Copy
project = await Project.create(
    prompt="Prove that the square root of 2 is irrational"
)
result = await project.wait_for_completion()
Formalize a Document
Submit a document containing mathematics in natural language — such as a .tex, .txt, or .md file — and Aristotle will produce formal Lean proofs:

aristotle formalize paper.tex --wait --destination output.tar.gz
Providing Context
When submitting with --project-dir, you can include supplementary files that help Aristotle understand your problem:

aristotle submit "Formalize the main theorems" --project-dir ./my-paper --wait
The directory can contain:

Lean files — definitions, theorems, and structures you want Aristotle to be aware of. Aristotle will automatically resolve transitive dependencies but will not modify context files.
Text files — textbook chapters, personal notes, or hints to guide Aristotle.
Context is optional — Aristotle can make progress without it.

#### Prompt Cookbook
Aristotle is smart and flexible — you can easily guide it with natural language prompts. Here are effective prompts for common use cases.

##### Sorry Filling
Fill in all the sorries in this project
##### Flexibility
Prove this using only `ring` and `omega`, avoiding heavy automation
##### Accessibility
Fill in the sorries and add detailed docstrings explaining each definition, theorem, and proof step for Lean beginners
##### Modularity
Refactor this file into a modular structure: extract helper lemmas, group related definitions, and minimize imports
##### Proof Optimization
Golf all the proofs in this project: minimize tactic count and simplify where possible
##### Proof Repair
Fix all compilation errors and linter warnings in this project
##### Auxiliary Lemmas
Build auxiliary lemmas that would help prove the main sorry'd goal in this file
##### API Development
Develop API lemmas for the main structure in this file: coercions, simp lemmas, and basic properties
##### Formal Skeleton
Build a formal sorry'd skeleton closely following my paper, with theorem statements matching each result
##### Code Quality
Formalize this paper and make sure the code quality closely follows Mathlib standards



## lean reference
https://github.com/leanprover/lean4
https://lean-lang.org/doc/reference/latest/
https://lean-lang.org/learn/
https://lean-lang.org/doc/api/
https://lean-lang.org/doc/api/foundational_types.html
https://lean-lang.org/doc/api/tactics.html


