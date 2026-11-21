Prompt 4:

Based on refactored.tex, create a formalization blueprint in BLUEPRINT.md, with the goal of proving the main Lean statement in Showcase.lean using Lean 4 and Mathlib.\
\
Instructions:\
\
Construct the blueprint. Translate the mathematical proof into precise, independently formalizable definitions, lemmas, and theorems. Specify their dependencies, detailed proof strategies, and relevant Mathlib declarations, verifying their actual availability.\
\
Establish the dependency graph. Provide a complete, acyclic dependency structure from Mathlib to the main theorem. Ensure every step is sufficiently fine-grained for autoformalization, without hidden arguments or substantial missing infrastructure.\
\
Design the Lean file structure. Propose a division into Lean files. Organize the formalization so that it can proceed incrementally toward the main theorem.\
\
Independent verification and iterative refinement:\
\
Once the blueprint is complete, launch an independent subagent to audit whether the dependency graph is acyclic, the path from Mathlib to the main theorem is complete, and every intermediate step is detailed enough.\
\
If issues are found, revise BLUEPRINT.md. Then launch a fresh, independent subagent to audit the updated blueprint from scratch.
