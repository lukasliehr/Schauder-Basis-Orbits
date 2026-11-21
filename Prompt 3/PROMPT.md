Prompt 3

\
With the above information, we can refactor the tex to make it better suited for Lean formalization. Note that since the LLM has access to the folder with the original files, it will automatically deposit all of its findings there.\
\begin{prompt}\
&#x20;   Based on the findings in AUDIT.md, refactor the mathematical proof in paper.tex into a Lean-friendly document named refactored.tex.\
\
The objective is to produce a rigorous, self-contained mathematical proof that can later serve as the foundation for a Lean 4 formalization, relying as much as possible on existing Mathlib infrastructure.\
\
Instructions:\
\
Refactor the proof. Organize the argument into clearly stated definitions, lemmas, propositions, and theorems. Formulate and prove nontrivial intermediate claims separately, avoiding large proof steps, implicit arguments, and hidden assumptions.\
\
Incorporate the audit findings. Address the obstacles identified in AUDIT.md by adapting arguments, introducing suitable intermediate results, or choosing alternative proof strategies that better align with Mathlib.\
\
Preserve mathematical rigor. Provide complete proofs of all results, with explicit assumptions and logically justified steps. Preserve the statement of thm:main and avoid unnecessary changes to the mathematical content.\
\
Ensure a clear structure. Organize the document into coherent sections and subsections, with consistent notation, descriptive theorem labels, and explicit references to previously established results.
