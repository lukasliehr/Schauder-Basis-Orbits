Prompt 1:

Audit the LaTeX file paper.tex, whose goal is to prove the theorem with the label thm:main. The Lean formulation of this theorem is provided in Showcase.lean, but do not write or modify any Lean code unless explicitly instructed.\
\
The objective is to make the proof of thm:main fully self-contained, without relying on external mathematical results whose proofs are not included in paper.tex.\
\
Examine the proof and identify every dependency on external mathematical inputs including results that are used implicitly without an explicit citation.\
\
For each such dependency, develop a complete, rigorous proof and incorporate it into paper.tex. Keep these additions minimal: include only the results and arguments that are genuinely necessary. Do not merely restate external results or replace citations with unproved assertions. All non-elementary mathematical results needed for thm:main must be established within the document. In particular, you can only rely on results already proven in Mathlib, and you should scan Mathlib for such results.\
\
After updating the file, perform an independent audit with a subagent to verify that all external dependencies have been resolved. If any dependency cannot be resolved, report it explicitly.
